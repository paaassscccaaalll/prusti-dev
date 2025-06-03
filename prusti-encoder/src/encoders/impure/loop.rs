use pcg::{
    borrow_pcg::region_projection::{
        MaybeRemoteRegionProjectionBase, RegionProjection, RegionProjectionBaseLike,
    },
    free_pcs::PcgBasicBlock,
    pcg::{EvalStmtPhase, PCGNode},
    r#loop::LoopId,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, Place, SnapshotLocation},
};
use prusti_rustc_interface::middle::{
    mir,
    ty::{self, TyKind},
};
use prusti_rustc_interface::span::def_id::DefId;

use task_encoder::TaskEncoder;
use vir::Reify;

use crate::encoders::{
    indirect::{IndirectKey, IndirectPredicatesEnc},
    rust_ty_predicates::{RustTyPredicatesEnc, RustTyPredicatesEncOutputRef},
    rust_ty_snapshots::RustTySnapshotsEnc,
    lifted::{
        casters::CastTypePure,
        rust_ty_cast::RustTyCastersEnc,
    },
    spec,
    mir_pure::{MirPureEnc, MirPureEncTask, PureKind},
    ImpureEncVisitor,
};

// Import ExprRet type definition from mir_pure
type ExprInput<'vir> = (DefId, &'vir [vir::Expr<'vir>]);
type ExprRet<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

pub(super) enum WandOldOuter<'vir> {
    LetBind(Vec<(&'vir str, vir::Expr<'vir>)>),
    Label(Option<&'vir str>),
}

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    /// Calculate invariant at loop head
    pub(crate) fn get_loop_inv(
        &mut self,
        _lh: LoopId,
        cfpcs: &PcgBasicBlock<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        let mut inv = Vec::new();
        let start = &cfpcs.statements[0];
        let state = &*start.states[EvalStmtPhase::PreOperands];
        // let borrows = &*start.borrows[EvalStmtPhase::PreOperands];
        // self.stmt(self.vcx.mk_comment_stmt(
        //     vir::vir_format!(self.vcx, "_borrows: {:#?}", borrows),
        // ));
        for cap_local in state.owned_pcg().locals().iter() {
            if cap_local.is_unallocated() {
                continue;
            }
            let cap = cap_local.get_allocated();
            for place in cap.leaves(self.pcg_ctxt()).iter() {
                if !state.capabilities().is_exclusive(*place) {
                    continue;
                }
                let (place_res, snap, _, _) = self.encode_place_snap(*place);
                let ty = (*place).ty(self.pcg_ctxt());
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
                let pred = ty_out.ref_to_pred(self.vcx, place_res.expr, None);
                inv.push(pred);

                let regions = ty.ty.walk().flat_map(IndirectKey::from_generic_arg);
                for region in regions {
                    let indirect = self
                        .deps
                        .require_ref::<IndirectPredicatesEnc>((ty.ty, region))
                        .unwrap();
                    inv.extend(
                        indirect
                            .covariant
                            .into_iter()
                            .map(|expr| expr.reify(self.vcx, snap)),
                    );
                }
            }
        }
        for (_edge, inputs, outputs) in Self::get_abstraction_edges(state.borrow_pcg().graph()) {
            let mut let_bind = WandOldOuter::LetBind(Vec::new());
            let mut wand_rhs = Vec::new();
            for i in inputs {
                self.encode_pcg_node(&i, &mut wand_rhs, &mut let_bind);
            }
            let mut wand_lhs = Vec::new();
            for i in outputs {
                let exprs = self.encode_region_projection(i, &mut let_bind);
                wand_lhs.extend(exprs);
            }
            let wand = self.vcx.mk_wand(
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
                self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
            );
            let mut wand = self.vcx.mk_wand_expr(wand);
            let WandOldOuter::LetBind(let_bind) = let_bind else {
                unreachable!()
            };
            for (ident, expr) in let_bind {
                wand = self.vcx.mk_let_expr(ident, expr, wand);
            }
            inv.push(wand);
        }

        self.collect_loop_invariants(&mut inv);
        self.vcx.alloc_slice(&inv)
    }

    pub(super) fn encode_pcg_node(
        &mut self,
        node: &PCGNode<'vir, MaybeRemotePlace<'vir>, MaybeRemotePlace<'vir>>,
        wand_rhs: &mut Vec<vir::Expr<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) {
        match node {
            PCGNode::Place(MaybeRemotePlace::Remote(_)) => unreachable!(),
            PCGNode::Place(place @ MaybeRemotePlace::Local(_)) => {
                let p = Self::get_place(*place);
                let ty = (*p).ty(self.local_decls, self.vcx.tcx());
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty.ty).unwrap();
                let p = self.encode_place(p);
                let p = self.configure_old(*place, p.expr, old_outer);

                let pred = ty_out.ref_to_pred(self.vcx, p, None);
                wand_rhs.push(pred);
            }
            PCGNode::RegionProjection(r) => {
                let exprs = self.encode_region_projection(*r, old_outer);
                wand_rhs.extend(exprs);
            }
        }
    }

    pub(super) fn encode_region_projection<T: RegionProjectionBaseLike<'vir>>(
        &mut self,
        r: RegionProjection<'vir, T>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::Expr<'vir>> {
        let place = r.place().to_maybe_remote_region_projection_base();
        let (place_snap, ty, _) = match place {
            MaybeRemoteRegionProjectionBase::Place(p) => {
                self.encode_maybe_remote_place_snap(p, old_outer)
            }
            MaybeRemoteRegionProjectionBase::Const(c) => todo!("{c:?}"),
        };
        let mut regions = ty.ty.walk().flat_map(IndirectKey::from_generic_arg);
        let region = regions.next().unwrap();
        // TODO:
        assert!(
            regions.next().is_none(),
            "multiple regions in a type not supported ({:?})",
            ty.ty
        );
        let indirect = self
            .deps
            .require_ref::<IndirectPredicatesEnc>((ty.ty, region))
            .unwrap();
        indirect
            .covariant
            .into_iter()
            .map(|expr| expr.reify(self.vcx, place_snap))
            .collect::<Vec<_>>()
    }

    fn get_place(place: MaybeRemotePlace<'vir>) -> Place<'vir> {
        match place {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) => place,
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(place)) => place.place,
            MaybeRemotePlace::Remote(r) => r.assigned_local().into(),
        }
    }

    fn encode_maybe_remote_place_snap(
        &mut self,
        place: MaybeRemotePlace<'vir>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> (
        vir::Expr<'vir>,
        mir::tcx::PlaceTy<'vir>,
        RustTyPredicatesEncOutputRef<'vir>,
    ) {
        let p = Self::get_place(place);
        let (_, place_snap, ty, ty_out) = self.encode_place_snap(p);
        let place_snap = self.configure_old(place, place_snap, old_outer);
        (place_snap, ty, ty_out)
    }

    fn configure_old(
        &mut self,
        place: MaybeRemotePlace,
        expr: vir::Expr<'vir>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir> {
        match place {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { .. }) => {
                self.mk_wand_outer(expr, old_outer)
            }
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(place)) => {
                let label = Self::get_location_label(self.vcx, place.at);
                self.vcx.mk_old(expr, label)
            }
            MaybeRemotePlace::Remote(_) => self.vcx.mk_old_expr(expr),
        }
    }

    pub(crate) fn get_location_label(
        vcx: &'vir vir::VirCtxt<'vir>,
        at: SnapshotLocation,
    ) -> vir::OldLabel<'vir> {
        match at {
            // TODO: handle this properly!!
            SnapshotLocation::After(loc) => {
                let name =
                    vir::vir_format!(vcx, "_after_{}_{}", loc.block.index(), loc.statement_index);
                vir::OldLabel::Label(name)
            }
            SnapshotLocation::Start(bb) => {
                vir::OldLabel::Block(vir::CfgBlockLabelData::BasicBlock(bb.as_usize()))
            }
        }
    }

    fn mk_wand_outer(
        &mut self,
        expr: vir::Expr<'vir>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> vir::Expr<'vir> {
        match old_outer {
            WandOldOuter::LetBind(let_bind) => {
                let ident = vir::vir_format!(self.vcx, "_snap{}", let_bind.len());
                let_bind.push((ident, expr));
                self.vcx.mk_local_ex(ident, expr.ty())
            }
            WandOldOuter::Label(label) => {
                let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
                self.vcx.mk_local_labelled_old_expr(expr, label)
            }
        }
    }

    fn collect_loop_invariants(&mut self, inv: &mut Vec<vir::Expr<'vir>>) {
        let mut closure_assignments = Vec::new();
        
        for (_block_idx, block_data) in self.body.basic_blocks.iter_enumerated() {
            for stmt in &block_data.statements {
                if let mir::StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                    if let mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(cl_def_id, _), _) = rvalue {
                        let is_loop_invariant = spec::with_def_spec(|def_spec| {
                            if let Some(loop_spec) = def_spec.get_loop_spec(cl_def_id) {
                                matches!(loop_spec, prusti_interface::specs::typed::LoopSpecification::Invariant(_))
                            } else {
                                false
                            }
                        });

                        if is_loop_invariant {
                            closure_assignments.push((*place, *cl_def_id));
                        }
                    }
                }
            }
        }
        
        for (place, cl_def_id) in closure_assignments {
            // Add access (Now there is this there might be insufficient permission to access p_test_Closure_0(_9p))
            let (place_res, _snap, _, _) = self.encode_place_snap(place.into());
            let closure_ty = place.ty(self.body, self.vcx.tcx()).ty;
            let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(closure_ty).unwrap();
            let pred = ty_out.ref_to_pred(self.vcx, place_res.expr, Some(self.vcx.mk_wildcard()));
            inv.push(pred);

            let invariant_expr = self.encode_loop_invariant_closure(cl_def_id, place);
            
            // Same unsafe transmute as in forall to convert ExprRet to ExprGen. Is there another way?
            let concrete_expr = unsafe {
                std::mem::transmute::<ExprRet<'_>, vir::ExprGen<'_, !, !>>(invariant_expr)
            };
            inv.push(concrete_expr);
        }
    }

    fn encode_loop_invariant_closure(&mut self, cl_def_id: DefId, closure_place: mir::Place<'vir>) -> ExprRet<'vir> {
        let tcx = self.vcx.tcx();
        
        let closure_ty = tcx.type_of(cl_def_id).instantiate_identity();
        
        let (qvar_tys, _upvar_tys) = match closure_ty.kind() {
            TyKind::Closure(_, cl_args) => (
                match cl_args.as_closure().sig().skip_binder().inputs()[0].kind() {
                    TyKind::Tuple(list) => list,
                    _ => unreachable!(),
                },
                cl_args.as_closure().upvar_tys().iter().collect::<Vec<_>>(),
            ),
            _ => panic!("illegal loop invariant closure"),
        };

        let qvars = self.vcx.alloc_slice(
            &qvar_tys
                .iter()
                .enumerate()
                .map(|(idx, qvar_ty)| {
                    let ty_out = self
                        .deps
                        .require_ref::<RustTySnapshotsEnc>(qvar_ty)
                        .unwrap();
                    self.vcx.mk_local_decl(
                        vir::vir_format!(self.vcx, "qvar_{idx}"),
                        ty_out.generic_snapshot.snapshot,
                    )
                })
                .collect::<Vec<_>>(),
        );


        let closure_place_result = self.encode_place(closure_place.into());
        
        let ref_to_closure_ty = tcx.mk_ty_from_kind(TyKind::Ref(
            tcx.lifetimes.re_erased,
            closure_ty,
            ty::Mutability::Not,
        ));
        let ref_to_closure_ty_out = self
            .deps
            .require_local::<RustTySnapshotsEnc>(ref_to_closure_ty)
            .unwrap()
            .generic_snapshot
            .specifics
            .expect_immref();
            
        let mut reify_args = vec![];
        
        let closure_ty_out = self
            .deps
            .require_ref::<RustTyPredicatesEnc>(closure_ty)
            .unwrap();
            
        let cast = self
            .deps
            .require_local::<RustTyCastersEnc<CastTypePure>>(closure_ty)
            .unwrap();
        
        let closure_snapshot = closure_ty_out.ref_to_snap(self.vcx, closure_place_result.expr);
        
        let closure_generic_snapshot = cast.cast_to_generic_if_necessary(
            self.vcx,
            closure_snapshot
        );
        
        // Wrap it in s_Ref_immutable_cons
        let closure_arg = ref_to_closure_ty_out.prim_to_snap.apply(
            self.vcx,
            [self.vcx.mk_null(), closure_generic_snapshot]
        );
        
        reify_args.push(closure_arg);
         reify_args.extend(
             qvars
                 .iter()
                 .map(|qvar| self.vcx.mk_local_ex(qvar.name, qvar.ty)),
         );

        // TODO: recursively invoke MirPure encoder to encode
        // the body of the closure; pass the closure as the
        // variable to use, then closure access = tuple access
        // (then hope to optimise this away later ...?)
        use vir::Reify;
        let body = self
            .deps
            .require_local::<MirPureEnc>(MirPureEncTask {
                encoding_depth: 1, // Which depth should I use here?
                kind: PureKind::Closure,
                parent_def_id: cl_def_id,
                param_env: tcx.param_env(cl_def_id),
                substs: ty::List::identity_for_item(self.vcx.tcx(), cl_def_id),
                caller_def_id: Some(self.def_id),
            })
            .unwrap()
            .expr
            // arguments to the closure are:
            // - the closure itself  
            // - the qvars
            .reify(self.vcx, (cl_def_id, self.vcx.alloc_slice(&reify_args)))
            .lift();

        let bool = self
            .deps
            .require_local::<RustTySnapshotsEnc>(tcx.types.bool)
            .unwrap()
            .generic_snapshot
            .specifics;
        let bool = bool.expect_primitive();

        self.vcx.mk_forall_expr(
            qvars,
            &[], // TODO
            bool.snap_to_prim.apply(self.vcx, [body]),
        )

    }
}
