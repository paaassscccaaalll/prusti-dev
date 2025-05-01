use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::{domain::{DomainBuilder, DomainEnc, DomainEncSpecifics}, predicate::{PredicateBuilder, PredicateEncData}, snapshot::SnapshotEncOutput, PredicateEnc};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    _builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    Ok(DomainEncSpecifics::Trusted)
}

pub(crate) fn predicate<'vir>(
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<PredicateEncData<'vir>, EncodeFullError<'vir, PredicateEnc>> {
    let snap_type = snap.snapshot;

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);

    builder.predicate(
        "",
        &[ref_self_decl],
        None,
    );

    // Ref-to-snap
    builder.function_snap = Some(builder.mk_function(
        "snap",
        &[ref_self_decl],
        snap_type,
        &[], 
        &[],
        None, // No body provided
    ).1);

    Ok(PredicateEncData::Trusted)
}