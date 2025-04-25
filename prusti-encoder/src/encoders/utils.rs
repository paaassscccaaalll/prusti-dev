use prusti_rustc_interface::span::def_id::DefId;
use prusti_interface::specs::typed::ProcedureSpecification;
use crate::encoders::spec::with_proc_spec;

pub(crate) fn is_def_id_trusted(def_id: DefId) -> bool {
    with_proc_spec(def_id, |def_spec: &ProcedureSpecification| {
        def_spec.trusted.extract_inherit().unwrap_or_default()
    })
    .unwrap_or_default()
}
