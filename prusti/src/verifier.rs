//! A module that invokes the verifier `prusti-viper`

use log::{debug, warn};
use prusti_interface::{data::VerificationTask, environment::Environment, specs::typed};
use prusti_utils::{config, report::user};

#[tracing::instrument(name = "prusti::verify", level = "debug", skip(env))]
pub fn verify(env: Environment<'_>, def_spec: typed::DefSpecificationMap) {
    if env.diagnostic.has_errors() {
        warn!("The compiler reported an error, so the program will not be verified.");
    } else {
        debug!("Prepare verification task...");
        // TODO: can we replace `get_annotated_procedures` with information
        // that is already in `def_spec`?
        let (annotated_procedures, types) = env.get_annotated_procedures_and_types();
        let verification_task = VerificationTask {
            procedures: annotated_procedures,
            types,
        };
        debug!("Verification task: {:?}", &verification_task);

        user::message(format!(
            "Verification of {} items...",
            verification_task.procedures.len()
        ));

        if config::print_collected_verification_items() {
            println!(
                "Collected verification items {}:",
                verification_task.procedures.len()
            );
            for procedure in &verification_task.procedures {
                println!(
                    "procedure: {} at {:?}",
                    env.name.get_item_def_path(*procedure),
                    env.query.get_def_span(procedure)
                );
            }
        }

        let tcx = env.tcx();
        
        let request = prusti_encoder::test_entrypoint(tcx, env.body, def_spec);
        let program = request.program;

        let mut results = prusti_server::verify_programs(vec![program]);
        assert_eq!(results.len(), 1); // TODO: eventually verify separate methods as separate programs again?

        let result = results.pop().unwrap().1;
        if std::env::var("LOCAL_TESTING").is_ok() {
            println!("raw result: {result:?}");
        }
        let success = match result {
            viper::VerificationResult::Success => true,
            viper::VerificationResult::JavaException(_e) => false,
            viper::VerificationResult::ConsistencyErrors(_e) => false,
            viper::VerificationResult::Failure(errors) => {
                let mut has_non_trusted_errors = false;
                
                for error in errors {
                    // TODO: offending_pos_id should always be set!
                    if let Some(offending_pos_id) = &error.offending_pos_id {
                        let error_from_trusted_fn = is_error_from_trusted_function(&error, tcx, &|def_id| env.name.get_item_name(def_id).to_string());
                        
                        if error_from_trusted_fn {
                            debug!("Ignoring error in trusted function: {:?}", error.full_id);
                            continue; 
                        }
                        
                        has_non_trusted_errors = true;
                        
                        if let Some(translated_errors) = prusti_encoder::backtranslate_error(
                            &error.full_id,
                            offending_pos_id.parse::<usize>().unwrap(),
                            error.reason_pos_id.as_ref().and_then(|id| id.parse::<usize>().ok()),
                        ) {
                            for prusti_error in translated_errors {
                                prusti_error.emit(&env.diagnostic);
                            }
                        }
                    } else {
                        has_non_trusted_errors = true;
                        eprintln!("verifier error without offending_pos_id: {error:?}");
                    }
                }
                
                !has_non_trusted_errors
            }
        };
        if !success {
            user::message("Verification failed");
            // assert!(
            //     env.diagnostic.has_errors()
            //         || config::internal_errors_as_warnings()
            //         || (config::skip_unsupported_features()
            //             && config::allow_unreachable_unsupported_code())
            // );
        }
    }
}

fn is_error_from_trusted_function<'a>(
    error: &viper::VerificationError, 
    tcx: prusti_rustc_interface::middle::ty::TyCtxt,
    name_resolver: &'a dyn Fn(prusti_rustc_interface::hir::def_id::DefId) -> String,
) -> bool {
    let function_name = extract_function_name_from_error(error);
    
    if let Some(name) = function_name {
        tcx.hir().items().filter_map(|item_id| {
            let def_id = item_id.owner_id.to_def_id();
            if !matches!(tcx.def_kind(def_id), 
                prusti_rustc_interface::hir::def::DefKind::Fn | 
                prusti_rustc_interface::hir::def::DefKind::AssocFn) {
                return None;
            }
            
            let item_name = name_resolver(def_id);
            
            if item_name.contains(&name) {

                for attr in tcx.get_attrs_unchecked(def_id) {

                    let path_str = format!("{:?}", attr.path());
                    if path_str.contains("trusted") {
                        return Some(true);
                    }
                }
            }
            
            None
        }).next().is_some()
    } else {
        false
    }
}

fn extract_function_name_from_error(error: &viper::VerificationError) -> Option<String> {
    if let Some(last_dot_idx) = error.full_id.rfind('.') {
        let name = &error.full_id[last_dot_idx + 1..];
        if !name.is_empty() {
            return Some(name.to_string());
        }
    }
    
    let message = &error.message;
    if let Some(idx) = message.find("function ") {
        let start = idx + "function ".len();
        if let Some(end) = message[start..].find('(') {
            return Some(message[start..start + end].trim().to_string());
        }
    }
    
    if let Some(idx) = message.find("method ") {
        let start = idx + "method ".len();
        if let Some(end) = message[start..].find('(') {
            return Some(message[start..start + end].trim().to_string());
        }
    }
    
    None
}
