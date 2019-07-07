open FindLoops
open Cil
open Feature



(* XXX Cil.featureDescr is now Feature.t *)
let feature : Feature.t = {
    fd_name = "countCalls";
    fd_enabled = true; (* XXX fd_enabled is now a bool, not a bool ref anymore. *)
    fd_description = "count and display the number of function calls";
    fd_extraopt = [];
    fd_doit = (function f ->
      Cfg.computeFileCFG f;
      visitCilFileSameGlobals (new countCalls) f;
      Errormsg.log "total: %d\n" !(loop_data.total);
      Errormsg.log "totalnonlocal: %d\n" !(loop_data.nonlocal);
      Errormsg.log "wellstructured: %b\n" (!(loop_data.nonlocal) = 0);
      Errormsg.log "nonlocals: %s\n" (String.concat " " (List.map string_of_int !(loop_data.nonlocals)));
      Errormsg.log "locals: %s\n" (String.concat " " (List.map string_of_int !(loop_data.locals)))
      (* Errormsg.log "%s contains %d function calls\n" f.fileName !counter; *)
    );

    fd_post_check = true;
  }


(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature
