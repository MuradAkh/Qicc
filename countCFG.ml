(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Printf


let counter = ref 0
let total = ref 0
let nonlocal = ref 0 

let toint a = a.sid

let printlist a = 
  if((List.length a) > 0) then
  List.iter (printf "%d ") (List.map toint a) 



let ifincr a = 
  if (a) then incr nonlocal

class countCalls = object(self)

  inherit nopCilVisitor

  method vglob s = match s with
  | GFun (fundec, funloc) -> Cfg.printCfgChannel stdout fundec; DoChildren;
  | _ -> DoChildren;
end


(* XXX Cil.featureDescr is now Feature.t *)
let feature : Feature.t = {
    fd_name = "countCalls";
    fd_enabled = true; (* XXX fd_enabled is now a bool, not a bool ref anymore. *)
    fd_description = "count and display the number of function calls";
    fd_extraopt = [];
    fd_doit = (function f ->
      Cfg.computeFileCFG f;
      visitCilFileSameGlobals (new countCalls) f;
      Errormsg.log "found %d nonlocal out of %d loops\n" !nonlocal !total
      (* Errormsg.log "%s contains %d function calls\n" f.fileName !counter; *)
    );

    fd_post_check = true;
  } 

(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature
