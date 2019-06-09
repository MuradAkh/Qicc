(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Printf


let counter = ref 0
let total = ref 0
let nonlocal = ref 0 

let unoption = function
  | Some x -> x;
  | None -> -1;


class countLocalCFG max = object(self)
    val ids = Array.make (max+1) (-1)
    val lows = Array.make (max+1) (-1)
    
    method tarjan root = 
        let onstack = Array.make (max+1) false in 
        let stack = Stack.create () in
        let idx = ref 0 in 

        let rec strongconnect x = begin
            ids.(x.sid) <- !idx; 
            lows.(x.sid) <- !idx; 
            onstack.(x.sid) <- true; 
            incr idx;
            Stack.push x.sid stack;       

            let checksucc s = begin
                if(ids.(s.sid) = -1) then begin
                    strongconnect s; 
                    lows.(x.sid) <- (min lows.(x.sid) lows.(s.sid))
                    end 
                else if(onstack.(s.sid)) then lows.(x.sid) <- (min lows.(x.sid) lows.(s.sid));       
                
                end in

            List.iter checksucc x.succs;

            if(ids.(x.sid) = lows.(x.sid)) then begin
               let size = ref 0 in

               let rec clean _ =  begin 
                  incr size;
                  let w = Stack.pop stack in
                  onstack.(w) <- false;
                  if (x.sid != w) then clean ();
               end in         

               clean ();      
               if !size > 1 then print_endline (string_of_int x.sid)

            end

        end in

        strongconnect root;
        (* print_endline (string_of_int s.sid) *)

end

let cfgChecker max stmt = 
    let obj = (new countLocalCFG (unoption max)) in
    obj#tarjan stmt


class countCalls = object(self)

  inherit nopCilVisitor

  method vglob s = match s with
  | GFun (fundec, funloc) ->  ignore((cfgChecker fundec.smaxstmtid (List.hd fundec.sallstmts))); SkipChildren;
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
