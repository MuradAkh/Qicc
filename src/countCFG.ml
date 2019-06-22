(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Printf


exception TarjanMe of string 


let counter = ref 0
let total = ref 0
let nonlocal = ref 0 
let locals = ref []
let nonlocals = ref []

let unoption = function
  | Some x -> x;
  | None -> -1;


class countLocalCFG max = object(self)
    val ids = Array.make (max+1) (-1)
    val loops = Array.make (max+1) (-1)
    val loop = Array.make (max+1) false
    val mutable tarjaned = false
    
    method tarjan root = 
        let onstack = Array.make (max+1) false in 
        let lows = Array.make (max+1) (-1) in
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
                else if(onstack.(s.sid)) then lows.(x.sid) <- (min lows.(x.sid) ids.(s.sid));       
                
                end in

            List.iter checksucc x.succs;

            if(ids.(x.sid) = lows.(x.sid)) then begin
               let size = ref 0 in

               let rec clean _ =  begin 
                  incr size;
                  let w = Stack.pop stack in
                  onstack.(w) <- false;
                  loops.(w) <- ids.(x.sid);
                  if (x.sid != w) then clean ();
               end in         

               clean ();      
               if !size > 1 then (loop.(x.sid) <- true; incr total)

            end

        end in

        strongconnect root;
        tarjaned <- true; 


    method countnonlocal stmt = 

      if(not tarjaned) then raise (TarjanMe "error: have to perform tarjan before counting non local");
      let visited = Array.make (max+1) false in

      let loopverify x = begin
            let loopvisited = Array.make (max+1) false in
            let exits = ref 0 in
            let loopid = ids.(x.sid) in

            let rec dfs y = begin
              loopvisited.(y.sid) <- true;  
              let checkdfs s = if (not loopvisited.(s.sid)) then begin
                 if (loops.(s.sid) = loopid) then (dfs s)
                 else if (ids.(y.sid) != loopid) then ((incr exits))  (*not root of loop*)
              
              end in

              List.iter checkdfs y.succs
            end in

            dfs x;            
            if(!exits > 1) then begin incr nonlocal;  nonlocals :=  x.sid :: !nonlocals end  
            else locals :=  x.sid :: !locals

      end in


      let rec dfs x = begin
          visited.(x.sid) <- true;  
          if (loop.(x.sid)) then loopverify x;

          let checkdfs s = if (not visited.(s.sid)) then dfs s in

          List.iter checkdfs x.succs
      end in

      dfs stmt;

      stmt.sid

end

let cfgChecker max stmt = 
    let obj = (new countLocalCFG (unoption max)) in
    obj#tarjan stmt;
    obj#countnonlocal stmt;


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
      Errormsg.log "total: %d\n" !total;
      Errormsg.log "totalnonlocal: %d\n" !nonlocal;
      Errormsg.log "wellstructured: %b\n" (!nonlocal = 0);
      Errormsg.log "nonlocals: %s\n" (String.concat " " (List.map string_of_int !nonlocals));
      Errormsg.log "locals: %s\n" (String.concat " " (List.map string_of_int !locals))
      (* Errormsg.log "%s contains %d function calls\n" f.fileName !counter; *)
    );

    fd_post_check = true;
  } 

(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature
