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

let printint i = (print_endline (string_of_int i));;


let unoption = function
  | Some x -> x;
  | None -> -1;



class countLocalCFG max = object(self)
    val ids = Array.make (max+1) (-1)
    val loops = Array.init (max+1) (fun i -> ref [])
    val loop = Array.make (max+1) false
    val mutable tarjaned = false


    method tarjan root = 
        let idx = ref 0 in 
      
       
        let rec tarjanx looproot first = begin
            let llows = Array.make (max+1) (-1) in
            let onstack = Array.make (max+1) false in 
            let visited = Array.make (max+1) false in 
            let stack = Stack.create () in

            let rec strongconnect x = begin
                if(first) then (ids.(x.sid) <- !idx; incr idx);
                llows.(x.sid) <- ids.(x.sid); 
                onstack.(x.sid) <- true; 
                visited.(x.sid) <- true; 
                Stack.push x.sid stack;       

                let checksucc s = begin if(first || (self#part_of_loop ids.(looproot.sid) s.sid && (s.sid != looproot.sid))) then begin
                    if((not visited.(s.sid))) then begin
                        strongconnect s; 
                        llows.(x.sid) <- (min llows.(x.sid) llows.(s.sid));
                        end 
                    else if(onstack.(s.sid))  then llows.(x.sid) <- (min llows.(x.sid) llows.(s.sid));       
                    end 
                end in

                List.iter checksucc x.succs;

                if(ids.(x.sid) = llows.(x.sid)) then begin
                    let size = ref 0 in

                    let rec clean _ =  begin 
                        incr size;
                        let w = Stack.pop stack in
                        onstack.(w) <- false;
                        loops.(w) := ids.(x.sid) :: !(loops.(w));
                        if (x.sid != w) then clean ();
                    end in         

                    clean ();      

                    if !size > 1 then  begin
                            loop.(x.sid) <- true; 
                            incr total;
                            ignore(tarjanx x false);
                    end

                end
            end in

            strongconnect looproot
        
        end; in
        tarjanx root true;
        tarjaned <- true; 

    method part_of_loop loopid vertex = 
        let bools = List.map (fun it -> it = loopid) !(loops.(vertex)) in    
        List.fold_left (fun a b -> a || b) false bools;

    method countnonlocal stmt = 
    (* Array.iter (fun lst -> List.iter (fun it -> (print_endline (string_of_int it))) !lst) loops; *)


      if(not tarjaned) then raise (TarjanMe "error: have to perform tarjan before counting non local");
      let visited = Array.make (max+1) false in

      let loopverify x = begin
            let loopvisited = Array.make (max+1) false in
            let exits = ref 0 in
            let loopid = ids.(x.sid) in

            let rec dfs y = begin
              loopvisited.(y.sid) <- true;  
              let checkdfs s = if (not loopvisited.(s.sid)) then begin
                 if (self#part_of_loop loopid s.sid) then dfs s 
                 else if (ids.(y.sid) != loopid) then incr exits; (*not root of loop*)
              
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
