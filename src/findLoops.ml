(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Printf

exception TarjanMe of string 

type loopdata = {
   counter: int ref;
   total: int ref;
   nonlocal: int ref ;
   locals: int list ref;
   nonlocals: int list ref;
}

let loop_data = {
      counter = ref 0;
      total = ref 0;
      nonlocal = ref 0;
      locals = ref [];
      nonlocals = ref [];
}


let printint i = (print_endline (string_of_int i));;


let unoption = function
  | Some x -> x;
  | None -> -1;



class countLocalCFG  max = object(self)
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
                            incr loop_data.total;
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
            let midexit = ref false in

            let checkmidexit passed = begin
                if(List.length passed > 1) then midexit := true;
                print_endline (string_of_int (List.length passed))


            end in


            let rec dfs y passed = begin
              loopvisited.(y.sid) <- true;  
              let checkdfs s = if (not loopvisited.(s.sid)) then begin
                 if (self#part_of_loop loopid s.sid) then dfs s (s :: passed)
                 else if (ids.(y.sid) != loopid) then (incr exits; checkmidexit passed)(*not root of loop*)
                 (* y has an exit out of the loop, the exit being S. *)
              
              end in

              List.iter checkdfs y.succs
            end in

            dfs x [];            
            if(!exits > 1 || !midexit) then begin incr loop_data.nonlocal;  loop_data.nonlocals :=  x.sid :: !(loop_data.nonlocals) end  
            else loop_data.locals :=  x.sid :: !(loop_data.locals)

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




type respones = {locals: int list ref; nonlocals: int list ref}

let getLoops f = begin
    visitCilFileSameGlobals (new countCalls) f;
    {locals = loop_data.locals; nonlocals = loop_data.nonlocals}
end
