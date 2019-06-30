(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Printf



let counter = ref 0
let total = ref 0
let nonlocal = ref 0 
let newfuns = ref []

let toint a = a.sid

let propred a = 
  if((List.length a) > 0) then
  List.iter (printf "%d ") (List.map toint a) 



class prepFun a = object(self)
  inherit nopCilVisitor

  method vblock s = match s with
  | _ -> dumpStmt defaultCilPrinter stdout 1 a; s.bstmts <- [a]; SkipChildren;
end


let newfun a = 
  let func = GFun(emptyFunction "newfun", ({line= -1; file= "file.c"; byte= -1})) in   
  ignore(visitCilGlobal (new prepFun a) func);
  dumpGlobal defaultCilPrinter stdout func;
  
  newfuns := func :: !newfuns;
  func


let ifincr a = 
  if (a) then incr nonlocal

class checkLocalAST = object(self)
  inherit nopCilVisitor

  val local = true;
  val break = ref 0;

  method vstmt s = match s.skind with
  | Break _ -> incr break; ignore(
      if(!break > 1) then 
      begin ifincr local; ignore(local = false) 
      end); 
      SkipChildren;
  | Continue _ -> ifincr local; ignore(local = false); SkipChildren;
  | Goto _ -> ifincr local; ignore(local = false); SkipChildren;
  | _ -> DoChildren;
end

let i2s (i : instr) : stmt = mkStmt(Instr [i])
let v2e (v : varinfo) : exp = Lval(var v)



class countCalls = object(self)

  inherit nopCilVisitor

  method vglob s = match s with
  (* | GFun (fundec, funloc) -> Cfg.printCfgChannel stdout fundec; DoChildren; *)
  (* | GFun (fundec, funloc) -> ignore(emptyFunction "Hello"); DoChildren; *)
  | GFun (fundec, funloc) -> ignore(emptyFunction "Hello"); DoChildren;
  (* | GFun (fundec, funloc) -> print_endline "Hello"; DoChildren; *)
  | _ -> DoChildren;

  method vstmt s = match s.skind with
  (* | Loop _ -> incr total; ignore(visitCilStmt (new checkLocalAST) s); DoChildren; *)
  | Loop _ -> let x = newfun s in begin
      match x with  
      | GFun(fdec, loc) -> ChangeTo (i2s (Call(None, v2e (fdec.svar), [], locUnknown)));
      | _ -> DoChildren;
      end      
  | _ -> DoChildren;

  method vinst s = match s with 
  (* | Set(_, _, _) -> newfun s; DoChildren; *)
  (* | Set(_, _, _) -> pushGlobal (GText("haha")) (ref []) (ref []); DoChildren; *)
  (* | Set(_, _, _) -> ignore(makeGlobalVar "aaa" intType); DoChildren; *)
  | _ -> DoChildren;

end


(* XXX Cil.featureDescr is now Feature.t *)
let feature : Feature.t = {
    fd_name = "countCalls";
    fd_enabled = true; (* XXX fd_enabled is now a bool, not a bool ref anymore. *)
    fd_description = "count and display the number of function calls";
    fd_extraopt = [];
    fd_doit = (function f ->
      (* findOrCreateFunc f "test" intType; *)
      Cfg.computeFileCFG f;
      visitCilFileSameGlobals (new countCalls) f;

      let declarefuns func = begin match func with
        | GFun(fdec, loc) -> ignore(findOrCreateFunc f fdec.svar.vname fdec.svar.vtype);
        | _ -> ()
      end in 

      List.iter declarefuns !newfuns;
      f.globals <-  f.globals @ !newfuns;
      Errormsg.log "found %d nonlocal out of %d loops\n" !nonlocal !total
      (* Errormsg.log "%s contains %d function calls\n" f.fileName !counter; *)
    );

    fd_post_check = true;
  } 

(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature
