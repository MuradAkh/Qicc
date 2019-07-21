(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Printf
open Tututil
open Pretty
open FindLoops


let newfuncount = ref 0

let newfuns = ref []

let printint i = (print_endline (string_of_int i));;


let unoption = function
  | Some x -> x;
  | None -> -1;


class prepFun a = object(self)
  inherit nopCilVisitor

  method vblock s =  s.bstmts <- [a]; SkipChildren;
end

let newfunname _ = 
    incr newfuncount;
    "newfun" ^ string_of_int !newfuncount


let newfun fsmt exprs = 

 
  let genTypes expr = begin match expr with 
    | Lval(lh, off) -> begin 
        match lh with 
        | Var(info) -> [info.vname, info.vtype];
        | Mem(exp) -> print_endline "BAD GENTYPE"; [];
    end;
    | _ -> [];
  end in  

  let typelists = (List.fold_left (fun a b -> a @ b) [] (List.map genTypes exprs)) in

  let fdec = emptyFunction (newfunname ()) in
  setFunctionTypeMakeFormals fdec (mkFunTyp voidType typelists);
  let func = GFun(fdec, ({line= -1; file= "file.c"; byte= -1})) in   
  ignore(visitCilGlobal (new prepFun fsmt) func);
  
  newfuns := func :: !newfuns;
  func



let rec evalexpr names exprs item = begin 
        let save info found = (* Save the expression, to be added to params*)
            if(not (List.mem info.vname !names)) then begin   
                names :=  info.vname :: !names;       
                exprs :=  found :: !exprs;
            end;
        in

        match item with 
        | BinOp(binopp, e1, e2, t) -> BinOp(binopp, evalexpr names exprs e1, evalexpr names exprs e2, t) 
        | Lval(lh, off)  -> begin match lh with 
            | Var(info) ->             
                if(isFunctionType info.vtype) then item (*Don't care about functions (assume are global) *)
                else begin
                    let cpy = begin match info.vtype with 
                        | TPtr(_, _) -> info;
                        | _ -> let c = copyVarinfo info info.vname in c.vtype <- TPtr(info.vtype, []); c;
                    end in

                    save info (Lval(Var(cpy), off));               
                    Lval((Mem(Lval(Var(cpy), off)), off));
                 end;

            | _ ->  item; end

        | AddrOf(lh, off) ->  (* Nasty Hack *)
            begin match lh with         
            | Var(info) ->          

                let cpy = begin match info.vtype with 
                    | TPtr(t, _) -> let c = copyVarinfo info info.vname in c.vtype <- t; c;
                    | _ -> info;
                end in
            
                save info (Lval(Var(info), off));               
                Lval(Var(cpy), off);

            | _ ->  item; end
        | _ -> item;
    end


class allExpr exprs = object(self)
    inherit nopCilVisitor
    val names = ref []


    method vexpr s = begin 
        ChangeDoChildrenPost(s, (evalexpr names exprs));
    end;

    method vinst s = begin 
    match s with 
    | Set((lh, off), r1, loc) -> begin match lh with 
        | Var(info)  -> 

            let evaluated = evalexpr names exprs (Lval((lh, off))) in
            begin match evaluated with 
            | Lval(lh, off) -> ChangeTo [Set((lh, off), evalexpr names exprs r1, loc)];
            | _ -> DoChildren; end;


        | _ ->  DoChildren; end (*TODO: Handle pointers*)
    | Call(toset, gfun, params, loc) -> begin
        match toset with 
        | Some((lh, off)) -> begin 
            let evaluated = evalexpr names exprs (Lval((lh, off))) in
            match evaluated with 
            | Lval(lh, off) -> ChangeTo [Call(Some(lh, off), gfun, List.map (fun a -> evalexpr names exprs a) params, loc)];
            | _ -> DoChildren;
         end;
        | _ -> DoChildren;

    end;
    | _ -> DoChildren;
    end;


end

let getExprs stmt = 
    let exprs = ref [] in
    let vstr = (new allExpr exprs) in 
    ignore(visitCilStmt vstr stmt); 
    exprs;


class extractMLC locals = object(self)

  inherit nopCilVisitor

  method vstmt s = match s with
    | stmt -> begin 
            if(List.mem s.sid !locals) then begin 
                let action item = begin
                    (* List.iter (fun a -> fprint stdout 10 (printExp defaultCilPrinter () a)) !(getExprs s);
                    List.iter (fun a -> print_endline "AAAAAAA") !(getExprs s); *)
                    let exprs = !(getExprs s) in
                    let x = newfun item exprs in begin
                 

                    let params = begin 
                        let toparam p = begin match p with 
                            | Lval (lh, off) -> begin match lh with 
                                | Var(info) -> begin 
                                    match info.vtype with 
                                    | TPtr(_, _) -> [AddrOf(lh, off)]
                                    | _ -> []
                                end;
                                | _ -> [];
                            end; 
                            | _  -> [];
                        end in
                        

                        let lsts = List.map toparam exprs in
                        List.fold_left (fun a b -> a @ b) [] lsts;          
                    end in

                    match x with  
                    | GFun(fdec, loc) -> (i2s (Call(None,v2e (fdec.svar), params, locUnknown)));
                    | _ -> item;
                    end
                end in
                ChangeDoChildrenPost(s, action);
        end else DoChildren;
    end 
end



(* XXX Cil.featureDescr is now Feature.t *)
let feature : Feature.t = {
    fd_name = "findLoops";
    fd_enabled = true; (* XXX fd_enabled is now a bool, not a bool ref anymore. *)
    fd_description = "count and display the number of function calls";
    fd_extraopt = [];
    fd_doit = (function f ->
      Cfg.computeFileCFG f;
    

      let res = getLoops f in
      visitCilFileSameGlobals (new extractMLC res.locals) f;

      let declarefuns func = begin match func with
        | GFun(fdec, loc) -> ignore(findOrCreateFunc f fdec.svar.vname fdec.svar.vtype);
        | _ -> ()
      end in 

      List.iter declarefuns !newfuns;
      f.globals <-  f.globals @ !newfuns;

      Errormsg.log "total: %d\n" !newfuncount;

      (* Errormsg.log "%s contains %d function calls\n" f.fileName !counter; *)
    );

    fd_post_check = true;
  } 

(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature