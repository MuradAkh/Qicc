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

let pointer_depth = Hashtbl.create 100000

let getdepth (funname : string) (varname: string) = begin 
    Hashtbl.find pointer_depth (String.concat funname ["_____"; varname]);
end

let setdepth (funname : string) (varname: string) (depth: int) = begin 
    Hashtbl.add pointer_depth (String.concat funname ["_____"; varname]) depth;
    ()
end

let checkoffset lval = begin 

end


let incroffset lval = begin 

end

let decroffset lval = begin 

end

exception NotAFunction of string

let getfunname (g: global) = begin function
    | GFun(fd, _) -> fd.svar.vname;
    | _ -> raise ( NotAFunction "Attempted to visit a statement not within a function")

end


let unoption = function
  | Some x -> x;
  | None -> Some();


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



let rec saveexpr names exprs item : unit = begin 
        let save info found = (* Save the expression, to be added to params*)
            if(not (List.mem info.vname !names)) then begin   
                names :=  info.vname :: !names;       
                exprs :=  found :: !exprs;
            end;
        in

        let reval = saveexpr names exprs in

        match item with 
        | UnOp(unop, exp, typ) -> reval exp;
        | Question(e1, e2, e3, typ) -> reval e1; reval e2; reval e3; 
        | BinOp(binopp, e1, e2, t) ->  reval e1; reval e2;
        | CastE(t, exp) -> reval exp;
        | Lval(lh, off)  -> begin match lh with 
            | Var(info) ->             
                if(isFunctionType info.vtype) then () (*Don't care about functions (assume are global) *)
                else begin
                    let cpy = begin match info.vtype with 
                        | TPtr(_, _) -> info;
                        | _ -> let c = copyVarinfo info info.vname in c.vtype <- TPtr(info.vtype, []); c;
                    end in

                    save info (Lval(Var(cpy), off));               
                 end;

            | _ ->  (); end
        | _ -> ();
    end





let rec modexpr item = begin 
        let reval = modexpr in
        match item with 
        | UnOp(unop, exp, typ) -> UnOp(unop, reval exp, typ)
        | Question(e1, e2, e3, typ) -> Question(reval e1, reval e2, reval e3, typ)
        | BinOp(binopp, e1, e2, t) -> BinOp(binopp, reval e1, reval e2, t)
        | CastE(t, exp) -> CastE(t, reval exp)
        | Lval(lh, off)  -> begin match lh with 
            | Var(info) ->             
                if(isFunctionType info.vtype) then item (*Don't care about functions (assume are global) *)
                else begin
                    let cpy = begin match info.vtype with 
                        | TPtr(_, _) -> info;
                        | _ -> let c = copyVarinfo info info.vname in c.vtype <- TPtr(info.vtype, []); c;
                    end in

                    Lval((Mem(Lval(Var(cpy), off)), off));
                 end;
            | _ ->  item; end
        | _ -> item;
    end


class allExpr opt call set = object(self)
    inherit nopCilVisitor
    
    method vexpr = opt;

    method vinst s = begin 
    match s with 
    | Set((lh, off), r1, loc) -> begin match lh with 
        | Var(info)  -> 
            set lh off r1 loc;
        | _ ->  DoChildren; end (*TODO: Handle pointers*)
    | Call(toset, gfun, params, loc) -> begin
        match toset with 
        | Some((lh, off)) -> begin 
            call lh off gfun params loc;
         end;
        | _ -> DoChildren;

    end;
    | _ -> DoChildren;
    end;
end

let getExprs stmt = begin
    let exprs = ref [] in
    let names = ref [] in

    let set lh off r1 loc = begin 
        saveexpr names exprs (Lval((lh, off))); 
        saveexpr names exprs r1;
        DoChildren;
    end in 

    let call lh off gfun params loc =  
        saveexpr names exprs (Lval((lh, off))); DoChildren;
    in

    let opt s = begin 
        saveexpr names exprs s; DoChildren;
    end in


    let vstr = (new allExpr opt call set) in 
    ignore(visitCilStmt vstr stmt); 
    exprs; 
end;;

let modExprs stmt = begin

    let set lh off r1 loc = begin 
        let evaluated = modexpr (Lval((lh, off))) in
        begin match evaluated with 
        | Lval(lh, off) -> ChangeTo [Set((lh, off), modexpr r1, loc)];
        | _ -> DoChildren; end;
    end in 

    let call lh off gfun params loc = begin 
        let evaluated = modexpr (Lval((lh, off))) in
            match evaluated with 
            | Lval(lh, off) -> ChangeTo [Call(Some(lh, off), gfun, List.map (fun a -> modexpr a) params, loc)];
            | _ -> DoChildren;    
    end in

    let opt s = begin 
            ChangeDoChildrenPost(s, modexpr);
    end in

    let vstr = (new allExpr opt call set) in 
    ignore(visitCilGlobal vstr stmt); 
end;;


class registerVariables = object(self)
    inherit nopCilVisitor

    method vinst s  =  DoChildren;

end

class extractMLC locals = object(self)

  inherit nopCilVisitor

  method vstmt s = match s.skind with
    | Loop(blk, l1, l2, l3) -> begin 
          
            if(List.mem s.sid !locals) then begin 
                let action item = begin
                    (* List.iter (fun a -> fprint stdout 10 (printExp defaultCilPrinter () a)) !(getExprs s);
                    List.iter (fun a -> print_endline "AAAAAAA") !(getExprs s); *)
                    let replacement = (mkStmt (Block({battrs=blk.battrs; bstmts=  blk.bstmts}))) in
                    let exprs = !(getExprs replacement) in
                    let x = newfun replacement exprs in begin
                 
                    
                    let params = begin 
                        let toparam p = begin match p with 
                            | Lval (lh, off) -> begin match lh with 
                                | Var(info) -> begin 
                                    match info.vtype with 
                                    | TPtr(_, _) -> [AddrOf(lh, off)]
                                    | _ -> [Lval(lh, off)]
                                end;
                                | _ -> [];
                            end; 
                            | _  -> [];
                        end in
                        

                        let lsts = List.map toparam exprs in
                        List.fold_left (fun a b -> a @ b) [] lsts;          
                    end in

                    match x with  
                    | GFun(fdec, loc) -> begin
                        ignore(visitCilGlobal (new extractMLC locals) x);
                        modExprs x;
                        mkStmt (Loop(mkBlock ([(i2s (Call(None,v2e (fdec.svar), params, locUnknown)))]), l1, l2, l3));
                    end
                    | _ ->  print_endline "FFFFFFF"; item;
                    end
                end in
                ChangeTo(action s);
        end else DoChildren;
    end 
        | _ -> DoChildren;
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
