(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature 
open Printf
open Tututil
open Pretty
open FindLoops

type funcvar = {
    info: varinfo;
    depth: int
}
module FuncVars = Map.Make(String)
module VarTypes = Map.Make(String)
module NewCalls = Set.Make(struct type t = exp let compare = compare end)

let newfuncount = ref 0
let newfuns = ref []
let funcparents = ref []
let funclocs = ref []


let printint i = (print_endline (string_of_int i));;

let pointer_depth = ref FuncVars.empty
let new_calls = ref NewCalls.empty

let getdepth (funname : string) (varname: string) : int = ( 
    FuncVars.find (String.concat funname ["_____"; varname]) !pointer_depth;
)

let setdepth (funname : string) (varname: string) (depth: int) : unit = ( 
    pointer_depth := FuncVars.add (String.concat funname ["_____"; varname]) depth !pointer_depth;
)

let checkdepth (vinfo : varinfo) = ( 

    let rec check tp = 
        match tp with 
        | TPtr(t, _) -> 1 + check t
        | _ -> 0
    in

    check vinfo.vtype
)


exception NotInList of string

let rec find x lst =
    match lst with
    | [] -> raise (NotInList "Could not find item in list")
    | h :: t -> if x = h then 0 else 1 + find x t


let rec incrdepth lval by = ( 
   match by with 
    | 0 -> lval
    | _ -> (Mem(Lval (incrdepth lval (by-1))), NoOffset)
)

let rec decrdepth lval by = ( 
    mkAddrOf lval;
)

exception NotAFunction of string

let getfunname = ( function
    | GFun(fd, _) -> fd.svar.vname;
    | _ -> raise ( NotAFunction "Attempted to visit a statement not within a function")

)


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


class registerVariables = object(self)
    inherit nopCilVisitor
    method vvrbl info  =  let funame = getfunname !currentGlobal in setdepth funame info.vname (checkdepth info); DoChildren;

end

let newfun fsmt exprs = 

 
  let genTypes expr = ( match expr with 
    | Lval(lh, off) -> ( 
        match lh with 
        | Var(info) -> [info.vname, info.vtype];
        | Mem(exp) -> print_endline "BAD GENTYPE"; [];
    );
    | _ -> [];
  ) in  

  let typelists = (List.fold_left (fun a b -> a @ b) [] (List.map genTypes exprs)) in

  let fdec = emptyFunction (newfunname ()) in
  setFunctionTypeMakeFormals fdec (mkFunTyp voidType typelists);
  let func = GFun(fdec, ({line= -1; file= "file.c"; byte= -1})) in   
  ignore(visitCilGlobal (new prepFun fsmt) func);
  
  newfuns := func :: !newfuns;
  func



let rec saveexpr (exprs: funcvar VarTypes.t ref) isset item: unit = ( 
        let save info found = (* Save the expression, to be added to params*)
            let depth = checkdepth info + isset in

            
            let cpy = ( match info.vtype with 
                    | _ -> info;
                    (* | _ -> let c = copyVarinfo info info.vname in c.vtype <- TPtr(info.vtype, []); c; *)
            ) in
            

            let wasdepth = ( 
                try (VarTypes.find info.vname !exprs).depth
                with Not_found -> -1
            ) in

            if(depth > wasdepth) then exprs := VarTypes.add info.vname {info=cpy; depth=wasdepth} !exprs
        in

        let reval = saveexpr exprs isset in

        match item with 
        | UnOp(unop, exp, typ) -> reval exp;
        | Question(e1, e2, e3, typ) -> reval e1; reval e2; reval e3; 
        | BinOp(binopp, e1, e2, t) ->  reval e1; reval e2;
        | CastE(t, exp) -> reval exp;
        | Lval(lh, off)  -> ( match lh with 
            | Var(info) ->             
                if(isFunctionType info.vtype) then () (*Don't care about functions (assume are global) *)
                else save info (Lval(lh, off));               

            | _ ->  (); )
        | _ -> ();
    )








class allExpr opt call set = object(self)
    inherit nopCilVisitor
    

    method vinst s = ( 
    match s with 
    | Set((lh, off), r1, loc) -> ( match lh with 
        | Var(info)  -> 
            set lh off r1 loc;
        | _ ->  DoChildren; ) (*TODO: Handle pointers*)
    | Call(toset, gfun, params, loc) -> (
        match toset with 
        | Some((lh, off)) -> ( 
            call lh off gfun params loc;
         );
        | _ -> DoChildren;

    );
    | _ -> DoChildren;
    );

    method vexpr = opt;

end

(** Get expression *)
let getExprs stmt = (
    let exprs = ref VarTypes.empty in

    let set lh off r1 loc = ( 
        saveexpr exprs 1 (Lval((lh, off))); 
        saveexpr exprs 0 r1;
        DoChildren;
    ) in 


    let call lh off gfun params loc =  
        saveexpr exprs 0 (Lval((lh, off))); 
        List.iter (saveexpr exprs 0) params;
        DoChildren;
    in

    let opt s = ( 
        saveexpr exprs 0 s; DoChildren;
    ) in


    let vstr = (new allExpr opt call set) in 
    ignore(visitCilStmt vstr stmt); 
    exprs; 
);;




class hasBreak out = object(self) 
    inherit nopCilVisitor

    method vstmt s = ( match s.skind with 
        | Break(_) -> (out := true; SkipChildren)
        | _ -> DoChildren;

    )

end

class fetchExpr expr = object(self) 
    inherit nopCilVisitor

    method vstmt s = match s.skind with
        | If(e, _, _, _) -> expr := e; SkipChildren
        | _ -> DoChildren;

end

let fetchExprFromIf (s: stmt) : exp = 
    let e = ref (Const(CChr('a'))) in (* dummy *)

    ignore(visitCilStmt (new fetchExpr e) s);    

    !e



let checkbreak statement = (
    let out = ref false in
    ignore (visitCilStmt (new hasBreak out) statement);
    !out
) 


class assertsSwitcher eassert = object(self) 
    inherit nopCilVisitor

    (* method vstmt s = 

        let switchInst = (function
            | Call(lval, Lval(Var(info), off), exps, loc) -> 
                if info.vname = "__CPROVER_assert" then(
                    Call(lval, v2e eassert.svar, exps, loc)
                )else Call(lval, Lval(Var(info), off), exps, loc)
            | a -> a
        ) in
    
        match s.skind with 
            | Instr(intrs) -> ChangeTo(mkStmt @@ Instr(List.map switchInst intrs))
            | a -> DoChildren *)


    method vinst = function 
            | Call(lval, Lval(Var(info), off), exps, loc) -> 
                if info.vname = "__CPROVER_assert" then(
                    ChangeTo([ 
                         Call(lval, v2e eassert.svar, exps, loc)
                    ])
                )else DoChildren
            | _ -> DoChildren

    

end

let rec cloneBlock  (blk : Cil.block) : Cil.block = 
    let rec cloneStmt s = match s.skind with 
        | If(e, b1, b2, loc) -> 
            mkStmt @@ If(e, cloneBlock b1, cloneBlock b2, loc)
        | Switch(e, b1, slist, loc) -> 
            mkStmt @@ Switch(e, cloneBlock b1, List.map cloneStmt slist, loc)
        | Block(blk) -> mkStmt @@ Block(cloneBlock blk)
        | Loop(blk, loc, so1, so2) -> (
            let ns = mkStmt @@ Loop(cloneBlock blk, loc, so1, so2) in 
            ns.sid <- s.sid;
            ns
        )
        | TryExcept(b1, is, b2, loc) -> mkStmt @@ TryExcept(cloneBlock b1, is,cloneBlock b2, loc)
        | TryFinally(b1, b2, loc) -> mkStmt @@ TryFinally(cloneBlock b1, cloneBlock b2, loc)
        | _ -> mkStmt s.skind


    in 
    mkBlock @@ List.map cloneStmt blk.bstmts


class stmtSwitcher = object(self)
    inherit nopCilVisitor


    method vstmt s = 
        ChangeTo(mkStmt s.skind)
end

let switchAsserts (smtlist : stmt list) eassert : stmt list = 


    let switchInst = (function
        | Call(lval, Lval(Var(info), off), exps, loc) -> 
            if info.vname = "__CPROVER_assert" then(
                Call(lval, v2e eassert.svar, exps, loc)
            )else Call(lval, Lval(Var(info), off), exps, loc)
        | a -> dumpStmt defaultCilPrinter stdout 1 @@ i2s a; a
    ) in


    let switchKind = (function 
        | Instr(intrs) -> Instr(List.map switchInst intrs)
        | a -> a
    ) in
    
    let switchOne sm = 

        mkStmt @@ switchKind sm.skind;
    in

    List.map switchOne smtlist;




class extractMLC assume eassert locals thisfunname (locals_locs: int list ref) = object(self)

  inherit nopCilVisitor

  method vstmt s = match s.skind with
    | Loop(blk, loc, l2, l3) -> ( 
          
            if(List.mem s.sid !locals) then ( 
                let action item = (

                    (* Has to be done asap due to a bug in CIL. This will be broken once a new visitor is called*)
                    

                    let first_break = checkbreak (List.hd blk.bstmts) in
                    let rstatements = if(first_break) then (
                        let expr =  (fetchExprFromIf (List.hd blk.bstmts)) in
                        let call = v2e assume.svar in
                        
                        i2s (Call(None, call, [expr], locUnknown)) :: List.tl blk.bstmts 
                        
                    )else blk.bstmts in

                    let replacement = (mkStmt (Block({battrs=blk.battrs; bstmts= rstatements}))) in
                    let usages = !(getExprs replacement) in
                    let exprs = (                                        
                        let out = ref [] in
                       
                        VarTypes.iter (fun a b -> out :=  Lval(Var(b.info), NoOffset) :: !out) usages;                  
                        !out;
                    ) in                 
                    

                    (*TODO: add assume each pointer not null *)
                    let asummes_valid_pointers = (
                        let pointer_params = (
                         (* List.filter 
                            (fun p -> isPointerType (typeOf p ) )
                            exprs
                        ) in *)
                        []) in
                         
                         List.map 
                            (fun p -> i2s (Call(None, (v2e assume.svar ), 
                                [BinOp(Gt, p, integer 0 , intType)],
                                locUnknown)))
                            pointer_params 
                    ) in

                    let newStmts = List.map (fun a -> mkStmt a.skind) rstatements in
                    let newb =  mkStmt @@ Block({battrs=blk.battrs; bstmts= asummes_valid_pointers @ newStmts}) in 
                    
                    ignore(visitCilBlock (new stmtSwitcher) @@ force_block newb);

                    let x = 
                        newfun 
                        (mkStmt @@ Block(cloneBlock @@ force_block @@ (newb) ))
                        exprs 
                    in (


                    funcparents := [(getfunname x); thisfunname] :: !funcparents;
                    funclocs := [(getfunname x); 
                        (getfunname x)
                        ] :: !funclocs;



                    VarTypes.iter (fun a b -> setdepth (getfunname x) b.info.vname b.depth) usages;                  
                                    


                    match x with  
                        | GFun(fdec, loc) -> (
                            ignore(visitCilGlobal (new extractMLC assume eassert locals (getfunname x) locals_locs) x);
                        
                            ignore(visitCilBlock (new assertsSwitcher eassert) blk);
                            (* mkStmt (Loop 
                            (
                                blk, loc, l2, l3
                            )) *)
                            s
                            
                        )
                        | _ ->  print_endline "ERROR"; item;

                    
                    )
                ) in
                ChangeTo(action s);
        ) else DoChildren;
    ) 
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
      visitCilFileSameGlobals (new registerVariables) f;

      let assume = findFunction  f.globals "__CPROVER_assume" in
      let eassert = findFunction  f.globals "__QICC_assert" in

      List.iter (fun g -> 
        if(match g with GFun  _ -> true | _ -> false) 
        then ignore(visitCilGlobal (new extractMLC assume eassert res.locals (getfunname g) res.locals_locs) g)) f.globals;
        

      let declarefuns func = (match func with
        | GFun(fdec, loc) -> ignore(findOrCreateFunc f fdec.svar.vname fdec.svar.vtype);
        | _ -> ()
      ) in 

      List.iter declarefuns !newfuns;
      f.globals <-  f.globals @ !newfuns;

      Errormsg.log "total: %d\n" !newfuncount;
      print_endline "FUNC CREATED - PARENT FUNC";
      List.iter (fun a -> 
            print_endline (String.concat " " ["!!CHILDOF"; List.nth a 0; List.nth a 1]
      )) !funcparents;

        List.iter (fun a -> 
            print_endline (String.concat " " ["!!FUNCLOC"; List.nth a 0; List.nth a 1]
      )) !funclocs;
      

      (* List.iter (fun a -> print_endline (string_of_int a )) !res.locals_locs *)
    );

    fd_post_check = true;
  } 

(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature
