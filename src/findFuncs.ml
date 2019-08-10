(* A sample CIL plugin *)

(* API changes from 1.7.3 are marked with XXX below *)

open Cil
open Feature (* XXX you need to open the Feature module *)
open Sys
open Tututil

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false


let getfunname = ( function
    | GFun(fd, _) -> fd.svar.vname;
    | _ -> "NOT_A_FUN_______________________________________"
)

class hasAssert asserts= object(self)
  inherit nopCilVisitor

  method vinst = function
  | Call(_, expr, _, loc)-> (
        match expr with
        | Lval(lh, off) -> 
          match lh with 
          | Var(info) -> (if(contains info.vname "__CPROVER") then asserts := getfunname !currentGlobal :: !asserts;
          )
          | _ -> ();
          ;
        | _ -> ();
        ;

        DoChildren;

  );
  | _ -> DoChildren
end


class parents funcparents = object(self)
  inherit nopCilVisitor

  method vinst = function
  | Call(_, expr, _, loc)-> (
        match expr with
        | Lval(lh, off) -> 
          match lh with 
          | Var(info) -> if(not (contains info.vname "__CPROVER")) then (
               funcparents := [(info.vname); getfunname !currentGlobal] :: !funcparents;
          ) 
          | _ -> ();
          ;
        | _ -> ();
        ;

        DoChildren;

  );
  | _ -> DoChildren
end



(* XXX Cil.featureDescr is now Feature.t *)
let feature : Feature.t = {
    fd_name = "countCalls";
    fd_enabled = true; (* XXX fd_enabled is now a bool, not a bool ref anymore. *)
    fd_description = "count and display the number of function calls";
    fd_extraopt = [];
    fd_doit = (function f ->

      let asserts = ref [] in

      let print_fun_if (g: global) = (
          if((Sys.getenv "FUN_NAME") = (getfunname g)) then (
            dumpGlobal defaultCilPrinter stdout g 
          );
      ) in


      let cmd = Sys.getenv "FIND_COMMAND" in
      match cmd with 
       | "GET_FUNC" -> List.iter print_fun_if f.globals;
       | "GET_ASSERT_FUNCS" ->  ( 
         visitCilFileSameGlobals (new hasAssert asserts) f;
         List.iter print_endline !asserts;
       
       )
       | "GET_ALL_FUNCS" -> (
          List.iter (onlyFunctions (fun fd loc -> (print_endline fd.svar.vname))) f.globals;
       )
       | "GET_PARENTS" -> (
          let funcparents = ref [] in 
          visitCilFileSameGlobals (new parents funcparents) f;
          List.iter (fun a -> 
            print_endline (String.concat " " ["!!CHILDOF"; List.nth a 0; List.nth a 1]
          )) !funcparents;
       )
       | _ -> print_endline "INVALID COMMAND";
    

    );
    fd_post_check = true;
  } 

(* XXX you need to register each feature using Feature.register. *)
let () = Feature.register feature