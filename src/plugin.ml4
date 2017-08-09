DECLARE PLUGIN "tpi"

(** We reify the structure of coq expressions as an ocaml
    data-type. We reify only the structure of the expression
    w.r.t. the [plus], [S], and [O] symbols of Coq. All other
    sub-expressions are stored in an environment.
*)
module Arith = struct

  (** First, we initialise some constants from Coq standard library.*)
  let z0   = lazy (Lib_coq.init_constant ["Coq"; "Numbers"; "BinNums"] "Z0")
  let zneg = lazy (Lib_coq.init_constant ["Coq"; "Numbers"; "BinNums"] "Zneg")
  let zpos = lazy (Lib_coq.init_constant ["Coq"; "Numbers"; "BinNums"] "Zpos")
  let zadd  = lazy (Lib_coq.init_constant ["Coq"; "ZArith"; "BinIntDef"; "Z"] "add") (** double check it *)
   
  let xH   = lazy (Lib_coq.init_constant ["Coq"; "Numbers"; "BinNums"] "xH")
  let xO   = lazy (Lib_coq.init_constant ["Coq"; "Numbers"; "BinNums"] "xO")
  let xI   = lazy (Lib_coq.init_constant ["Coq"; "Numbers"; "BinNums"] "xI")
  
  (** [t] is an algebraic data-type that represents reified arithemtic
      expressions *)

  type p =
	| XH 
    | XI of p
	| XO of p
    | PAdd of (p * p)
    | PConst of int 
    | PVar of int	
  
  type t =
    | Z0
	| ZNeg of p
	| ZPos of p
    | Add of (t * t)
	| ZConst of int
    | ZVar of int	
	
	       
  let quote (env : Lib_coq.Env.t) (c : Term.constr) : t =
    (** First, we force the constants, once and for all  *)
    let zadd = Lazy.force zadd in 
    let z0 = Lazy.force z0 in 
    let zneg = Lazy.force zneg in
    let zpos = Lazy.force zpos in

	let xH = Lazy.force xH in 
    let xO = Lazy.force xO in
    let xI = Lazy.force xI in 
    (** Second, we decompose recursively the given term.  If the term
	is an application, we compare the head-symbol with [plus] and
	[succ]. If the term is equal to [zero], we build a
	constant. In any other case, we have to add a new variable to
	the reification environement. *)
    let rec aux c = 
	  let rec paux c =
        begin match Lib_coq.decomp_term c with
 	      | Term.App (head,args) when Term.eq_constr head xO && Array.length args = 1 ->  	  
			(** a small match to get a intelligible representation of
			constants. *)
		    begin match (paux args.(0)) with 
		      | PConst i -> PConst (i * 2)
		      | e -> XO e
		    end
 	      | Term.App (head,args) when Term.eq_constr head xI && Array.length args = 1 ->      	  
			(** a small match to get a intelligible representation of
			constants. *)
	        begin match (paux args.(0)) with 
		      | PConst i -> PConst (i * 2 + 1)
		      | e -> XI e
	        end
          | _ when Term.eq_constr c xH -> XH
		  | _ -> let i = Lib_coq.Env.add env c in PVar i
	    end
	  in
	  match Lib_coq.decomp_term c with
        | Term.App (head,args) when Term.eq_constr head zadd && Array.length args = 2 -> Add  (aux args.(0), aux args.(1))
 	    | Term.App (head,args) when Term.eq_constr head zneg && Array.length args = 1 -> ZNeg (paux args.(0))
 	    | Term.App (head,args) when Term.eq_constr head zpos && Array.length args = 1 -> ZPos (paux args.(0))
        | _ when Term.eq_constr c z0 -> Z0	  
	    | _ -> let i = Lib_coq.Env.add env c in ZVar i
    in
    aux c
end

(** Now that we have reified the structure of the term inside ocaml,
    we will reify it inside Coq (this is also the purpose of the Quote
    module of standard Coq). 
*)

module Reif = struct
  (** We initialize a new bunch of constants that correspond to the
      constructors of our inductive. *)
    
  (** This [path] correspond to the name of the logical directory
      (ML_tutorial), and the name of the library (Theory). The name of
      the logical directory must be consistent with the options given
      to coq_makefile: [-R ./src ML_tutorial] adds the physical
      directory [src] as the logical directory [ML_tutorial].
  *)
  let path = ["Tutorial";"Theory"]
  
  let add = lazy (Lib_coq.init_constant  path "a_zadd")
  let zvar = lazy (Lib_coq.init_constant  path "a_zvar")
  let zconst = lazy (Lib_coq.init_constant path "a_zconst")
  let z0 = lazy (Lib_coq.init_constant path "a_Z0")
  let zneg = lazy (Lib_coq.init_constant path "a_ZNeg")
  let zpos = lazy (Lib_coq.init_constant path "a_ZPos")

  let pvar = lazy (Lib_coq.init_constant  path "a_pvar")
  let pconst = lazy (Lib_coq.init_constant path "a_pconst")  
  let xH = lazy (Lib_coq.init_constant path "a_xH")
  let xO = lazy (Lib_coq.init_constant path "a_xO")
  let xI = lazy (Lib_coq.init_constant path "a_xI")


  let eval = lazy(Lib_coq.init_constant path "eval")

  (** [eval] is the Coq function that maps a reified Coq arithmetic
      expression back to a nat *)

  (** [to_constr t] build the Coq term that corresponds to [t]. *)
  let rec to_constr (t: Arith.t) : Term.constr = 
    let rec to_constr_p (p: Arith.p)  =
	  match p with
        | Arith.XO a -> Term.mkApp (Lazy.force xO, [|(to_constr_p a)|])
        | Arith.XI a -> Term.mkApp (Lazy.force xI, [|(to_constr_p a)|])
        | Arith.XH ->  (Lazy.force xH)
        | Arith.PConst n -> Term.mkApp (Lazy.force pconst, [|(Lib_coq.Positive.to_positive n)|])
        | Arith.PVar n -> Term.mkApp (Lazy.force pvar, [|(Lib_coq.Positive.to_positive (n+1))|]) 
	in
    match t with
      | Arith.Add (a, b) -> Term.mkApp (Lazy.force add, [|(to_constr a); (to_constr b)|])
      | Arith.ZNeg a -> Term.mkApp (Lazy.force zneg, [|(to_constr_p a)|])
      | Arith.ZPos a -> Term.mkApp (Lazy.force zpos, [|(to_constr_p a)|])
      | Arith.Z0 ->  (Lazy.force z0)
      | Arith.ZConst n -> Term.mkApp (Lazy.force zconst, [|(Lib_coq.Z.to_Z n)|])
      | Arith.ZVar n -> Term.mkApp (Lazy.force zvar, [|(Lib_coq.Z.to_Z n)|])
	
  (** [env_to_constr env] build the Coq list that correspond to the
      environment map. We build a uniform Coq list of nat of type
      [list nat]. More complex situations may be treated in subsequent
      tutorials. *)
  let env_to_constr (env : Lib_coq.Env.t) : Term.constr = 
    let l = Lib_coq.Env.to_list env in 
    Lib_coq.List.of_list (Lazy.force Lib_coq.Z.typ) l
      
  (** [build_eval env t] builds the Coq term that corresponds to [eval
      env t]. *)
  let build_eval (env : Term.constr) (t : Arith.t) : Term.constr =
    Term.mkApp (Lazy.force eval, [|env; to_constr t|])
	
  (** [tac] is the final tactic. *)
  let tac : unit Proofview.tactic =
      Proofview.Goal.enter (fun gl ->   
      (** We get the conclusion of the as a goal, which is a constr.
          (see [proofs/proofview.mli].)  *)
      let concl = Proofview.Goal.raw_concl gl in
      
      (** In our particular setting, the conclusion of the goal must
	  be a relation applied to at least two arguments (the
	  left-hand side and the right-hand side) of the
	  "equation".  *)
      match Lib_coq.decomp_term concl with
	| Term.App(c, args) when Array.length args >= 2 ->
          let n = Array.length args in
       	  let left = args.(n-2) in
       	  let right = args.(n-1) in 
	  (** We initialize the environment, to reify the left
	      hand-side and the right-hand side of the equation*)
       	  let arith_env = Lib_coq.Env.empty () in
       	  let left' = Arith.quote arith_env left in
       	  let right' = Arith.quote arith_env right in
	  let coq_env = env_to_constr arith_env in
	  (** We want to move from 
	      {C left == right}
	      to
	      {C (eval env left') == (eval env right')}
	  *)
          args.(n-2) <- build_eval coq_env left';
          args.(n-1) <- build_eval coq_env right';
       	  let concl' = Term.mkApp (c, args)
	  in
	  (** We use a {i tactical} to chain together a list of
	      tactics (as would be done using a semi-column in Coq).
	      (see [tactics/tacticals.mli] for other tacticals.)  *)
       	  Tacticals.New.tclTHENLIST
	    [
	      (** Our list of tactics consists in the following single
       		  tactic, that changes the conclusion of the goal to
       		  [concl'] if [concl] and [concl'] are convertible. 
		  (see [tactics/tactis.mli] for other tactics.)  *)
	      Tactics.change_concl concl' ;
	    ]
	| _ -> 
	  (** If the goal was not looking like a relation applied to two
	      arguments, we fail using the tacticals [tclFAIL]. 
	      
	      The documentation of fail is
	      {{:http://coq.inria.fr/refman/Reference-Manual012.html#@tactic183}here}

	      In a nutshell [tclFAIl] has type [int -> Pp.std_ppcmds ->
	      tactic]. The number is the failure level (0 means that
	      an englobing [match goal] may proceed to the next clause
	      and [try] succeeds, while n > 1 means that the current
	      [match goal] or [try] is aborted, and the level is
	      decremented. 

	      The [Pp.std_ppcmds] is a pretty-printer command. 
	      
	      (see lib/pp.mli for more functions)
	  *)
	  Tacticals.New.tclFAIL 1
	    (Pp.str "The goal does not look like an equation"))
end
  
(** The final magic part is to register our custom tactic in
    Coq. [_reflect_] is the name of this tactic extension (I do not know
    what it is used for). [Reif.tac] is our custom
    tactic. [reflect_arith] is the string through which this tactic
    can be invoked inside Coq. 
*)

TACTIC EXTEND _brkZ_
| ["reflect_Z"] -> [Reif.tac]
END

