module type TermSignature =
sig
  type v
  type c
  val v_eq: v -> v -> bool
  val v_cmp: v -> v -> int
  val c_eq: c -> c -> bool
  val ar: c -> int
end

module Unification (TS: TermSignature) =
struct

  (** A term is either a variable or a constant with a list of terms,
      which lenght is hopefully equal to the arity of the constant **)
  type term =
    | V of TS.v
    | C of TS.c * term list

  let rec t_eq (t1: term) (t2: term): bool =
    match t1, t2 with
    | V n1, V n2 -> TS.v_eq n1 n2
    | C (c1, l1), C (c2, l2) ->
      TS.c_eq c1 c2 &&
      List.for_all (fun (x1, x2) -> t_eq x1 x2) (List.combine l1 l2)
    | _ -> false

  let is_var: term -> bool = function
    | V _ -> true
    | _ -> false

  let to_var: term -> TS.v option =
    function
    | V n -> Some n
    | _   -> None
      
  (** check whether the constants have the right arity **)
  let rec check: term -> bool =
    function
    | V _ -> true
    | C (c, l) -> (List.length l = TS.ar c) && (List.for_all check l)

  (** Recursively traverse a term doing something to its variables **)
  let rec trav (f: TS.v -> term): term -> term =
    function
    | V v      -> f v
    | C (c, l) -> C (c, List.map (trav f) l)

  let rec vars: term -> TS.v list =
    let rec aux acc = function
      | V n -> n :: acc
      | C (_, l) -> List.append acc (List.concat_map (aux []) l)
    in aux []

  (** A subst is a map from variable names to terms **)
  module S = Map.Make(struct type t = TS.v let compare = TS.v_cmp end)
  type subst = term S.t

  (** When there is no binding for a variable name v, the subst
      map to the variable term build with the variable name v **)
  let get (s: subst) (v: TS.v) : term =
    if S.mem v s then S.find v s else V v

  (** A trivial binding is a binding of a variable name to a variable
     term build with this name **)
  let is_trivial (v: TS.v): term -> bool =
    function
    | V n -> TS.v_eq v n
    | C _ -> false

  (** Remove all trivial bindings from a subst **)
  let filter_trivials: subst -> subst =
    S.filter (fun v t -> not (is_trivial v t))
      
  (** It is nice to get the variable names into a set (which is
     possible as the variable name type is an OrderedType **)
  module V = Set.Make(struct type t = TS.v let compare = TS.v_cmp end)

  (** To apply a subst to a term is to travers this term
     replacing all the variables by the term they are binded with in
     the subst **)
  let apply (s: subst) : term -> term = trav (get s)

  (** The domain of a subst is the set of all the variable
     names for which a binding is defined and not trivial **)
  let dom (s: subst) : V.t =
    V.of_seq (Seq.map fst (S.to_seq (filter_trivials s)))

  (** The range of a subsitution is the list of terms that we can get
     from it **)
  let range (s: subst) : term list =
    List.of_seq (Seq.map snd (S.to_seq s))

  (** The set of variable occuring in the range of a subst **)
  let vrange (s: subst) : V.t =
    V.of_list (List.concat_map vars (range s))

  (** The restiction of a subst s to a set x For every element
     n of the intesection of x and the domain of s, we add the binding
     of n in s to a new subst that is build up from an empty
     one. **)
  let restict (s: subst) (x: V.t): subst =
    V.fold (fun n -> S.add n (S.find n s)) (V.inter x (dom s)) S.empty
      
  (** Composition of two subst (apply sigma, then apply theta **)
  let compose (sigma: subst) (theta: subst) : subst =
    let sigma1 = S.map (apply theta) sigma in
    let theta1 = V.fold S.remove (dom sigma) theta in
    let sigma2 = S.filter (fun v t -> not (is_trivial v t)) sigma1 in
    S.union (fun _ t1 _ -> Some t1) sigma2 theta1

  (** A subsitution is idempotent means that applying it twice gives
     the same result as applying it once. We know that a subst
     s is idempotent iff the intersection between the domain of s with
     the set of variable of the range of s is empty. **)
  let idempotent (s: subst) : bool =
    V.inter (dom s) (vrange s) = V.empty

  (** A subst is a renaming if is domain is equals to its
     range.  As the domain and the range of our subst are not
     the same types, we need to do some plumbing here **)
  let renaming (s: subst): bool =
    let r = range s in
    List.for_all is_var r &&
    V.equal (dom s) (V.of_list (List.filter_map to_var r))

  (** Equal variable names give equal terms **)
  let equal (s1: subst) (s2: subst): bool =
    S.equal t_eq s1 s2

  (** In order to express the relation more general than, we need to
     provide a witness. A subst sigma is more general than a
     subst theta, if there exists a subst éta such that
     theta = sigma theta.contents

      This is not really usefull. Existential quantifier would need dependent types... **)
  let more_general_than (sigma: subst) (theta: subst) (eta: subst) =
    equal theta (compose sigma eta)

  (** A subst s is a unifier of two terms if the application of
      s render the two terms equals **)
  let is_unifier (l: term) (r: term) (s: subst): bool =
    t_eq (apply s l) (apply s r)  
end

