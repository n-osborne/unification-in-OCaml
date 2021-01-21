(** * In order to make the Substitution generic, we need a Signature.

    A substitution is build upon the definition of Term.  To be a Term
   means that:

    - There is a type of variable name (or there is no sense in
   talking about substitution) that can be compared (for
   implementation reason, but the minimum requirement is decidable
   equality).

    - There is a type of term that can be traversed (applying a
   function at each variables.

    - As we don't know anything about the inductive structure of the
   term type here, the trav function should be provided by the user.

    - We will need decidable equality between terms

    - We will need to decide whether a term is a variable or not

    - We can get the list of all the variables that occurs in a term.

    - We can turn a variable name into a term (typically var x) and
   get the name of a variable (that is a partial function)

**)
module type TermType =
sig
  type v
  val compare: v -> v -> int
  type t
  val trav: (v -> t) -> t -> t    
  val eq_term: t -> t -> bool
  val isvar : t -> bool    
  val vars: t -> v list    
  val v2t : v -> t
  val t2v : t -> v option

end


module Substitution (T : TermType) =
struct
  (** A substitution is a map from variable names to terms **)
  module S = Map.Make(struct type t = T.v let compare = T.compare end)
  type substitution = T.t S.t

  (** When there is no binding for a variable name v, the substitution
     map to the variable term build with the variable name v **)
  let get (s: substitution) (v: T.v) : T.t =
    if S.mem v s then S.find v s else T.v2t v

  (** A trivial binding is a binding of a variable name to a variable
     term build with this name **)
  let is_trivial (v: T.v) (t: T.t): bool =
    match T.t2v t with
    | None -> false
    | Some n -> v = n

  (** Remove all trivial bindings from a substitution **)
  let filter_trivials: substitution -> substitution =
    S.filter (fun v t -> not (is_trivial v t))
      
  (** It is nice to get the variable names into a set (which is
     possible as the variable name type is an OrderedType **)
  module V = Set.Make(struct type t = T.v let compare = T.compare end)

  (** To apply a substitution to a term is to travers this term
     replacing all the variables by the term they are binded with in
     the substitution **)
  let apply (s: substitution) : T.t -> T.t = T.trav (get s)

  (** The domain of a substitution is the set of all the variable
     names for which a binding is defined and not trivial **)
  let dom (s: substitution) : V.t =
    V.of_seq (Seq.map fst (S.to_seq (filter_trivials s)))

  (** The range of a subsitution is the list of terms that we can get
     from it **)
  let range (s: substitution) : T.t list =
    List.of_seq (Seq.map snd (S.to_seq s))

  (** The set of variable occuring in the range of a substitution **)
  let vrange (s: substitution) : V.t =
    V.of_list (List.concat_map T.vars (range s))

  (** The restiction of a substitution s to a set x For every element
     n of the intesection of x and the domain of s, we add the binding
     of n in s to a new substitution that is build up from an empty
     one. **)
  let restict (s: substitution) (x: V.t): substitution =
    V.fold (fun n -> S.add n (S.find n s)) (V.inter x (dom s)) S.empty
      
  (** Composition of two substitution (apply sigma, then apply theta **)
  let compose (sigma: substitution) (theta: substitution) : substitution =
    let sigma1 = S.map (apply theta) sigma in
    let theta1 = V.fold S.remove (dom sigma) theta in
    let sigma2 = S.filter (fun v t -> not (is_trivial v t)) sigma1 in
    S.union (fun v t1 t2 -> Some t1) sigma2 theta1

  (** A subsitution is idempotent means that applying it twice gives
     the same result as applying it once. We know that a substitution
     s is idempotent iff the intersection between the domain of s with
     the set of variable of the range of s is empty. **)
  let idempotent (s: substitution) : bool =
    V.inter (dom s) (vrange s) = V.empty

  (** A substitution is a renaming if is domain is equals to its
     range.  As the domain and the range of our substitution are not
     the same types, we need to do some plumbing here **)
  let renaming (s: substitution): bool =
    let r = range s in
    List.for_all T.isvar r &&
    V.equal (dom s) (V.of_list (List.filter_map T.t2v r))

  (** Equal variable names give equal terms **)
  let equal (s1: substitution) (s2: substitution): bool =
    S.equal T.eq_term s1 s2

  (** In order to express the relation more general than, we need to
     provide a witness. A substitution sigma is more general than a
     substitution theta, if there exists a substitution éta such that
     theta = sigma theta.contents

      This is not really usefull. Existential quantifier would need dependent types... **)
  let more_general_than (sigma: substitution) (theta: substitution) (eta: substitution) =
    equal theta (compose sigma eta)

  (** A substitution s is a unifier of two terms if the application of
      s render the two terms equals **)
  let is_unifier (l: T.t) (r: T.t) (s: substitution): bool =
    T.eq_term (apply s l) (apply s r)
end

