theory Poly
imports Main Basics Lists 
begin

(* (** * Poly: Polymorphism and Higher-Order Functions *)
(* Version of 4/7/2010 *)

Require Export Lists.

(* ###################################################### *)
(** * Polymorphism *)

(* ###################################################### *)
(** ** Polymorphic lists *)

(** Up to this point, we've been working with lists of numbers.
    Programs also need to be able to manipulate lists whose elements
    are drawn from other types -- lists of strings, lists of booleans,
    lists of lists, etc.  We could define a new inductive datatype for
    each of these, for example... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... but this would quickly become tedious,
    partly because we have to make up different
    constructor names for each datatype but mostly because
    we would also need to define new versions of all our
    list manipulating functions ([length], [rev], etc.)
    for each new datatype definition. *)

(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a polymorphic
    list data type. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
*)

(* CL:  As we've previously discussed, there's polymorphic inductive datatypes
        in Isabelle.  Most of this material related to implicit parameters 
        isn't particularly relevant *)

(* 
(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We're able to re-use the constructor names [nil] and
    [cons] because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.) *)

(** With this definition, when we use the constructors [nil] and
    [cons] to build lists, we need to specify what sort of lists we
    are building -- that is, [nil] and [cons] are now "polymorphic
    constructors".  Observe the types of these constructors: *)

Check nil. 
Check cons. 

(** The "[forall X]" in these types should be read as an
    additional argument to the constructors that determines the
    expected types of the arguments that follow.  When [nil] and
    [cons] are used, these arguments are supplied in the same way as
    the others.  For example, the list containing [2] and [1] is
    written like this: *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** We can now go back and make polymorphic (or "generic")
    versions of all the list-processing functions that we wrote
    before.  Here is [length], for example: *)

Fixpoint length (X:Type) (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(** The uses of [nil] and [cons] in [match] patterns do not
    require any type annotations: we already know that the list [l]
    contains elements of type [X], so there's no reason to include [X]
    in the pattern.  (More formally, the type [X] is a parameter of
    the whole definition of [list], not of the individual
    constructors.)

    Just as we did with [nil] and [cons], to use [length] we apply it
    first to a type and then to its list argument: *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(** (We are writing [nil] and [cons] here because we haven't yet
    defined the [ [] ] and [::] notations.  We'll do that in a
    bit.) *)

(** To use our length with other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

Fixpoint app (X : Type) (l1 l2 : list X) 
                : (list X) := 
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) := 
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X := 
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat))) 
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2: 
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** *** Argument Synthesis *)
*)
(* 
(** Whenever we use a polymorphic function, we need to pass it
    one or more types in addition to its other arguments.  For
    example, the recursive call in the body of the [length] function
    above must pass along the type [X].  But this is a bit heavy and
    verbose: Since the second argument to [length] is a list of [X]s,
    it seems entirely obvious that the first argument can only be
    [X] -- why should we have to write it explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please figure out for yourself what
    type belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to "unify" all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    Using implicit arguments, the [length] function can be written
    like this: *)

Fixpoint length' (X:Type) (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(** In this instance, the savings of writing [_] instead of [X] is
    small.  But in other cases the difference is significant.  For
    example, suppose we want to write down a list containing the
    numbers [1], [2], and [3].  Instead of writing this... *)

Definition list123'' := 
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use argument synthesis to write this: *)

Definition list123 := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Implicit arguments *)

(** To avoid writing too many [_]'s, we can also tell Coq that we
    _always_ want it to infer the type argument(s) of a given
    function. *)

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Check (length list123).  (* note: no _ *)

(** We can also conveniently declare an argument to be implicit
    while defining the function itself, by surrounding the argument in
    curly braces.  For example: *)

Fixpoint length'' {X:Type} (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(** Note that in this case, we didn't even have to provide a
    type argument to the recursive call to [length'']. We will use
    this style whenever possible, although we will continue to use use
    explicit [Implicit Argument] declarations for [Inductive]
    constructors. *)

(** One small problem with declaring arguments [Implicit] is
    that, occasionally, there will not be enough local information to
    determine a type argument and we will need to tell Coq specially
    that we want to give it explicitly even though we've declared it
    to be [Implicit].  For example, if we write: *)

(* Definition mynil := nil. *)

(** Coq will give us an error, because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration: *)

Definition mynil : list nat := nil.

(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer the type when we use these. *)

Notation "x :: y" := (cons x y) 
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

(** Now lists can be written just the way we'd hope: *)

Definition list123' := [1, 2, 3].

(* ###################################################### *)
(** *** Exercises: Polymorphic lists *)

(** **** Exercise: 2 stars, optional (poly_exercises) *)
(** Here are a few simple exercises, just like ones in Lists.v, for
    practice with polymorphism.  Fill in the definitions and complete
    the proofs below. *)

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X := 
  (* SOLUTION: *)
  match count with
  | O => nil 
  | S count' => cons n (repeat _ n count')
  end.

Example test_repeat1: 
  repeat bool true 2 = cons true (cons true nil).
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Theorem nil_app : forall X:Type, forall l:list X, 
  app [] l = l.
Proof.
  (* SOLUTION: *)
   reflexivity.
Qed.

Theorem rev_snoc : forall X : Type, 
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  (* SOLUTION: *)
  intros X v s. induction s as [| v' s'].
  Case "s = []".
    reflexivity.
  Case "s = v' :: s'".
    simpl. rewrite -> IHs'. reflexivity.
Qed.

(** **** Exercise: 2 stars, optional *)
Theorem snoc_with_append : forall X : Type, 
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* SOLUTION: *)
  intros X l1 l2 v. induction l1 as [| v1 l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = v1 :: l1'".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.
(** [] *)

(* ###################################################### *)
(** ** Polymorphic pairs *)

(** Similarly, the type definition we gave above for pairs of
    numbers can be generalized to "polymorphic pairs": *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Implicit Arguments pair [X Y].

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for pair _types_: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should be used when parsing types.) *)

(** The first and second projection functions now look pretty
    much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X := 
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y := 
  match p with (x,y) => y end.

(** The following function takes two lists and combines them
    into a list of pairs.  (In many functional programming languages,
    it is called [zip].  We call it [combine] for consistency with
    Coq's standard library.) *)
*)

(* CL:  I'm going to do these using the built in list and product operators. 
        If that's cheating, let me know!
*)

(* 
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) 
           : list (X*Y) :=
  match lx with
  | [] => []
  | x::tx => match ly with
             | [] => []
             | y::ty => (x,y) :: (combine tx ty)
             end
  end.
*)
fun combine :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
"combine [] _ = []" |
"combine _ [] = []" |
"combine (x # xs) (y # ys) = (x,y) # (combine xs ys)"

(* 
(** **** Exercise: 1 star (combine_checks) *)
(** Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check 
      @combine] print?)
    - What does
[[
 Eval simpl in (combine [1,2] [false,false,true,true]).
]]
      print?   []
*)

(** **** Exercise: 2 stars *)
(** The function [split] is the inverse of combine: it takes a list of
    pairs and returns a pair of lists.  In many functional programing
    languages, this function is called "unzip".

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split 
  (* SOLUTION: *)
           {X Y : Type} (l : list (X*Y)) 
           : (list X) * (list Y) :=
  match l with
  | [] => 
      ([], []) 
  | cons (x,y) t => 
      match split t with
        (lx,ly) => (x::lx, y::ly)
      end
  end.
*)

fun split :: "('a \<times> 'b) list \<Rightarrow> ('a list \<times> 'b list)" where
"split [] = ([],[])" |
"split ((x,y) # xys) = (case (split xys) of
                         (xs,ys) \<Rightarrow> (x # xs, y # ys))"

(* 
Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** ** Polymorphic options *)

(** One last polymorphic type for now: "polymorphic options".
    The type declaration generalizes the one for [natoption] from the
    previous chapter: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [X].
Implicit Arguments None [X].

(** We can now rewrite the [index] function so that it works
    with any type of lists. *)

Fixpoint index 
             {X : Type} (n : nat)
             (l : list X) : option X :=
  match l with
  | [] => None 
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1],[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(** **** Exercise: 1 star *)
(** Complete the definition of a polymorphic version of the
    [hd_opt] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  (* SOLUTION: *)
  match l with
  | [] => None 
  | a :: l' => Some a 
  end.

(** To force the implicit arguments to be explicit, we can use [@]
    before the name of a function. *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1,2] = Some 1. 
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_hd_opt2 :   hd_opt  [[1],[2]]  = Some [1].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(* ###################################################### *)
(** * Functions as Data *)

(* ###################################################### *)
(** ** Higher-order functions *)

(** Like many other modern programming languages -- including,
    of course, all "functional languages" -- Coq treats functions as
    first-class citizens: it allows functions to be passed as
    arguments to other functions, returned as results from other
    functions, stored in data structures, etc.  

    Functions that manipulate other functions are called
    "higher-order" functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X := 
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)
Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Partial application *)

(** In fact, the multiple-argument functions we have already
    seen are also examples of higher-order functions.  For instance,
    the type of [plus] is [nat -> nat -> nat]. *)

Check plus.

(** Since [->] is _right-associative_, this type can
    equivalently be written [nat -> (nat -> nat)] -- i.e., it can be
    read as saying that "[plus] is a one-argument function that takes
    a [nat] and returns a one-argument function that takes another
    [nat] and returns a [nat]."  In the examples above, we have always
    applied [plus] to both of its arguments at once, but if we like we
    can supply just the first.  This is called "partial
    application." *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Digression: Currying *)

(** **** Exercise: 2 stars, optional (currying) *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    "currying", named in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called "uncurrying".  In an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* SOLUTION: *)
    match p with
      (x,y) => f x y
    end.

(** (Thought exercise: before running these commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]?) *)
Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* SOLUTION: *)
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* SOLUTION: *)
  intros X Y Z f p.
  destruct p as [x y].
  reflexivity.
Qed.
(** [] *)

(* ###################################################### *)
(** ** Filter *)

(** Here is a useful higher-order function, which takes a list
    of [X]s and a predicate on [X] (a function from [X] to [bool]) and
    "filters" the list, returning a new list containing just those
    elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X) 
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2: 
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** We can use [filter] to give a concise version of the
    [countoddmembers] function from [Lists.v]. *)

Definition countoddmembers' (l:list nat) : nat := 
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0,2,4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Anonymous functions *)

(** It was annoying to be forced to define the function
    [length_is_1] and give it a name just to be able to pass it as an
    argument to [filter], since we will probably never use it again.
    This is not an isolated example.  When using higher-order
    functions, we will often pass as arguments "one-off" functions
    that we will never use again; having to give each of these
    functions a name would be tedious.

    However, there is a solution. It is also possible to construct a
    function "on the fly" without declaring it at the top level or
    giving it a name; this is analogous to the notation we've been
    using for writing down constant lists, etc. *)
*)

(* CL:  In Isabelle, we declare anonymous function as lambda expressions
        e.g. (\<lambda>x. x) *)

(* 
Example test_anon_fun: 
  doit3times (fun (n:nat) => mult n n) 2 = 256.
Proof. reflexivity.  Qed.

(** The expression [fun (n:nat) => mult n n] here can be read
    "The function that, given a number [n], returns [mult n n]."

    We don't actually need to bother declaring the type of the
    argument [n]; Coq can see that it must be [nat] by looking at the
    context.  This convenient capability is called _type inference_. *)

Example test_anon_fun': 
  doit3times (fun n => mult n n) 2 = 256.
Proof. reflexivity.  Qed.

(** Here is our motivating example from before, rewritten to use
    an anonymous function. *)

Example test_filter2': 
    filter (fun l => beq_nat (length l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars, optional *)
(** Use [filter] to write a coq function [partition]: 
[[
  partition : forall X : Type, (X -> bool) -> list X -> list X * list X
]]
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
*)

Definition partition {X : Type} (test : X -> bool) (l : list X) 
                     : list X * list X :=
(* SOLUTION: *)
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
(* SOLUTION: *)
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
(* SOLUTION: *)
Proof. reflexivity. Qed.
(** [] *)

(* ###################################################### *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) 
             : (list Y) := 
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity.  Qed.

(** The element types of the input and output lists need not be
    the same ([map] takes _two_ type arguments, [X] and [Y]).  This
    version of [map] can thus be applied to a list of numbers and a
    function from numbers to booleans to yield a list of booleans: *)

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity.  Qed.

(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a list of lists of booleans: *)

Example test_map3: 
    map (fun n => [evenb n,oddb n]) [2,1,2,5] 
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity.  Qed.


Theorem map_snoc : forall (X Y : Type) 
                          (f : X -> Y) (x : X) (l : list X),
  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros X Y f x l. induction l as [| v l'].
  Case "l = []".
    reflexivity.
  Case "l = v :: l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(** **** Exercise: 2 stars, optional *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* SOLUTION: *)
  intros X Y f l. induction l as [| v l']. 
  Case "l = []".
    reflexivity.
  Case "l = v :: l'".
    simpl. rewrite -> map_snoc. rewrite -> IHl'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
[[
        flat_map (fun n => [n,n,n]) [1,5,4]
      = [1, 1, 1, 5, 5, 5, 4, 4, 4].
]]
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) 
                   : (list Y) := 
  (* SOLUTION: *)
  match l with
  | []     => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1: 
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(** Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)

Definition map_option {X Y : Type} (f : X -> Y) (xo : option X) 
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 1 star, optional (implicit_args) *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.  [] *)

(* ###################################################### *)
(** ** Fold *)

(** An even more powerful higher-order function is called [fold].  It
    is the inspiration for the "[reduce]" operation that lies at the
    heart of Google's map/reduce distributed programming framework. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1,2,3,4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,
[[
   fold plus [1,2,3,4] 0
]]
    yields
[[
   1 + (2 + (3 + (4 + 0))).
]]
    Here are some more examples:
*)

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app  [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, optional *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* ###################################################### *)
(** ** Functions For Constructing Functions *)

(** Most of the higher-order functions we have talked about so
    far take functions as _arguments_.  Now let's look at some
    examples involving _returning_ functions as the results of other
    functions.

    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called. *)

Definition constfun {X: Type} (x: X) : nat->X := 
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** Similarly, but a bit more interestingly, here is a function
    that takes a function [f] from numbers to some type [X], a number
    [k], and a value [x], and constructs a function that behaves
    exactly like [f] except that, when called with the argument [k],
    it returns [x]. *)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

(** For example, we can apply [override] twice to obtain a
    function from numbers to booleans that returns [false] on [1] and
    [3] and returns [true] on all other arguments. *)

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star *)
(** Before starting to work on the following proof, make sure you
    understand exactly what the theorem is saying and can paraphrase
    it in english.  The proof itself is straightforward. *) 

Theorem override_example : forall (b:bool), 
  (override (constfun b) 3 true) 2 = b.
Proof.
  (* SOLUTION: *)
  intros b.
  simpl. reflexivity.
Qed.
(** [] *)

(** We'll use function overriding heavily in parts of the rest of the
    course, and we will end up needing to know quite a bit about its
    properties.  To prove these properties, though, we need to know
    about a few more of Coq's tactics; developing these is the main
    topic of the rest of the chapter. *)

(* ###################################################### *)
(** * More About Coq *)

     
(** ###################################################### *)
(** ** The [unfold] tactic *)

(** The precise behavior of the [simpl] tactic is subtle: even
    expert Coq users tend to work with it by just trying it and seeing
    what it does in particular situations, rather than trying to
    predict in advance.  However, one point is worth noting: [simpl]
    never expands names that have been declared as [Definition]s.

    For example, these two expressions do not simplify to the same
    thing.
*)

Eval simpl in (plus 3 5).
Eval simpl in (plus3 5).

(** The opacity of definitions shows up in other places too.
    For example, there are times when a proof will get stuck because
    Coq can't automatically see that two terms are equal because one
    of them involves a definition. *)

Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n = m.
Proof.
  intros m n H.
  (* At this point, we'd like to do [rewrite -> H], but it fails
     because Coq doesn't realize that [plus3 n] is definitionally
     equal to [3 + n]. *) 
  Admitted.

(** The [unfold] tactic can be used to explicitly replace a
    defined name by the right-hand side of its definition.  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n = m.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

(** Now we can prove a first property of [override]: If we
    override a function at some argument [k] and then look up [k], we
    get back the overriden value. *)

Theorem override_eq : forall (X:Type) x k (f : nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

(** This proof was straightforward, but note that it requires
    [unfold] to expand the definition of [override]. *)

(** **** Exercise: 2 stars *)
Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  (* SOLUTION: *)
  intros X x1 x2 k1 k2 f. intros Hx1 Hneq.
  unfold override.
  rewrite -> Hneq.
  apply Hx1.
Qed.
(** [] *)

(* ###################################################### *)
(** ** Inversion *)

(** Recall the definition of natural numbers:
[[
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
]]
   It is clear from this definition that every number has one of two
   forms: either it is the constructor [O] or it is built by applying
   the constructor [S] to another number.  But there is more here than
   meets the eye: implicit in the definition (and in our informal
   understanding of how datatype declarations work in other
   programming languages) are two other facts:

   - The constructor [S] is "injective".  That is, the only way we can
     have [S n = S m] is if [n = m].

   - The constructors [O] and [S] are "disjoint".  That is, [O] is not
     equal to [S n] for any [n].
*)

(* CL:  inversion in Coq is interesting!  It doesn't quite correspond to 
        just one thing in Isabelle, as far as I can tell, because not
        every construction in Isabelle is an inductive type.  At least
        I think that's the issue.  For the purposes of this chapter,
        I believe that cases is the closest analog to inversion.  *)

(* 
   Similar principles apply to all inductively defined types: all
   constructors are injective, and the values built from distinct
   constructors are never equal.  For lists, the [cons] constructor is
   injective and [nil] is different from every non-empty list.  For
   booleans, [true] and [false] are unequal.  (Since neither [true]
   nor [false] take any arguments, their injectivity is not an issue.)
 *)

(** Coq provides a tactic, called [inversion], that allows us to
    exploit these principles in making proofs.
 
    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
[[
      c a1 a2 ... an = d b1 b2 ... bm
]]
    for some constructors [c] and [d] and arguments [a1 ... a2] and
    [b1 ... bm].

    Then [inversion H] instructs Coq to "invert" this equality to
    extract the information it holds about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [G] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)(** The
      [inversion] tactic is probably easier to understand by seeing it
      in action than from general descriptions like the above.  Below
      you will find example theorems which demonstrate the use of
      [inversion] and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.
Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.
Qed.

(** As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)
Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity.
Qed.

(** **** Exercise: 1 star *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* SOLUTION: *)
  intros X x y z l j eq1 eq2.
  inversion eq1. inversion eq2. symmetry. apply H0.
Qed.
(** [] *)
*)

lemma assumes H1:"(x # y # l) = (z # j)" and H2:"(y # l) = (x # j)"
      shows "x = y"
proof -
  have "x # x # j = z # j" using H2 H1 by simp 
  thus "x = y" using H1 H2 by simp
qed

(* CL:  Yeah, since the = in Isabelle isn't an inductive type we can't
        really play the inversion game. On the other hand, we can certainly
        play the game of just using the simplifier because it actually
        handles equalities in a sensible way. auto doesn't blast out
        the solution just because it's a touch too hard to see the trick
        but if you break it into two pieces in Isar the simp can handle it
        fine. *)

(* 
Theorem silly6 : forall (n : nat),
     S n = O ->
     plus 2 2 = 5.
Proof.
  intros n contra. inversion contra. 
Qed.
*)

lemma "(1 :: nat) + 0 = 0 \<Longrightarrow> 2 + 2 = 5"
by simp

(* CL:  I find the above interesting, because the fact that
        Suc n \<noteq> 0 is NOT just an application of some kind of inversion,
        but a more complicated application of the inductive rules; however,
        I think that might just be an artifact of trying to make nat 
        a low level built in type in Isabelle.  Let's try something really
        simple as our own nat as a test!! *)

(* 

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra. 
Qed.

(** **** Exercise: 1 star *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* SOLUTION: *)
  intros X x y z l j eq1 eq2. inversion eq1.
Qed.
(** [] *)

(** Here is a more realistic use of inversion to prove a
    property that is useful in many places later on... *)

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n']. 
  Case "n = 0". 
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'". simpl. intros contra. inversion contra. 
  Case "n = S n'". 
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      rewrite -> (IHn' m' H). reflexivity.
Qed.

(** **** Exercise: 2 stars (beq_nat_eq_informal) *)
(** Give an informal proof of [beq_nat_eq]. *)

(** THEOREM: For all natural numbers n and m, if [true = beq_nat n m],
      then [n = m].
 
(* SOLUTION: *)
    PROOF: By induction on [n].

      - Suppose [n = 0].  We must show that if [true = beq_nat 0 m],
        then [0 = m].  We proceed by cases on m.
        
          - If [m = 0], we must show [0 = 0], which is true by
            reflexivity.

          - If [m = S m'], our hypothsis states that [true = beq_nat 0
            (S m')].  But [beq_nat 0 (S m')] reduces to [false], so
            this is absurd.

      - Otherwise, [n = S n'], and the inductive hypothesis states
        that for all natural numbers m', if [true = beq_nat n' m'],
        then [n' = m'].  We must show that if [true = beq_nat (S n')
        m], then [S n' = m].  We again proceed by cases on m.

          - If [m = 0], the hypothesis states that [true = beq_nat (S
            n') 0], which is absurd.

          - Otherwise [m = S m'].  Our hypothesis now states that
            [true = beq_nat (S n') (S m')], which simplifies to [true
            = beq_nat n' m'].  We may therefore apply the inductive
            hypothesis (instantiated at m') to conclude that [n' =
            m'], which immediately implies that [S n' = S m']. []
   []
*)

(** **** Exercise: 2 stars *)
(** We can also prove beq_nat_eq by induction on [m] (though we
    have to be a little careful about which order we introduce
    the variables, so that we get a general enough induction
    hypothesis; this is done for you below).  Finish the
    following proof.  To get maximum benefit from the exercise,
    try first to do it without looking back at the one above. *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m']. 
  (* SOLUTION: *)
    Case "m = 0". 
      intros n. destruct n as [| n'].
      SCase "n = 0". reflexivity.  
      SCase "n = S n'". simpl. intros contra. inversion contra. 
    Case "m = S m'". 
      intros n. destruct n as [| n'].
      SCase "n = 0". intros contra. inversion contra.
      SCase "n = S n'". simpl. intros H.
        assert (n' = m') as H1.
          apply IHm'. apply H.
        rewrite -> H1. reflexivity.
Qed.
(** [] *)

(** Here's another illustration of [inversion].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)
*)

lemma "length l = n \<Longrightarrow> length (snoc l v) = Suc n"
apply (induct l, simp_all)
done

(*
Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'". 
      assert (length (snoc l' v) = S n').
        SSCase "Proof of assertion". apply IHl'. 
        inversion eq. reflexivity.
      rewrite -> H. reflexivity.
Qed.

(* ###################################################### *)
(** *** Practice session *)


(** **** Exercise: 2 stars, optional (practice) *)
(** Some nontrivial but not-too-complicated proofs to work together in
    class, and some for you to work as exercises.  Some of the
    exercises may involve applying lemmas from earlier lectures or
    homeworks. *)
 

Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  (* SOLUTION: *)
  intros n. intros Heq.
  destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    inversion Heq.
Qed.

Theorem beq_nat_0_r : forall n,
  true = beq_nat n 0 -> 0 = n.
Proof.
  (* SOLUTION: *)
  intros n. intros Heq.
  destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    inversion Heq.
Qed.
(** [] *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
*)

primrec dub :: "nat \<Rightarrow> nat" where
"dub 0 = 0" |
"dub (Suc n) = Suc (Suc (dub n))"

lemma "\<forall> m. (dub n = dub m) \<longrightarrow> n = m"
apply (induct n)
by (intro allI, case_tac m, simp+)+

lemma "(dub n = dub m) \<Longrightarrow> n = m"
apply (induct n arbitrary: m)
by (case_tac m, simp+)+

(* CL: EWW - let's do better *)
(* *)
lemma "dub n = dub m \<Longrightarrow> n = m"
proof (induct n arbitrary: m)
 case 0
  from 0 show ?case by (cases m, simp_all)
 next
 case (Suc n')
  from Suc show ?case by (cases m, simp_all) 
qed 

(* 
Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* WORKED IN CLASS *)
    Case "n = 0". simpl. intros m eq. destruct m as [| m'].
      SCase "m = 0". reflexivity.
      SCase "m = S m'". inversion eq. 
    Case "n = S n'". intros m eq. destruct m as [| m'].
      SCase "m = 0". inversion eq.
      SCase "m = S m'". 
        inversion eq.  rewrite (IHn' m' H0). reflexivity. 
Qed.

(* ###################################################### *)
(** ** Using tactics on hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  But most tactics have a variant that
    performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H. 
Qed.

(** Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].
 
    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].
 
    By contrast, [apply L] is "backward reasoning" -- it says that if
    we know [L1->L2] and we are trying to prove [L2], it suffices to
    prove [L1].  Here is a variant of a proof from above, using
    forward reasoning throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.
Qed.

(** In general, Coq tends to favor backward reasoning, but in
    some situations the forward style can be easier to think about. *)

(** **** Exercise: 2 stars *)
(** You can practice using the "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     plus n n = plus m m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
    (* SOLUTION: *)
    Case "n = 0". intros m. simpl. intros eq. destruct m as [| m'].
      SCase "m = 0". reflexivity.
      SCase "m = S m'". inversion eq. 
    Case "n = S n'". intros m eq. destruct m as [| m'].
      SCase "m = 0". inversion eq.
      SCase "m = S m'". 
        assert (n' = m') as H.
        SSCase "Proof of assertion". apply IHn'. 
          (* just [simpl in eq] doesn't work here *)
          rewrite <- plus_n_Sm in eq. rewrite <- plus_n_Sm in eq.   
          inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.
(** [] *)
*)

(* TODO:  Do a proof in Isar mode to illustrate forward reasoning *)

(* 
(* ###################################################### *)
(** ** Using [destruct] on compound expressions *)

(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.
Qed.
*)

definition sillyfun :: "nat \<Rightarrow> bool" where
"sillyfun n \<equiv> (if n=3 then False else (if n=5 then False else False))"

lemma "sillyfun n = False"
apply (unfold sillyfun_def)
apply (cases "n=3")
apply simp
apply simp
done
(* CL: Okay, the above proof was actually a little silly.  The real way
   it would work in Isabelle is *)

lemma "sillyfun n = False"
by (simp add: sillyfun_def)

(*
(** **** Exercise: 1 star *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* SOLUTION: *)
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true".
    reflexivity.
  Case "beq_nat k1 k2 = false".
    reflexivity.
Qed.
(** [] *)
*)

theorem "\<forall> l1 l2. split l = (l1, l2) \<longrightarrow> combine l1 l2 = l"
apply (induct l)
apply simp
apply (case_tac "split l")
apply auto
done
(*
lemma "split l = (l1, l2) \<Longrightarrow> combine l1 l2 = l"
proof (induct l arbitrary: l1 l2)
 case Nil
  from Nil show ?case by simp
 next
 case (Cons a l')
  from Cons show ?case apply (cases "split l'", auto)
*)

lemma split_aux : "\<lbrakk>split l = (l1, l2); split (a # l) = (l3, l4)\<rbrakk> \<Longrightarrow> l3 = (fst a # l1) \<and> l4 = (snd a # l2)"
apply (cases a)
apply (induct l)
by simp_all

lemma combine_aux [simp] : "combine l1 l2 = l \<Longrightarrow> combine ((fst a) # l1) ((snd a) # l2) = a # l"
apply (cases a)
apply (induct l)
by simp_all

theorem "\<forall> l1 l2. split l = (l1, l2) \<longrightarrow> combine l1 l2 = l"
apply (intro allI impI)
apply (induct l)
apply simp
apply (case_tac "split l")
by auto

(* Okay, now we'll do an automated version but with the use of an important argument to the induct tactic
   called arbitrary.  *)

theorem "split l = (l1,l2) \<Longrightarrow> combine l1 l2 = l"
apply (induct l arbitrary: l1 l2)
apply simp
apply (case_tac "split l")
by auto

(* CL: So in order to do this proof without using auto we need a couple of cute tools that we haven't
       introduced yet.  First, is "drule".  drule basically is the same as applying a rule to a hypothesis in Coq.
       It doesn't change the proof state, but it does change the hypothesis it is applied to; however,
       if we just apply drule split_aux, it actually will apply it to the wrong hypothesis!  Instead,
       we choose which hypothesis to apply it to via the numeric argument in parentheses.  Indexing starts from 0,
       so the (1) means "apply it to the second possible match" *)

theorem "split l = (l1,l2) \<Longrightarrow> combine l1 l2 = l"
apply (induct l arbitrary: l1 l2)
apply simp
apply (case_tac "split l")
apply simp
apply (drule (1) split_aux)
apply simp
done

(* 
(** **** Exercise: 2 stars *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  (* SOLUTION: *)
  Case "l = []".
    intros l1 l2 H.
    inversion H.
    reflexivity.
  Case "l = (x, y) :: l'".
    intros l1 l2 H.
    simpl in H.
    destruct (split l') as [lx ly].
    SCase "split l' = (lx,ly)".
      inversion H.
      simpl.
      rewrite -> IHl'.
        reflexivity.
        reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional *)
(** Thought exercise: We have just proven that for all lists of pairs,
    [combine] is the inverse of [split].  How would you state the
    theorem showing that [split] is the inverse of [combine]?
 
    Hint: what property do you need of [l1] and [l2] for [split]
    [combine l1 l2 = (l1,l2)] to be true?

    State this theorem in Coq, and prove it. (Be sure to leave your
    induction hypothesis general by not doing [intros] on more things
    than necessary.) *)
(* SOLUTION: *)
(** Here are two different approaches. *)
*)
theorem "\<forall> l2. length l1 = length l2 \<longrightarrow> split (combine l1 l2) = (l1,l2)"
apply (induct l1)
apply simp
apply (intro allI impI)
apply (case_tac l2)
apply auto
done

(* CL:  Again, don't want to use auto here!  I might need to switch to Isar
        in order to make a more step-wise proof *)

(* 
Theorem split_combine : forall (X Y:Type) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y. induction l1 as [| x l1'].
  Case "l1 = []".
    intros l2 Heq. destruct l2 as [|y l2'].
    SCase "l2 = []". reflexivity.
    SCase "l2 = y :: l2'". inversion Heq.
  Case "l1 = x :: l1'".
    intros l2 Heq. destruct l2 as [|y l2'].
    SCase "l2 = []". inversion Heq.
    SCase "l2 = y :: l2'". 
      simpl. rewrite IHl1'. reflexivity.
      inversion Heq. reflexivity.
Qed.

Theorem split_combine2 : forall (X Y:Type) l (l1 : list X) (l2 : list Y),
  (l1, l2) = split l -> split (combine l1 l2) = (l1, l2).
Proof.
  induction l as [| [x y] l'].
  Case "l = []". intros l1 l2 Heq.
    simpl in Heq. inversion Heq. reflexivity.
  Case "l = (x,y) :: l'". intros l1 l2 Heq.
    simpl in Heq. destruct (split l') as [l1' l2'].
    inversion Heq. simpl. rewrite IHl'. 
    reflexivity. reflexivity.
Qed.
(** [] *)

(* ###################################################### *)
(** ** The [case_eq] tactic *)


(** We have seen how the [destruct] tactic can be used to
    perform case analysis of the results of arbitrary computations.
    If [e] is an expression whose type is some inductively defined
    type [T], then, for each constructor [c] of [T], [destruct e]
    generates a subgoal in which all occurrences of [e] (in the goal
    and in the context) are replaced by [c].

    Sometimes, however, this substitution process loses information
    that we need in order to complete the proof.  For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Admitted.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep at
    least one of these because we need to be able to reason that
    since, in this branch of the case analysis, [beq_nat n 3 = true],
    it must be that [n = 3], from which it follows that [n] is odd.

    Fortunately, Coq has a tactic [case_eq] that acts like [destruct] 
    but also generates an equality between the original form of th term and
    outcomes of the case analysis. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  case_eq (beq_nat n 3). 
  (* At this point, we get two alternatives, just as for [destruct], but
     each has the form of an implication, with an equality hypothesis 
     that can be introduced and used... *)
    Case "beq_nat n 3 = true".  intros Heq3.  
        symmetry in Heq3. apply beq_nat_eq in Heq3. rewrite -> Heq3. reflexivity. 
    Case "beq_nat n 3 = false". intros Heq3.
      (* When we come to the second equality test in the
         body of the function we are reasoning about, we can
         use [case_eq] again in the same way, allowing us
         to finish the proof. *)
      case_eq (beq_nat n 5).       
        SCase "beq_nat n 5 = true".
            intros Heq5.  symmetry in Heq5. apply beq_nat_eq in Heq5.
            rewrite -> Heq5. reflexivity. 
        SCase "beq_nat n 5 = false". 
            intros Heq5.  rewrite Heq3 in eq.  rewrite Heq5 in eq.  inversion eq. 
Qed.

(** **** Exercise: 2 stars *)
(* You can prove this _without_ unfolding the definition of override
   by making use of some previous lemmas.  *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* SOLUTION: *)
  intros X x1 k1 k2 f. intros Hx1.
  case_eq (beq_nat k1 k2). 
  Case "beq_nat k1 k2 = true".
    intro Heq.
    apply beq_nat_eq' in Heq.
    rewrite <- Heq. 
    rewrite Hx1. 
    apply override_eq. 
  Case "beq_nat k1 k2 = false".
    intro Heq. 
    apply override_neq. 
    reflexivity.
    apply Heq. 
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** This one is a bit challenging.  Be sure your initial [intros] go
    only up through the parameter on which you want to do
    induction! *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                               (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* SOLUTION: *)
  intros X test x l. induction l as [| v' l'].
    Case "l = []". intros lf eq. inversion eq.
    Case "l = v' :: l'". intros lf eq.
      simpl in eq.
      case_eq (test v'). 
        SCase "test v' = true". 
          intro E. rewrite E in eq. inversion eq. rewrite <- H0. 
          rewrite <- E. reflexivity.
        SCase "test v' = false". 
          intro E.  rewrite E in eq. 
          apply IHl' with lf. apply eq.
Qed.
(** [] *)

(* ###################################################### *)
(** ** The [apply ... with ...] tactic *)

(** The following (silly) example uses two rewrites
    in a row to get from [ [m,n] ] to [ [r,s] ]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.
Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [ [nat] ], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2. 
Qed.

(**  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: apply trans_eq with [c,d]. *)

(** **** Exercise: 2 stars (apply_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (plus n p) = m ->
     (plus n p) = (minustwo o). 
Proof.
  (* SOLUTION: *)
  intros n m o p eq1 eq2. 
  apply trans_eq with m. apply eq2. apply eq1. 
Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  (* SOLUTION: *)
  intros n m p. intros Hnm Hmp.
  apply beq_nat_eq in Hnm.
  rewrite -> Hnm.
  rewrite -> Hmp.
  reflexivity.
Qed.

(* This proof is a bit more challenging if you do it without unfolding the definition of override,
   and instead use previously-proved lemmas about it.  *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* SOLUTION: *)
  intros X x1 x2 k1 k2 k3 f. intros Hneq.
  unfold override.
  case_eq (beq_nat k1 k3). 
     Case "beq_nat k1 k3 = true".
       intro eq13. apply beq_nat_eq' in eq13. rewrite <- eq13. 
       case_eq (beq_nat k2 k1). 
        SCase "beq_nat k2 k1 = true". 
          intro eq21.  apply beq_nat_eq' in eq21.  rewrite <- eq21 in Hneq. rewrite <- beq_nat_refl in Hneq.  inversion Hneq.
        SCase "beq_nat k2 k1 = false".
          reflexivity. 
     Case "beq_nat k1 k3 = false". 
       reflexivity. 
Qed.
(** [] *)

(* ###################################################### *)
(** ** Additional exercises *)

(** **** Exercise: 3 stars *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternate definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* SOLUTION: *)
Proof.
  induction l as [| x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'". 
    unfold fold_length. 
    unfold fold_length in IHl'.
    simpl. rewrite IHl'.
    reflexivity.
Qed.

(** [map] can also be defined in terms of [fold].  Define [fold_map]
    below. *)
Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* SOLUTION: *)
  fold (fun x l' => f x :: l') l nil.

(** Write down a theorem in Coq stating that [fold_map] is correct,
    and prove it. *)
(* SOLUTION: *)
Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  induction l as [| x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'".
    unfold fold_map in *.
    simpl. rewrite IHl'.
    reflexivity.
Qed.
(** [] *)

Module MumbleBaz.
(** **** Exercise: 2 stars, optional *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble]? 
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c] 
(* SOLUTION: *)
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true] 
      - [e mumble (b c 0)]
[] *)

(** **** Exercise: 2 stars, optional *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have? 
(* SOLUTION: *)
None!
[] *)

End MumbleBaz.

(** **** Exercise: 3 stars (forall_exists_challenge) *)
(** Challenge problem: Define two recursive [Fixpoints],
    [forallb] and [existsb].  The first checks whether every
    element in a list satisfies a given predicate:
[[
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true
  
      forallb evenb [0,2,4,5] = false
  
      forallb (beq_nat 5) [] = true
]]
    [existsb] checks whether there exists an element in the
    list that satisfies a given predicate:
[[
      existsb (beq_nat 5) [0,2,3,6] = false
 
      existsb (andb true) [true,true,false] = true
 
      existsb oddb [1,0,0,0,0,3] = true
 
      existsb evenb [] = false
]]
    Next, create a _nonrecursive_ [Definition], [existsb'], using
    [forallb] and [negb].
 
    Prove that [existsb'] and [existsb] have the same behavior.
*)

(* SOLUTION: *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Example test_forallb_1 : forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity.  Qed.

Example test_forallb_2 : forallb negb [false,false] = true.
Proof. reflexivity.  Qed.

Example test_forallb_3 : forallb evenb [0,2,4,5] = false.
Proof. reflexivity.  Qed.

Example test_forallb_4 : forallb (beq_nat 5) [] = true.
Proof. reflexivity.  Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => false
    | x :: l' => orb (test x) (existsb test l')
  end.

Example test_existsb_1 : existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity.  Qed.

Example test_existsb_2 : existsb (andb true) [true,true,false] = true.
Proof. reflexivity.  Qed.

Example test_existsb_3 : existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity.  Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity.  Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros. induction l as [| x l'].
  Case "l = []".
    unfold existsb'. simpl. reflexivity.
  Case "l = x :: l'".
    unfold existsb'. simpl.
    destruct (test x).
    SCase "test x = true".
      simpl. reflexivity.
    SCase "test x = false".
      simpl.
      rewrite -> IHl'.
      unfold existsb'. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Recall the definition of the [index] function:
[[
   Fixpoint index (X : Set) (n : nat) (l : list X) {struct l} : option X :=
     match l with
     | [] => None 
     | a :: l' => if beq_nat n O then Some a else index _ (pred n) l'
     end.
]]
   Write an informal proof of the following theorem:
[[
   forall X n l, length l = n -> index X (S n) l = None.
]]
(* SOLUTION: *)
   Let a set [X] and a list [l] be given.  We will show, by induction on [l],
   that [length l = n] implies [index X (S n) l = None], for any natural number
   [n]. There are two cases to consider:
     - If [l = nil], we must show [index (S n) [] = None].  This follows
       immediately from the definition of [index].

     - Otherwise, [l = cons x :: l'] for some [x] and [l'], and the
       induction hypothesis tells us that [length l' = n' => index (S
       n') l = None] for any [n'].

       Let [n] be a number such that [length l = n].  We must show
       that [index (S n) (x :: l') = None].  By the definition of
       [index], it is enough to show [index n l' = None].

       But we know that [n = length l = length (x :: l') = S (length l')].
       So it's enough to show [index (S (length l')) l' = None], which
       follows directly from the induction hypothesis, picking [length l']
       for [n'].
*)
(** [] *)

*)

end