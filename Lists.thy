theory Lists 
imports Main Basics begin

(* (** * Lists: Products, Lists and Options *)
(* Version of 4/7/2010 *)

Require Export Basics.

(** The preceding line imports all of our definitions from Basics.v.  For
    it to work, you need to compile Basics.v into Basics.vo.  (This is
    like making a .class file from a .java file, or a .o file from a
    .c file.)
  
    Here are two ways to compile your code:
  
     - CoqIDE
   
       1. Open Basics.v.
       2. In the "Compile" menu, click on "Compile Buffer".
   
     - Command line
   
       1. Run: coqc Basics.v

    In this file, we again use the [Module] feature to wrap all of the
    definitions for pairs and lists of numbers in a module so that,
    later, we can reuse the same names for improved (generic) versions
    of the same operations. *)

Module NatList.

(* ###################################################### *)
(** * Pairs of numbers *)

(** In an [Inductive] type definition, each constructor can take
    any number of parameters---none (as with [true] and [O]), one (as
    with [S]), or more than one, as in this definition: *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.
*)

datatype natprod = Pair nat nat

(*
(** This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor [pair] to
    two arguments of type [nat]."

    Here are some simple function definitions illustrating pattern
    matching on two-argument constructors: *)

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.
*)

definition fst :: "natprod \<Rightarrow> nat" where
"fst p \<equiv> (case p of
           Pair p1 p2 \<Rightarrow> p1)"

declare fst_def [simp]

definition snd :: "natprod \<Rightarrow> nat" where
"snd p \<equiv> (case p of
           Pair p1 p2 \<Rightarrow> p2)"

declare snd_def [simp]

(* 
(** Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation [(x,y)] instead
    of [pair x y].  We can instruct Coq to allow this with a
    [Notation] declaration. *)

Notation "( x , y )" := (pair x y).
*) 

(* CL:  If we wanted to add notation, we should have done it in the original
        declaration. *)

datatype natprod' = Pair' nat nat ("{{_,_}}")

term "{{1,2}}"

(* 

(** The new notation can be used both in expressions and in
    pattern matches (indeed, we've seen this already in the previous
    chapter -- the comma is provided as part of the standard
    library): *)

Eval simpl in (fst (3,4)).

Definition fst' (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.
*)

definition fst' :: "natprod' \<Rightarrow> nat" where
"fst' p \<equiv> (case p of
           {{x,y}} \<Rightarrow> x)"
declare fst'_def [simp]

definition snd' :: "natprod' \<Rightarrow> nat" where
"snd' p \<equiv> (case p of
           {{x,y}} \<Rightarrow> y)"

declare snd'_def [simp]
definition swap_pair' :: "natprod' \<Rightarrow> natprod'" where
"swap_pair' p \<equiv> (case p of
                 {{x,y}} \<Rightarrow> {{y,x}})"

declare swap_pair'_def [simp]

(* 
(** Let's try and prove a few simple facts about pairs.  If we
    state the lemmas in a particular (and slightly peculiar) way, we
    can prove them with just reflexivity (and evaluation): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.
*)

theorem "{{n,m}} = {{fst' {{n,m}}, snd' {{n,m}} }}"
by (simp)

(* CL:  Let's add an Isar style proof just for kicks! *)

theorem "{{n,m}} = {{fst' {{n,m}}, snd' {{n,m}} }}"
proof - 
  have L1: "fst' {{n,m}} = n" by simp
  have L2: "snd' {{n,m}} = m" by simp
  from L1 L2 show ?thesis by simp
qed

(* 
(** But reflexivity is not enough if we state the lemma in a more
    natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Admitted.
*)


theorem "p = {{fst' p, snd' p}}"
apply (cases p)
by simp

(* 
(** We have to expose the structure of [p] so that simple can
    perform the pattern match in [fst] and [snd].  We can do this with
    [destruct].

    Notice that, unlike for [nat]s, [destruct] doesn't generate an
    extra subgoal here.  That's because [natprod]s can only be
    constructed in one way.  *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as (n,m).  simpl.  reflexivity.  Qed.

(** Notice that Coq allows us to use the notation we introduced
    for pairs in the "as..." pattern telling it what variables to
    bind. *)

(** **** Exercise: 2 stars *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* SOLUTION: *)
  intros p.  destruct p as (n,m).  simpl.  reflexivity.  Qed.
(** [] *)
*)

theorem "{{snd' p, fst' p}} = (swap_pair' p)"
apply (cases p)
by simp

(* 
(** **** Exercise: 2 stars, optional *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* SOLUTION: *) 
  intros p. destruct p as (n,m).  simpl.  reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** * Lists of numbers *)

(** Generalizing the definition of pairs a little, we can
    describe the type of _lists_ of numbers like this: "A list is
    either the empty list or else a pair of a number and another
    list." *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
*)

datatype natlist = Nil ("[[]]") | NatCons nat natlist (infixr "&" 65)

(* CL:  For the rest of this file, we'll just be using the Isabelle built in lists and we'll actually make things polymorphic.  Maybe that's cheating, but I don't know if we particularly gain much by keeping things monomorphic!  *)

(* 
(** For example, here is a three-element list: *)

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

(** As with pairs, it is more convenient to write lists in
    familiar mathematical notation.  The following two declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** It is not necessary to fully understand these declarations,
    but in case you are interested, here is roughly what's going on.

    The [right associativity] annotation tells Coq how to parenthesize
    expressions involving several uses of [::] so that, for example,
    the next three declarations mean exactly the same thing: *)

Definition l_123'   := 1 :: (2 :: (3 :: nil)).
Definition l_123''  := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

(** The [at level 60] part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,
[[
Notation "x + y" := (plus x y)  
                    (at level 50, left associativity).
]]
   [+] will bind tighter than [::], so [1 + 2 :: [3]] will be
   parsed correctly as [(1 + 2) :: [3]] rather than [1 + (2 :: [3])].

   (By the way, it's worth noting in passing that expressions like "[1
   + 2 :: [3]]" can be a little confusing when you read them in a .v
   file.  The inner brackets, around 3, indicate a list, but the outer
   brackets are there to instruct the "coqdoc" tool that the bracketed
   part should be displayed as Coq code rather than running text.
   These brackets don't appear in the generated HTML.)

   The second and third [Notation] declarations above introduce the
   standard square-bracket notation for lists; the right-hand side of
   the third one illustrates Coq's syntax for declaring n-ary
   notations and translating them to nested sequences of binary
   constructors. *)

(** A number of functions are useful for manipulating lists.
    For example, the [repeat] function takes a number [n] and a
    [count] and returns a list of length [count] where every element
    is [n]. *)

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
*)

primrec repeat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"repeat 0 a = []" |
"repeat (Suc n) a = a # (repeat n a)"

(* 
(** The [length] function calculates the length of a list. *)

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
*)

primrec mylength :: "'a list \<Rightarrow> nat" where
"mylength [] = 0" |
"mylength (h # t) = Suc (length t)"

(*
(** The [app] ("append") function concatenates two lists. *)

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.
*)
primrec app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app [] l2 = l2" |
"app (h # t) l2 = h # (app t l2)"

(* 

(** In fact, [app] will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it. *)

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1:             [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4,5] = [4,5].
Proof. reflexivity.  Qed.
Example test_app3:             [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity.  Qed.

(** Here are two more small examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] ("tail") returns everything but tqhe first
    element.  Of course, the empty list has no first element, so we
    must make an arbitrary choice in that case.  *)

Definition hd (l:natlist) : nat :=
  match l with
  | nil => 0  (* arbitrary! *)
  | h :: t => h
  end.
*)

(* CL:  This is an interesting example in Isabelle because it demonstates a big difference
        between Isabelle and Coq.  In Coq, you must give a case for the nil list or the definition will
        be rejected.  In Isabelle, you don't.  Why?  Because Isabelle is, essentially, classical set theory.
        We have the axiom of choice at our disposal and this definition means that there is some arbitrary
        element of the set 'a that corresponds to the nil case.  We don't know what it is, so if we pass
        hd [] then we can't prove anything about this value.  It's essentially useless to us, but it does
        mean that a function that *looks* partial doesn't make the system logically unsound. 
        
        Another detail here is that all types must be non-empty sets.  If you define a new type by hand
        with typedef, which we probably won't need to do in this course, you have an obligation to prove
        there exists at least one element in that type.
*)

primrec myHd :: "'a list \<Rightarrow> 'a" where
"myHd (h # t) = h"

(* 
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.
*)

primrec myTl :: "'a list \<Rightarrow> 'a list" where
"myTl (h # t) = t"

(* 
Example test_hd:              hd [1,2,3] = 1.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1,2,3] = [2,3].
Proof. reflexivity.  Qed.

(** **** Exercise: 1 star (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below.  *)
Fixpoint nonzeros (l:natlist) : natlist :=
  (* SOLUTION: *)
  match l with
  | nil => nil 
  | h :: t =>
      match h with
      | O => nonzeros t
      | S h' => h :: (nonzeros t)
      end
  end.
*)

primrec nonzeros :: "nat list \<Rightarrow> nat list" where
"nonzeros [] = []" |
"nonzeros (h # t) = (if h=0 then nonzeros t else h # (nonzeros t))" 

(* CL:  Note that while this is a slightly more complicated recursion than what we've
        done before, it still fits the basic pattern of a primrec declaration since it only
        involves recursive calls made by removing one constructor from the same argument in each
        case.  *)

(* 
Example test_nonzeros:            nonzeros [0,1,0,2,3,0,0] = [1,2,3].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Fixpoint oddmembers (l:natlist) : natlist :=
  (* SOLUTION: *)
  match l with
  | nil => nil 
  | h :: t =>
      match (oddb h) with
      | true => h :: (oddmembers t)
      | false => oddmembers t
      end
  end.

Example test_oddmembers:            oddmembers [0,1,0,2,3,0,0] = [1,3].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Fixpoint countoddmembers (l:natlist) : nat :=
  (* SOLUTION: *)
  match l with
  | nil => O
  | h :: t =>
      match (oddb h) with
      | true => S (countoddmembers t)
      | false => (countoddmembers t)
      end
  end.

Example test_countoddmembers1:    countoddmembers [1,0,3,1,4,5] = 4.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_countoddmembers2:    countoddmembers [0,2,4] = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_countoddmembers3:    countoddmembers nil = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(** **** Exercise: 2 stars (alternate) *)
(** Complete the definition of alternate.

    One natural way of writing [alternate] will fail to satisfy Coq's
    requirement that all [Fixpoint] definitions be "obviously
    terminating."  If you find yourself in this rut, look for a
    slightly more verbose solution that considers elements of
    both lists at the same time. *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* SOLUTION: *)
  match l1,l2 with
  | nil,_ => l2
  | _,nil => l1
  | h1 :: t1, h2 :: t2  => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1:        alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_alternate2:        alternate [1] [4,5,6] = [1,4,5,6].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_alternate3:        alternate [1,2,3] [4] = [1,4,2,3].
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(* ###################################################### *)
(** ** Bags via lists *)

(** A [bag] (or [multiset]) is a set where each element can
    appear any finite number of times.  One reasonable implementation
    of bags is to represent a bag of numbers as a list. *)
Definition bag := natlist.  
*)

type_synonym bag = "nat list"

(* 
(** **** Exercise: 3 stars (bag_functions) *)
(** As an exercise, complete the following definitions for the
    functions [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat := 
  (* SOLUTION: *)
  match s with
  | nil => 0
  | h :: t => 
      match beq_nat h v with
      | false => count v t
      | true => S (count v t)
      end
  end.
*)

primrec count :: "nat \<Rightarrow> bag \<Rightarrow> nat" where
"count n [] = 0" |
"count n (h # t) = (if h=n then 1 else 0) + (count n t)"

(* 
(** All these proofs can be done just by [reflexivity]. *)
Example test_count1:              count 1 [1,2,3,1,4,1] = 3.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_count2:              count 6 [1,2,3,1,4,1] = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
*)
lemma "count 1 [1,2,3,1,4,1] = 3"
by simp

(*  
(** Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)
Definition sum : bag -> bag -> bag := 
  (* SOLUTION: *)
  app.

Example test_sum1:              count 1 (sum [1,2,3] [1,4,1]) = 3.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Definition add (v:nat) (s:bag) : bag := 
  (* SOLUTION: *)
  v :: s.

Example test_add1:                count 1 (add 1 [1,4,1]) = 3.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_add2:                count 5 (add 1 [1,4,1]) = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Definition member (v:nat) (s:bag) : bool := 
  (* SOLUTION: *)
  negb (beq_nat (count v s) 0).

Example test_member1:             member 1 [1,4,1] = true.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_member2:             member 2 [1,4,1] = false.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(** **** Exercise: 3 stars, optional (bag_more_functions) *)
(** Here are some extra (optional) bag functions for you to practice
    with. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
 (* Note that when remove_one is applied (nonsensically) to the empty
    bag, it's OK to return the empty bag. *)
  (* SOLUTION: *)
  match s with
  | nil => nil
  | h :: t => 
      match beq_nat h v with
      | true => t
      | false => h :: (remove_one v t)
      end
  end.

Example test_remove_one1:         count 5 (remove_one 5 [2,1,5,4,1]) = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_remove_one2:         count 5 (remove_one 5 [2,1,4,1]) = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_remove_one3:         count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_remove_one4: 
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* SOLUTION: *)
  match s with
  | nil => nil
  | h :: t => 
      match beq_nat h v with
      | true => remove_all v t
      | false => h :: (remove_all v t)
      end
  end.

Example test_remove_all1:          count 5 (remove_all 5 [2,1,5,4,1]) = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_remove_all2:          count 5 (remove_all 5 [2,1,4,1]) = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_remove_all3:          count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_remove_all4:          count 5 (remove_all 5 [2,1,5,4,5,1,4]) = 0.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* SOLUTION: *)
  match s1 with 
  | nil => true
  | h1 :: t1 => 
      andb (member h1 s2)
               (subset t1 (remove_one h1 s2))
  end.

Example test_subset1:              subset [1,2] [2,1,4,1] = true.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_subset2:              subset [1,2,2] [2,1,4,1] = false.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(** **** Exercise: 3 stars (bag_theorem) *)
(** Write down an interesting theorem about bags involving the
    functions [count] and [add], and prove it.  Note that since this
    problem is somewhat open-ended, it's possible that you may come up
    with a theorem which is true, but whose proof requires techniques
    you haven't learned yet.  Feel free to ask for help if you get
    stuck!  *)
(* SOLUTION: *)
(** Here is one possible solution: *)
Theorem bag_add_one_count : forall s:bag, forall v:nat,
  count v (add v s) = 1 + count v s.
Proof.
  intros s v. simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.  


(* ###################################################### *)
(** * Reasoning about lists *)

(** Just as with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification. For
    example, simplification is enough for this theorem... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
   reflexivity.  Qed.

(** ... because the [[]] is substituted into the match position
    in the definition of [app], allowing the match itself to be
    simplified. *)

(** Also like numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'". 
    reflexivity.  Qed.

(** Here, the [nil] case works because we've chosen [tl nil =
    nil]. Notice that the [as] annotation on the [destruct] tactic
    here introduces two names, [n] and [l'], corresponding to the fact
    that the [cons] constructor for lists takes two arguments (the
    head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
    induction for their proofs. *)

(* ###################################################### *)
(** ** Induction on lists *)

(** Proofs by induction over data types like [natlist] are
    perhaps a little less familiar than standard natural number
    induction, but the basic idea is equally simple.  Each [Inductive]
    declaration defines a set of data values that can be built up from
    the declared constructors: a number can be either [O] or [S]
    applied to a number; a boolean can be either [true] or [false]; a
    list can be either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], asssuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    stopping eventually with [nil], these two things together
    establish the truth of [P] for all lists [l]. *)

Theorem ass_app : forall l1 l2 l3 : natlist, 
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.
*)

theorem "l1 @ (l2 @ l3) = (l1 @ l2) @ l3"
apply (induct l1)
by simp_all
  

(* 
(** Again, this Coq proof is not especially illuminating as a
    static written document -- it is easy to see what's going on if
    you are reading the proof in an interactive Coq session and you
    can see the current goal and context at each point, but this state
    is not visible in the written-down parts of the Coq proof.  A
    natural-language proof needs to include more explicit signposts --
    in particular, it helps the reader a lot to be reminded exactly
    what the induction hypothesis is in the second case. *)

(** Theorem: For all [l1], [l2], and [l3], 
   [l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3].

   Proof: By induction on [l1].

   - First, suppose [l1 = []].  We must show:
[[
       [] ++ (l2 ++ l3) = ([] ++ l2) ++ l3
]]
     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with
[[
       l1' ++ l2 ++ l3 = (l1' ++ l2) ++ l3
]]
     (the induction hypothesis). We must show
[[
       (n :: l1') ++ l2 ++ l3 = ((n :: l1') ++ l2) ++ l3
]]  
     By the definition of [++], this follows from
[[
       n :: (l1' ++ l2 ++ l3) = n :: ((l1' ++ l2) ++ l3)
]]
     which is immediate from the induction hypothesis.  []

  An exercise to be worked together: *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = plus (length l1) (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.
*)
theorem "length (l1 @ l2) = (length l1) + (length l2)"
by (induct l1, simp_all)

(* 
(** For a slightly more involved example of an inductive proof
    over lists, suppose we define a "cons on the right" function
    [snoc] like this... *)

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.
*)
primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (h # t) a = h # (snoc t a)"


(* 
(** ... and use it to define a list-reversing function [rev]
    like this: *)

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.
*)

primrec rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (h # t) = snoc (rev t) h"

(* 

Example test_rev1:            rev [1,2,3] = [3,2,1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** Now we prove some more list theorems using our newly defined
    snoc and rev.  Let's try something a little more intricate:
    proving that reversing a list does not change its length.  Our
    first attempt at this proof gets stuck in the successor case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. (* Here we get stuck: the goal is an equality involving
              [snoc], but we don't have any equations in either the
              immediate context or the global environment that have
              anything to do with [snoc]! *)
Admitted.
*)
(* CL: Just like in Coq, we need an auxilary lemma about
       snoc in order to make this theorem work!
theorem "length l = length (rev l)"
apply (induct l)
apply (simp_all)
*)

lemma [simp]: "length (snoc l n) = Suc (length l)"
by (induct l, simp_all)

theorem "length l = length (rev l)"
by (induct l, simp_all)

(* Also, much like Coq we could have had made a local theorem.  subgoal_tac adds
   the theorem to be proved at the end of the list of goals, though, rather than make it
   the current goal *)

theorem "length l = length (rev l)"
apply (subgoal_tac "\<forall>l n. length (snoc l n) = Suc (length l)")
apply (induct l)
apply simp
apply simp
apply (intro allI)
apply simp
done

theorem "length l = length (rev l)"
proof (induct l)
  case Nil
   show "length [] = length (rev [])" by simp
  case (Cons a l)
   from Cons(1) show "length (a # l) = length (rev (a # l))" by simp
qed

(* 

(** So let's take the equation about snoc that would have
    enabled us to make progress and prove it as a separate lemma. *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed. 

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc. 
    rewrite -> IHl'. reflexivity.  Qed.

(** Let's take a look at informal proofs of these two theorems: 

    - _Theorem_: For all numbers [n] and lists [l],
         [length (snoc l n) = S (length l)].
 
      _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show
[[
          length (snoc [] n) = S (length []),
]]
        which follows directly from the definitions of
        [length] and [snoc].

      - Next, suppose [l = n'::l'], with
[[
          length (snoc l' n) = S (length l').
]]
        We must show
[[
          length (snoc (n' :: l') n) = S (length (n' :: l'))
]]
        By the definitions of [length] and [snoc], this
        follows from
[[
          S (length (snoc l' n)) = S (S (length l')),
]] 
        which is immediate from the induction hypothesis. []
                          
    - _Theorem_: For all lists [l], [length (rev l) = length l]
    
      _Proof_: By induction on [l].  

        - First, suppose [l = []].  We must show
[[
            length (rev []) = length []
]]
          which follows directly from the definitions of [length] 
          and [rev].
    
        - Next, suppose [l = n::l'], with
[[
            length (rev l') = length l'
]]
          We must show
[[
            length (rev (n :: l')) = length (n :: l').
]]
          By the definition of [rev], this follows from
[[
            length (snoc (rev l') n) = S (length l')
]]
          which, by the previous lemma, is the same as
[[
            S (length (rev l')) = S (length l').
]]
          This is immediate from the induction hypothesis. [] *)

(** Obviously, the style of these proofs is rather longwinded
    and pedantic.  After we've seen a few of them, we might begin to
    find it easier to follow proofs that give a little less detail
    overall (since we can easily work them out in our own minds or on
    scratch paper if necessary) and just highlight the non-obvious
    steps.  In this more compressed style, the above proof might look
    more like this: *)

(** _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that
[[
       length (snoc l n) = S (length l)
]]
     for any [l].  This follows by a straightforward induction on [l].

     The main property now follows by another straightforward
     induction on [l], using the observation together with the
     induction hypothesis in the case where [l = n'::l']. [] *)

(** Which style is preferable in a given situation depends on
    the sophistication of the expected audience and on how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is usually a safe
    fallback. *)

(* ###################################################### *)
(** *** List exercises, Part 1 *)

(** **** Exercise: 2 stars (list_exercises) *)
(** More practice with lists *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  (* SOLUTION: *)
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity.  Qed.


Theorem rev_snoc : forall n : nat, forall l : natlist,
  rev (snoc l n) = n :: (rev l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* SOLUTION: *)
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc. rewrite -> IHl'. reflexivity.  Qed.
*)

lemma [simp]: "rev (snoc l n) = n # (rev l)"
by (induct l, simp_all)

theorem "rev (rev l) = l"
by (induct l, simp_all)

(* 

Theorem snoc_with_append : forall l1 l2 : natlist,
                         forall n : nat,
  snoc (l1 ++ l2) n = l1 ++ (snoc l2 n).
Proof.
  intros l1 l2 n. induction l1 as [| n' l1'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* SOLUTION: *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l = nil".
    simpl. rewrite -> app_nil_end. reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl1'. rewrite -> snoc_with_append. reflexivity.  Qed.
*)

(* CL: All the others basically follow the same format! *)

(* 
(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way... *)
Theorem ass_app4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* SOLUTION: *)
  intros l1 l2 l3 l4. 
  rewrite -> ass_app. rewrite -> ass_app.
  reflexivity.  Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* SOLUTION: *)
  intros l n. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite <- IHl'. reflexivity.  Qed.

(** An exercise about your implementation of [nonzeros]. *)
Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* SOLUTION: *)
  intros l1 l2.  induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. destruct n as [| n'].
    SCase "n = 0".
      rewrite -> IHl1'. reflexivity.
    SCase "n = S n'".
      rewrite -> IHl1'. reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** *** List exercises, part 2 *)

(** **** Exercise: 2 stars (list_design) *)
(** Design exercise: 
     - Write down a non-trivial theorem involving [cons]
       ([::]), [snoc], and [append] ([++]).  
     - Prove it.
*) 
(* SOLUTION: *)
(** Here's one possibility: *)
Theorem append_snoc : forall l1 l2 : natlist, forall n : nat,
  ((snoc l1 n) ++ l2) = l1 ++ (n :: l2).
Proof.
  intros l1 l2 n. induction l1 as [| n' l1'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.
(** [] *)
*)
theorem "(snoc l1 n) @ l2 = l1 @ (n # l2)"
by (induct l1, simp_all)

(* 
(** **** Exercise: 2 stars, optional (bag_proofs) *)
(** If you did the optional exercise about bags above, here are a
    couple of little theorems to prove about your definitions. *)
Theorem count_member_nonzero : forall (s : bag),
  ble_nat 0 (count 1 (1 :: s)) = true.
Proof.
  (* SOLUTION: *)
  intros s.  reflexivity.  Qed.

(** The following lemma about ble_nat might help you below. *)
Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".  
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* SOLUTION: *)
  intros s.  induction s as [| n s'].  
  Case "s = nil".
    simpl.  reflexivity.  
  Case "s = cons".
    simpl. destruct n as [| n'].  
    SCase "0".
      simpl.  rewrite ble_n_Sn. reflexivity.
    SCase "S n'".
      simpl. rewrite IHs'. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (bag_count_sum) *)  
(** Write down an interesting theorem about bags involving the
    functions [count] and [sum], and prove it. *)
(* SOLUTION: *)
(** Here is one possible solution: *)
Theorem count_sums : forall (s1 s2:bag), forall v:nat,
  count v (sum s1 s2) = count v s1 + count v s2.
Proof.
  intros s1 s2 v.
  induction s1 as [|v' s1'].
  Case "s1 = nil".
    reflexivity.
  Case "s1 = v' :: s1'".
    simpl. destruct (beq_nat v' v).
    SCase "v' = v".
      rewrite IHs1'. simpl. 
      reflexivity.
    SCase "v' <> v".
      apply IHs1'.
Qed.

(* ###################################################### *)
(** * Options *)

(** Here is another type definition that is often useful in
    day-to-day programming: *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  
*)

(* CL:  Isabelle has an option type as well!  It also has constructors Some and None 
   I'm not going to do the rest of the exercises and instead just move on to Poly.thy! 
   See you there!
*)

(* 
(** One use of [natoption] is as a way of returning "error
    codes" from functions.  For example, suppose we want to write a
    function that returns the [n]th element of some list.  If we give
    it type [nat -> natlist -> nat], then we'll have to return some
    number when the list is too short! *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with 
               | true => a 
               | false => index_bad (pred n) l' 
               end
  end.

(** On the other hand, if we give it type [nat -> natlist ->
    natoption], then we can return [None] when the list is too short
    and [Some a] when the list has enough members and [a] appears at
    position [n]. *)

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4,5,6,7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4,5,6,7] = None.
Proof. reflexivity.  Qed.

(** This example is also an opportunity to introduce one more
    small feature of Coq's programming language: conditional
    expressions. *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

(** Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the boolean type
    is not built in, Coq actually allows conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)
(** This function pulls the nat out of a [natoption], returning
   a supplied default in the [None] case. *)

Definition option_elim (o : natoption) (d : nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: 2 stars *)
(** Using the same idea, fix the hd function from earlier so we don't
   have to return an arbitrary element in the [nil] case.  *)
Definition hd_opt (l : natlist) : natoption :=
  (* SOLUTION: *)
  match l with
  | nil    => None
  | n :: l => Some n
  end.

Example test_hd_opt1 : hd_opt [] = None.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Example test_hd_opt3 : hd_opt [5,6] = Some 5.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 (** [] *)

(** **** Exercise: 2 stars *)
(** This exercise relates your new [hd_opt] to the old [hd]. *)
Theorem option_elim_hd : forall l:natlist,
  hd l = option_elim (hd_opt l) 0.
Proof.
  (* SOLUTION: *)
  intros l. destruct l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars (beq_natlist) *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)
Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* SOLUTION: *)
  match l1,l2 with 
  | nil,nil => true
  | h1::t1,h2::t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
  | _,_ => false
  end.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_beq_natlist2 :   beq_natlist [1,2,3] [1,2,3] = true.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 Example test_beq_natlist3 :   beq_natlist [1,2,3] [1,2,4] = false.
 (* SOLUTION: *)
Proof. reflexivity.  Qed.
 
Theorem beq_natlist_refl : forall l:natlist,
  beq_natlist l l = true.
Proof.
  (* SOLUTION: *)
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl.  rewrite <- beq_nat_refl.  rewrite -> IHl'.
    reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** * The [apply] tactic *)

(** We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with [rewrite ->
     eq2. reflexivity.] as we have done several times above.  But we
     can achieve the same effect in a single step by using the [apply]
     tactic instead: *)
  apply eq2.  Qed.
*)

(* CL:  A lot of the business with the apply tactic is
        covered by creating local theorems in Isar mode.
        When in apply script mode, you don't actually have
        that fine level of control *)

(* 
(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some "universal variables."  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars *)
(** Complete the following proof without using [simpl]. *)
Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* SOLUTION: *)
  intros H1 H2.
  apply H1. apply H2.  Qed.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal EXACTLY -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* here we cannot use [apply] directly *)
Admitted.

(** In this case we can use the [symmetry] tactic, which
    switches the left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.             (* Actually, this line is unnecessary, since *)
  apply H.           (* [apply] will do a [simpl] step first. *)  Qed.

(** **** Exercise: 3 stars (apply_exercises) *)
Theorem rev_exercise1 : forall (l l' : natlist),
     l = rev l' ->
     l' = rev l.
Proof.
  (* Hint: you can use [apply] with previously defined lemmas, not
     just hypotheses in the context. *)
  (* SOLUTION: *)
  intros l l' eq. rewrite -> eq. 
  symmetry.
  apply rev_involutive.   Qed.

(** The next exercise is a little tricky.  The first line of the proof
    is provided, because it uses an idea we haven't seen before.
    Notice that we don't introduce m before performing induction.
    This leaves it general, so that the IH doesn't specify a
    particular m, but lets us pick.  We'll talk more about this below,
    and later in the course in more depth.  *)

Theorem beq_nat_sym : forall (n m : nat), forall (b : bool),
  beq_nat n m = b -> beq_nat m n = b.
Proof.
  intros n. induction n as [| n'].
  (* SOLUTION: *)
  Case "n = 0".
    intros m b E. destruct m as [| m'].
    SCase "m = 0". rewrite -> E. reflexivity. 
    SCase "m = S m'". rewrite <- E. reflexivity. 
  Case "n = S n'".
    intros m b E. destruct m as [| m'].
    SCase "m = 0". rewrite <- E. reflexivity.
    SCase "m = S m'". rewrite <- E. simpl. apply IHn'. 
                      reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars (beq_nat_sym_informal) *)
(** Provide an informal proof of this lemma:

   Theorem: For any [nat]s [n] [m] and [bool] [b], if
   [beq_nat n m = b] then [beq_nat m n = b].

   Proof:
   (* SOLUTION: *)
   Let an arbitrary nat [n] be given.  We go by induction
   on [n].

   - For the base case, we have n = 0.  Let [m] and [b] be
     given and assume [beq_nat 0 m = b].  Either [m = 0]
     or not.

     - In the first case, we must show [beq_nat 0 0 = b]
       which is exactly the assumption.

     - In the second case, [m = S m'] for some [m'].  By
       our assumption, it's enough to show [beq_nat (S m')
       0 = beq_nat 0 (S m')], and by the definition of
       [beq_nat] both are [false].

   - In the inductive case, we have [n = S n'] for some
     [n'] such that, for any [m] and [b],
[[
       beq_nat n' m = b -> beq_nat m n = b
]]
     Let [m] and [b] be given and assume [beq_nat (S n') m
     = b].  We go by cases on [m].
  
     - Suppose first [m = 0].  By the assumption, it's
       enough to show [beq_nat 0 (S n') = beq_nat (S n')
       0].  By the definition of [beq_nat], both sides are
       [false].
   
     - Otherwise, [m = S m'] for some [m'].  By the
       assumption, it's enough to show:
[[
         beq_nat (S m') (S n') = beq_nat (S n') (S m')
]]
       And, by the definition of [beq_nat], this reduces to
       showing:
[[
         beq_nat m' n' = beq_nat n' m'.
]]
       Picking [m = m'] and [b = beq_nat n' m'] in the 
       inductive hypothesis gives:
[[
         beq_nat n' m' = beq_nat n' m -> 
         beq_nat m' n' = beq_nat n' m'.
]] 
       The premise is trivial, and the conclusion is exactly
       what we wanted to show.
   []
 *)
(** [] *)

(** **** Exercise: 1 star (apply_rewrite) *)
(** Briefly explain the difference between the tactics
    [apply] and [rewrite].  Are there situations where
    either one can be applied? 

  (* SOLUTION: *)
    The [rewrite] tactic is used to apply a known equality to either
    the goal or a hypothesis in the context, replacing all occurrences
    of one side by the other.  The [apply] tactic uses a known
    implication (a hypothesis from the context, a previously proved
    lemma, or a constructor) to modify the proof state either
    backward (if the goal matches the conclusion of the implication,
    in which case a subgoal is generated for each premise of the
    implication) or forward (if some hypothesis matches the premise of
    the implication, in which case this hypothesis is replaced by the
    conclusion of the implication).  If the fact is itself an
    equality (i.e., an implication with no premises), then either
    tactic can be used.
*)
(** [] *)

(* ###################################################### *)
(** * Varying the Induction Hypothesis *)

(** One subtlety in these inductive proofs is worth noticing here.
    For example, look back at the proof of the [ass_app] theorem.  The
    induction hypothesis (in the second subgoal generated by the
    [induction] tactic) is

      [ l1' ++ l2 ++ l3 = (l1' ++ l2) ++ l3 ].

    (Note that, because we've defined [++] to be right associative,
    the expression on the left of the [=] is the same as writing [l1'
    ++ (l2 ++ l3)].)

    This hypothesis makes a statement about [l1'] together with the
    _particular_ lists [l2] and [l3].  The lists [l2] and [l3], which
    were introduced into the context by the [intros] at the top of the
    proof, are "held constant" in the induction hypothesis.  If we set
    up the proof slightly differently by introducing just [n] into the
    context at the top, then we get an induction hypothesis that makes
    a stronger claim:

     [ forall l2 l3, l1' ++ l2 ++ l3 = (l1' ++ l2) ++ l3 ]

    (Use Coq to see the difference for yourself.)

    In the present case, the difference between the two proofs is
    minor, since the definition of the [++] function just examines its
    first argument and doesn't do anything interesting with its second
    argument.  But we'll soon come to situations where setting up the
    induction hypothesis one way or the other can make the difference
    between a proof working and failing. *)

(** **** Exercise: 2 stars *)
(** Give an alternate proof of the associativity of [++] with a more
    general induction hypothesis.  Complete the following (leaving the
    first line unchanged). *)
Theorem ass_app' : forall l1 l2 l3 : natlist, 
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.   
Proof.
  intros l1. induction l1 as [ | n l1'].
  (* SOLUTION: *)
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    intros l2 l3.
    assert (l1' ++ l2 ++ l3 = (l1' ++ l2) ++ l3) as H.
      SCase "Proof of assertion". apply IHl1'.
    simpl. rewrite -> H. reflexivity.  Qed.
(** [] *)

End NatList.
*)

(* 
(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 1 star (destruct_induction) *)
(** Briefly explain the difference between the tactics
    [destruct] and [induction].  

(* SOLUTION: *)
   Both are used to perform case analysis on an element of an
   inductively defined type; [induction] also generates an induction
   hypothesis, while [destruct] does not.

*)
(** [] *)

(** The following declaration puts [beq_nat_sym] into the
    top-level namespace, so that we can use it later without having to
    write [NatList.beq_nat_sym]. *)
Definition beq_nat_sym := NatList.beq_nat_sym.
*)

hide_const (open) fst snd

end