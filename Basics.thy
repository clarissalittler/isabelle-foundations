theory Basics 
imports Main begin

(*
(** * Basics: Functional programming and reasoning about programs *)
(* Version of 4/7/2010 *)

(* ###################################################################### *)
(** * Enumerated Types *)

(** In Coq's programming language, almost nothing is built
    in -- not even booleans or numbers!  Instead, it provides powerful
    tools for defining new types of data and functions that process
    and transform them. *)

(* ###################################################################### *)
(** ** Days of the week *)

(** Let's start with a very simple example.  The following
    definition tells Coq that we are defining a new set of data
    values -- a "type."  The type is called [day] and its members are
    [monday], [tuesday], etc.  The lines of the definition can be read
    "[monday] is a [day], [tuesday] is a [day], etc." *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.
*)

datatype day = Monday | Tuesday | Wednesday 
             | Thursday | Friday | Saturday | Sunday

(*
(** Having defined this type, we can write functions that operate
    on its members. *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
*)
(* CL: One could define things this way, but it's easier to do
definition next_weekday :: "day \<Rightarrow> day" where
"next_weekday d \<equiv> (case d of
                    Monday \<Rightarrow> Tuesday |
                    Tuesday \<Rightarrow> Wednesday |
                    Wednesday \<Rightarrow> Thursday |
                    Thursday \<Rightarrow> Friday |
                    Friday \<Rightarrow> Monday |
                    Saturday \<Rightarrow> Monday |
                    Sunday \<Rightarrow> Monday)"
*)

primrec next_weekday :: "day \<Rightarrow> day" where
"next_weekday Monday = Tuesday"|
"next_weekday Tuesday = Wednesday" |
"next_weekday Wednesday = Thursday" |
"next_weekday Thursday = Friday" |
"next_weekday Friday = Monday" |
"next_weekday Saturday = Monday" |
"next_weekday Sunday = Monday"


(* 
(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often work out these types even if
    they are not given explicitly -- i.e., it performs some _type
    inference_ -- but we'll always include them to make reading
    easier. *)

(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  First, we can use the command [Eval simpl] to evaluate a
    compound expression involving [next_weekday].  Uncomment the
    following and see what they do. *)

(* Eval simpl in (next_weekday friday). *)
(* Eval simpl in (next_weekday (next_weekday saturday)). *)

(** If you have a computer handy, now would be an excellent
    moment to fire up the Coq interpreter under your favorite IDE --
    either CoqIde or Proof General -- and try this for yourself.  Load
    this file ([Basics.v]) from the book's accompanying Coq sources,
    find the above example, send it to Coq, and observe the
    result. *)

(** The keyword [simpl] (for "simplify") tells Coq precisely how
    to evaluate the expression we give it.  For the moment, [simpl] is
    the only one we'll need; later on we'll see some alternatives that
    are sometimes useful. *)
(** Second, we can record what we _expect_ the result to be in
    the form of a Coq [Example]: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
*)


lemma "next_weekday (next_weekday Saturday) = Tuesday"
by simp

(* CL: we could also prove this with Isar syntax via *)

lemma "next_weekday (next_weekday Saturday) = Tuesday"
proof (simp)
qed

lemma "next_weekday (next_weekday Saturday) = Tuesday"
proof -
show ?thesis by simp
qed

(* CL:  simp and simpl aren't exactly the same thing, but where you'd use
        simpl in Coq you probably want simp in Isabelle.  Essentially,
        simp does a lot more than simpl and can be given sets of rules to
        use when rewriting.  We demonstrate this here by using the
        'add' clause and passing it the 'next_weekday_def'.  
        One thing that's a little different between Coq & Isabelle is that
        definitions are never unfolded unless the rules of the definition
        are declared simp rules *)


(*
(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later. *)
(** Having made the assertion, we can also ask Coq to verify it,
    like this: *)

Proof. simpl. reflexivity.  Qed.


(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality are the same after simplification." *)

(** Third, we can ask Coq to "extract," from a [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to construct _fully certified_ programs in mainstream
    languages.  Indeed, this is one of the main uses for which Coq was
    developed.  We won't have space to dig further into this topic,
    but more information can be found in the Coq'Art book by Bertot
    and Castéran, as well as the Coq reference manual. *)

(* ###################################################################### *)
(** ** Booleans *)

(** In a similar way, we can define the type [bool] of booleans,
    with constants [true] and [false]. *)

Inductive bool : Type :=
  | true : bool
  | false : bool.
*)

(* CL:  In this conversion, I won't actually be using homegrown definitions of
   bool and nat.  Maybe I should, but I don't know if it really helps clarify
   things much.  *)

(* 
(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans in its standard
    library, together with a multitude of useful functions and
    lemmas.  (Take a look at [Coq.Init.Datatypes] in the Coq library
    documentation if you're interested.)  Whenever possible, we'll
    name our own definitions and theorems so that they exactly
    coincide with the ones in the standard library. *)

(** Functions over booleans can be defined in the same way as
    above: *)

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.
*)
(*
definition negb :: "bool \<Rightarrow> bool" where
"negb b \<equiv> (case b of
            True \<Rightarrow> False |
            False \<Rightarrow> True)"
*)
primrec negb :: "bool \<Rightarrow> bool" where
"negb True = False" |
"negb False = True"


(* 
Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.
*)

(*
definition andb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"andb b b' \<equiv> (case b of
               True \<Rightarrow> b' |
               False \<Rightarrow> False)" *)
primrec andb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"andb True b' = b'" |
"andb False b' = False"


(*
Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.
*)
(*
definition orb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"orb b b' \<equiv> (case b of
              True \<Rightarrow> True |
              False \<Rightarrow> b')" *)
primrec orb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"orb True b' = True" |
"orb False b' = b'"

(* CL:  All of the above is probably pretty straight forward, but
        what about these wacky 'declare' things below?
        Well, as I've stated above Isabelle is more conservative about
        unrolling definitions.  So in order to not have to worry about providing
        explicit definitions to simp, we can set these definitions to be
        part of the global simp set *)

(*

(** The last two illustrate the syntax for multi-argument
    function definitions. *)

(** The following four "unit tests" constitute a complete
    specification -- a truth table -- for the [orb] function: *)

Example test_orb1:  (orb true  false) = true. 
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true ) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true ) = true.
Proof. simpl. reflexivity.  Qed.
*)
lemma "orb True False = True"
by simp

lemma "orb False False = False"
by simp

(* CL:  examples of the above *)

(* 
(** _A note on notation_: We will often use square brackets
    to delimit fragments of Coq code in comments in .v files;
    this convention, which is also used by the coqdoc
    documentation tool, keeps them visually separate from the
    surrounding text.  In the html version of the files, these
    pieces of text appear in a different font, like [this]. *)

(** The following line of magic defines an [admit] value
  that can fill a hole in an incomplete  definition or proof.  
  We'll use it in the definition of [nandb] in the following 
  exercise.  In general, your job in the exercises is to 
  replace [admit] or [Admitted] with real definitions or proofs. *)
Definition admit {T: Type} : T.  Admitted.

(** **** Exercise: 1 star *)
(** Complete the definitions of the following functions, then make
    sure that the [Example] assertions below each can be verified by
    Coq.  *)

(** This function should return [true] if either or both of
    its inputs are [false]. *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  (* SOLUTION: *)
  match b1 with
  | true => negb b2
  | false => true
  end.
*)

definition nandb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"nandb b b' \<equiv> negb (andb b b')"
declare nandb_def [simp]

(* 
(** Remove "[Admitted.]" and fill in each proof with 
    "[Proof. simpl. reflexivity. Qed.]" *)

Example test_nandb1:               (nandb true false) = true.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_nandb2:               (nandb false false) = true.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_nandb3:               (nandb false true) = true.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_nandb4:               (nandb true true) = false.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
(** [] *)
*)

lemma "nandb False False = True" 
by simp

(* 

(** **** Exercise: 1 star *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* SOLUTION: *)
  andb b1 (andb b2 b3).
*)

definition andb3 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
"andb3 b1 b2 b3 \<equiv> andb b1 (andb b2 b3)"
declare andb3_def [simp]

(* 
Example test_andb31:                 (andb3 true true true) = true.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_andb32:                 (andb3 false true true) = false.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_andb33:                 (andb3 true false true) = false.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_andb34:                 (andb3 true true false) = false.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
(** [] *)
*)

lemma "andb3 True True True = True"
by simp

lemma "andb3 True True False = False"
by simp


(* 
(* ###################################################################### *)
(** ** Function Types *)

(** The [Check] command causes Coq to print the type of an
    expression.  For example, the type of [negb true] is [bool].
    (Remove the comments to try it yourself.) *)

Check (negb true).

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called function types, and
    they are written with arrows. *)

Check negb.
*)

(* CL:  There's two separate things that take the place of check, because 
        theorems and terms aren't on the same playing field.  *)

thm refl
term negb


(* 
(** The type of [negb], written [bool->bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool->bool->bool], can be
    read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)

(* ###################################################################### *)
(** ** Numbers *)

(** _Technical digression_: Coq provides a fairly fancy module system,
    to aid in organizing large developments.  In this course, we won't
    need most of its features, but one of them is useful: if we
    enclose a collection of declarations between [Module X] and [End
    X] markers, then, in the remainder of the file after the [End],
    all these definitions will be referred to by names like [X.foo]
    instead of just [foo].  This means that the new definition will
    not clash with the unqualified name [foo] later, which would
    otherwise be an error (a name can only be defined once in a given
    scope).
 
    Here, we use this feature to introduce the definition of the type
    [nat] in an inner module so that it does not shadow the one from
    the standard library. *)

Module Playground1.

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite collection
    of elements.  A more interesting way of defining a type is to give
    a collection of "inductive rules" describing its elements.  For
    example, we can define the natural numbers as follows: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** The clauses of this definition can be read: 
      - [O] is a natural number (note that this is the letter "[O]," not
        the numeral "[0]").
      - [S] is a "constructor" that takes a natural number and yields
        another one -- that is, if [n] is a natural number, then [S n]
        is too. *)
(** We can write simple functions that pattern match on natural
    numbers just as we did above -- for example, predecessor: *) 

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** The [n'] in the second branch of the match is different from
    the [n] received as input to [pred].  When that branch of the
    match is taken, we have [n = S n']. *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of special built-in magic for parsing and
    printing them: ordinary arabic numerals can be used as an
    alternative to the "unary" notation defined by the constructors
    [S] and [O].  Coq prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

(** The constructor [S] has the type [nat->nat], just like the
    functions [minustwo] and [pred]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference: functions
    like [pred] and [minustwo] come with _computation rules_
    -- e.g., the definition of [pred] says that [pred n] can be
    simplified to [match n with | O => O | S m' => m' end] -- while
    [S] has no such behavior attached.  Although it is a function in
    the sense that it can be applied to an argument, it does not _do_
    anything at all! *)

(** Every inductively defined set ([weekday], [nat], [bool], etc.) is
    actually a set of "expressions".  The definition of [nat] says how
    expressions in the set [nat] can be constructed:
      - the expression [O] belongs to the set [nat];
      - if [n] is an expression belonging to the set [nat], then [S n]
        is also an expression belonging to the set [nat]; and
      - expressions formed in these two ways are the only ones
        belonging to the set [nat].

    These three conditions are the precise force of the [Inductive]
    declaration.  They imply that 
      the expression [O],
      the expression [S O],
      the expression [S (S O)],
      the expression [S (S (S O))],
      and so on
    all belong to the set [nat], while other expressions like [true] and
    [S (S false)] do not. *)

(** For most function definitions over numbers, pure pattern
    matching is not enough: we also need recursion.  For example, to
    check that a number [n] is even, we may need to recursively check
    whether [n-2] is even.  To write such functions, we use the
    keyword [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.
*)

(* CL:  you might think that the following would work!
        it doesn't because primrec is more restrictive than Fixpoint
        in Coq, however we can do it with fun
primrec myeven :: "nat \<Rightarrow> bool" where
"myeven 0 = True" |
"myeven (Suc 0) = False" |
"myeven (Suc (Suc n)) = myeven n"
*)

fun myeven :: "nat \<Rightarrow> bool" where
"myeven 0 = True" |
"myeven (Suc 0) = False" |
"myeven (Suc (Suc n)) = myeven n"

(* CL:  OR!! *)

primrec myeven' :: "nat \<Rightarrow> bool" where
"myeven' 0 = True" |
"myeven' (Suc n) = negb (myeven n)"

(* 
(** When Coq checks this definition, it notes that [evenb] is
    "decreasing on 1st argument."  What this means is that we are
    performing a "structural recursion" over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [evenb] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is decreasing. *)

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition that will be easier to work with later: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity.  Qed.

(** Naturally, we can also define multi-argument functions by
    recursion.  *)

(* Once again, a module to avoid polluting the namespace. *)
Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
*)

primrec myplus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"myplus 0 m = m" |
"myplus (Suc n) m = Suc (myplus n m)"


(* 
(** Adding three to two now gives us five, as we'd expect. *)

(* Eval simpl in (plus (S (S (S O))) (S (S O))). *)

*)
(* CL:  rar! *)
lemma "myplus (Suc (Suc (Suc 0))) (Suc (Suc 0)) = (Suc (Suc (Suc (Suc (Suc 0)))))"
by simp

lemma "myplus 3 2 = 5"
by (simp add: eval_nat_numeral)

(* CL: nat_number is a convenient tool for converting back and forth between unary and decimal
       representations of numbers.  We can go ahead and add nat_number to the global simpset.
       As a warning, though, we may have to *remove it* at certain points to prevent infinite
       loops in the rewriter.  It's more powerful and more aggressive than the one in Coq. 

       In particular, it uses hypotheses for rewrite while Coq does not.  This tends to make Isabelle proofs
       more succinct, but occasionally requires a little care.
*)

(*

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)
(*     [plus (S (S (S O))) (S (S O))]    
   --> [S (plus (S (S O)) (S (S O)))]    by the second clause of the [match]
   --> [S (S (plus (S O) (S (S O))))]    by the second clause of the [match]
   --> [S (S (S (plus O (S (S O)))))]    by the second clause of the [match]
   --> [S (S (S (S (S O))))]             by the first clause of the [match]  *)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

(** You can match two expressions at once: *)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S n', O => S n'
  | S n', S m' => minus n' m'
  end.
*)

fun myminus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"myminus 0 _ = 0" |
"myminus (Suc n) 0 = Suc n" |
"myminus (Suc n) (Suc m) = myminus n m" 

(* CL:  We have to use fun instead of primrec because
        primrec is more restrictive than fixpoint! 
        We still have wildcards though.  *)

(* 
(** (The _ in the first line is a _wildcard pattern_.  Writing _ in a
    pattern is the same as writing some variable that doesn't get used
    on the right-hand side.  The _ avoids the need to make up a bogus
    name in this case. *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1:             (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 1 star *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat := 
  (* SOLUTION: *)
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
(** [] *)

(** We can make numerical expressions a little easier to read and
    write by introducing "notations" for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)  (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y)  (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y)  (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

(** Note that these do not change the definitions we've already
    made: they are simply instructions to the Coq parser to accept [x
    + y] in place of [plus x y] and, conversely, to the Coq
    pretty-printer to display [plus x y] as [x + y].

    Each notation-symbol in Coq, such as + - *, is active in a
    "notation scope".  Coq tries to guess what scope you mean, so when
    you write [S(O*O)] it guesses [nat_scope], but when you write the
    Cartesian-product (tupling) type [bool*bool] it guesses
    [type_scope].  Sometimes you have to help it out with
    percent-notation by writing [(x*y)%nat], and sometimes in Coq's
    feedback to you it will use [%nat] to indicate what scope a
    notation is in.

    Notation scopes also apply to numeral notation (3,4,5, etc.), so you
    may sometimes see [0%nat] which means [O], or [0%Z] which means the
    Integer zero.
*)

(** When we say that Coq comes with nothing built-in, we really
    mean it: even equality testing for numbers is a user-defined
    operation! *)

(** The [beq_nat] function tests [nat]ural numbers for [eq]uality,
    yielding a [b]oolean.  Note the use of nested [match]es (we could
    also have used a simultaneous match, as we did in [minus].)  *)
*)

(* CL: So, I'm not going to try defining an equality for naturals in Isabelle.
   All types have an inherent equality in Isabelle, and I feel that it's
   far more idiomatic to use that *)

(* 
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** Similarly, the [ble_nat] function tests [nat]ural numbers for
    [l]ess-or-[e]qual, yielding a [b]oolean. *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 1 star *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function.  *)
Definition blt_nat (n m : nat) : bool :=
  (* SOLUTION: *)
  (ble_nat (S n) m).

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* SOLUTION: *) Proof. simpl. reflexivity.  Qed. 
(** [] *)

(* ###################################################################### *)
(** * Proof By Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to the question of how to state and prove properties of their
    behavior.  Actually, in a sense, we've already started doing this:
    each [Example] in the previous sections makes a precise claim
    about the behavior of some function on some particular inputs.
    The proofs of these claims were always the same: use the
    function's definition to simplify the expressions on both sides of
    the [=] and notice that they become identical.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [plus] on the left can be proved
    just by observing that [plus 0 n] reduces to [n] no matter what
    [n] is, since the definition of [plus] is recursive in its first
    argument. *)

Theorem plus_O_n : forall n:nat, plus 0 n = n.
Proof.
  simpl. reflexivity.  Qed.
*)

(* CL:  So let's get into a few differences between Isabelle and Coq when
        it comes to real proofs.  First off, there's a difference between
        the quantifiers of the object logic (in this case HOL) and the
        meta logic of Isabelle.  
        For example, in the object logic of HOL the above theorem would
        look like *)

theorem "\<forall> n. myplus 0 n = n"
by (intro allI, simp)

theorem "\<forall> n. myplus 0 n = n"
by auto

(* CL:  We could, instead, use the forall of the metalogic *)

theorem "\<And>n. myplus 0 n = n"
by simp

(* CL:  In some ways, though, it's more idiomatic to use schematic variables*)

theorem "myplus 0 n = n"
by simp

theorem "\<forall> n. myplus 0 n = n"
proof (rule allI)
fix n
show "myplus 0 n = n" by simp
qed

(* A number of the subtleties related to the difference between schematic
   and metalogic bound variables are beyond me, I'll be honest.  I've noticed
   though that most theorems are described in terms of schematic variables
   as much as possible, unless it causes an induction principle to become
   too weak *)


(* 


(** The [reflexivity] command implicitly simplifies both sides of the
    equality before testing to see if they are the same, so we can
    shorten the proof a little. *)

Theorem plus_O_n' : forall n:nat, plus 0 n = n.
Proof.
  reflexivity.  Qed.
*)

(* CL:  The equivalent of this is the rule refl, but it doesn't simplifify
        first so you have to be more cautious in its use.  refl is called by
        simp, though, making Isabelle a slight oppositite of Coq. *)

theorem "n=n"
by (rule refl)

(* CL:  Now there's a cute trick in Isabelle/Proof General - type C-c C-f and you can search for theorems
        by the terms that appear in them.  Further, if you type C-c C-f intro you get a list of the introduction
        rules you could apply with a "rule" command.  This is pretty convenient for when you can't
        quite remember what the name of a theorem is.*)

(* 

(* 
(** The form of this theorem and proof are almost exactly the
    same as the examples above: the only differences are that we've
    added the quantifier [forall n:nat] and that we've used the
    keyword [Theorem] instead of [Example].  Indeed, the latter
    difference is purely a matter of style; the keywords [Example] and
    [Theorem] (and a few others, including [Lemma], [Fact], and
    [Remark]) mean exactly the same thing to Coq.

    The keywords [simpl] and [reflexivity] are examples of "tactics".
    A tactic is a command that is used between [Proof] and [Qed] to
    tell Coq how it should check the correctness of some claim we are
    making.  We will see several more tactics in the rest of this
    lecture, and yet more in future lectures. *)

(** **** Exercise: 1 star, optional *)
(** What will Coq print in response to this query? *)
(* Eval simpl in (forall n:nat, plus n 0 = n). *)

(** What about this one? *)
(* Eval simpl in (forall n:nat, plus 0 n = n). *)

(** Explain the difference.  [] *)

(* ###################################################################### *)
(** * The [intros] tactic *)

(** Aside from unit tests, which apply functions to particular
    arguments, most of the properties we will be interested in proving
    about programs will begin with some quantifiers (e.g., "for all
    numbers [n], ...") and/or hypothesis ("assuming [m=n], ...").  In
    such situations, we will need to be able to reason by _assuming
    the hypothesis_ -- i.e., we start by saying "OK, suppose [n] is
    some arbitrary number," or "OK, suppose [m=n]."

    The [intros] tactic permits us to do this by moving one or more
    quantifiers or hypotheses from the goal to a "context" of current
    assumptions.

    For example, here is a slightly different proof of the same theorem. *)
*)

(* CL:
   There isn't anything quite like the intros tactic in Isabelle; however,
   the introduction rule of the object-level forall is allI which can be
   applied as many times as needed by the command (intro allI)
   this is probably the closest thing to 'intros' there is in Isabelle.

*)

(* 
Theorem plus_O_n'' : forall n:nat, plus 0 n = n.
Proof.
  intros n. reflexivity.  Qed.
*)

*)

lemma "\<forall> n. myplus 0 n = n"
apply (rule allI)
apply simp
done

lemma "\<forall> n. myplus 0 n = n"
by (intro allI, simp)

lemma "\<forall> n. myplus 0 n = n"
by (auto)
(* auto can handle some pretty simple intro rules *)

(* 

(* 
(** Step through this proof in Coq and notice how the goal and
    context change. *)

Theorem plus_1_l : forall n:nat, plus 1 n = S n. 
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, mult 0 n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** (The [_l] suffix in the names of these theorems is
    pronounced "on the left.") *)

(* ###################################################################### *)
(** * Proof by rewriting *)

(** Here is a slightly more interesting theorem: *)

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  plus n n = plus m m.

(** Instead of making a completely universal claim about all numbers
    [n] and [m], this theorem talks about a more specialized property
    that only holds when [n = m].  The arrow symbol is pronounced
    "implies".

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite -> H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.
*)
*)

(* CL:  There's two points I'd like to make here.  First, that in general
        we'd do this with simp and be down with it!  As so *)

lemma "n=m \<Longrightarrow> myplus n n = myplus m m"
by simp

lemma assumes eq:"n=m"
      shows "myplus n n = myplus m m"
proof -
from eq show ?thesis by simp
qed

(* CL:  However, we could do this more explicitly via subst*)

lemma "n=m \<Longrightarrow> myplus n n = myplus m m"
by (erule ssubst, rule refl)

(* 
(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([plus n n = plus
    m m]) by replacing the left side of the equality hypothesis [H]
    with the right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes in Coq's behavior.) *)

(** **** Exercise: 1 star *)
(** Remove [Admitted.] and fill in the proof. *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> plus n m = plus m o.
Proof.
  (* SOLUTION: *)
  intros m n o.
  intros EQmn.
  intros EQno.
  rewrite -> EQmn.
  rewrite -> EQno.
  reflexivity.  Qed.
(** [] *)

(** The [Admitted] command tells Coq that we want to give up
    trying to prove this theorem and just accept it as a given.  This
    can be useful for developing longer proofs, since we can state
    subsidiary facts that we believe will be useful for making some
    larger argument, use [Admitted] to accept them on faith for the
    moment, and continue thinking about the larger argument until we
    are sure it makes sense; then we can go back and fill in the
    proofs we skipped.  Be careful, though: every time you say [admit]
    or [Admitted] you are leaving a door open for total nonsense to
    enter Coq's nice, rigorous, formally checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. *)

Theorem mult_0_plus : forall n m : nat,
  mult (plus 0 n) m = mult n m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 1 star *)
Theorem mult_1_plus : forall n m : nat,
  mult (plus 1 n) m = plus m (mult n m).
Proof.
  (* SOLUTION: *)
  intros n m.
  rewrite -> plus_1_l.
  reflexivity.  Qed.
(** [] *)

(* ###################################################################### *)
(** * Case analysis *) 

(** Of course, not everything can be proved by simple
    calculation: In general, unknown, hypothetical values (arbitrary
    numbers, booleans, lists, etc.) can show up in the "head position"
    of functions that we want to reason about, blocking
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck. *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (plus n 1) 0 = false.
Proof.
  intros n. simpl.  (* does nothing! *)
Admitted.

(** The reason for this is that the definitions of both
    [beq_nat] and [plus] begin by performing a [match] on their first
    argument.  But here, the first argument to [plus] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [plus n 1]; neither can be simplified.

    What we need is to be able to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (plus n 1) 0] and check that it is, indeed, [false].
    And if [n = S n'] for some [n'], then, although we don't know
    exactly what number [plus n 1] yields, we can calculate that, at
    least, it will begin with one [S], and this is enough to calculate
    that, again, [beq_nat (plus n 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (plus n 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.
*)

(* CL:  In Isabelle, cases is the tactic to use if you are dealing with a schematic variable! *)

lemma "(myplus n 1 = 0) = False" 
apply (cases n)
by (simp_all)

lemma "(myplus n 1 = 0) = False"
by (cases n, auto)

(* CL: cases is the equivalent of destruct *)

(* CL: what about a variable that is universally quantified in the meta-logic?  For that, 
       we need to use case_tac *)

lemma "\<And> n. (myplus n 1 = 0) = False"
apply (case_tac n)
by simp_all
(* CL: really, if you are using *_tac then there's something wrong - 
don't use the meta-forall if you can help it *)

(*
(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem as
    proved.  (No special command is needed for moving from one subgoal
    to the other.  When the first subgoal has been proved, it just
    disappears and we are left with the other "in focus.")  In this
    case, each of the subgoals is easily proved by a single use of
    [reflexivity].

    The annotation "[as [| n']]" is called an "intro pattern".  It
    tells Coq what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list_ of
    lists of names, separated by [|].  Here, the first component is
    empty, since the [O] constructor is nullary (it doesn't carry any
    data).  The second component gives a single name, [n'], since [S]
    is a unary constructor.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it here to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.
*)

lemma "negb (negb b) = b"
by (cases b, simp_all)

lemma "negb (negb b) = b"
proof (cases b) 
  case True
   from True(1) show ?thesis by simp
next
  case False
   from False(1) show ?thesis by simp
qed

(* CL:  Okay, so here's our first Isar proof! It's a little
   verbose in comparison to the typical automation but perhaps a bit cleaner.
   
   First off, we enter Isar mode with "proof" and end it
   with "qed"  We can declare that we start with an 
   initial tactic to set up the proof, in this case
   "cases".  That was a dumb sentence.
   We choose a case to examine with the keyword 'case'
   and move onto a new subgoal with the keyword 'next'
   After the "show" we can use apply scripts again, but
   in this case I just used by simp
*)

(*
(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written "[as[|]]".)  In fact, we can omit the [as] clause from
    _any_ [destruct] and Coq will fill in variable names
    automatically.  Although this is convenient, it is arguably bad
    style, since Coq often makes confusing choices of names when left
    to its own devices. *)

(** **** Exercise: 1 star *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (plus n 1) = false.
Proof.
  (* SOLUTION: *)
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.
(** [] *)

(* ###################################################################### *)
(** * Naming cases *)

(** The fact that there is no explicit command for moving from
    one branch of a case analysis to the next can make proof scripts
    rather hard to read.  In larger proofs, with nested case analyses,
    it can even become hard to stay oriented when you're sitting with
    Coq and stepping through the proof.  (Imagine trying to remember
    that the first five subgoals belong to the inner case analysis and
    the remaining seven are the cases are what remains of the outer
    one...)  Disciplined use of indentation and comments can help, but
    a better way is to use the [Case] tactic.

    [Case] is not built into Coq: we need to define it ourselves.
    There is no need to understand how it works -- just skip over the
    definition to the example that follows.  (It uses some facilities
    of Coq that we have not discussed -- the string library (just for
    the concrete syntax of quoted strings) and the [Ltac] command,
    which allows us to declare custom tactics.  Kudos to Aaron
    Bohannon for this nice hack!) *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.
*)

(* CL:  Okay, so we can do some of this stuff with Isar but in general Ltac doesn't have an equivalent in Isabelle *)

(* 
Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.

(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.
*)

(* CL:  We'll do this one Isar style! *)

theorem assumes H:"andb b c = True"
        shows "b = True"
proof (cases b)
 case True
   from True(1) show "b = True" by simp
next
 case False
   from False(1) have L1: "andb b c = False" by simp
   show "b = True" 
     using H L1 by simp
qed

(* 
(** [Case] does something very trivial: It simply adds a string
    that we choose (tagged with the identifier "Case") to the context
    for the current goal.  When subgoals are generated, this string is
    carried over into their contexts.  When the last of these subgoals
    is finally proved and the next top-level goal (a sibling of the
    current one) becomes active, this string will no longer appear in
    the context and we will be able to see that the case where we
    introduced it is complete.  Also, as a sanity check, if we try to
    execute a new [Case] tactic while the string left by the previous
    one is still in the context, we get a nice clear error message.

    For nested case analyses (i.e., when we want to use a [destruct]
    to solve a goal that has itself been generated by a [destruct]),
    there is an [SCase] ("subcase") tactic. *)

(** **** Exercise: 2 stars *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* SOLUTION: *)
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      reflexivity.  Qed.
(** [] *)

(** There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit [Case] tactics placed at
    the beginning of lines, then the proof will be readable almost no
    matter what choices are made about other aspects of layout.

    This is a good place to mention one other piece of (possibly
    obvious) advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or entire proofs on one line.  Good style lies somewhere in the
    middle.  In particular, one convention (not just for Coq proofs,
    but arguably for all programming!)  is to limit yourself to 80
    character lines.  Lines longer than this are hard to read and can
    be inconvenient to display and print.  Many editors have features
    that help enforce this. *)


(* ###################################################################### *)
(** * Induction *)

(** We proved above that [0] is a neutral element for [plus] on
    the left using a simple partial evaluation argument.  The fact
    that it is also a neutral element on the _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  plus n 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [plus n 0] is an arbitrary
  unknown number, so the [match] in the definition of [plus] can't be
  simplified.  And reasoning by cases using [destruct n] doesn't get
  us much further: the branch of the case analysis where we assume [n
  = 0] goes through, but in the branch where [n = S n'] for some [n']
  we get stuck in exactly the same way.  We could use [destruct n'] to
  get one step further, but since [n] can be arbitrarily large, if we
  continue this way we'll never be done. *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Admitted.

(** Case analysis gets us a little further, but not all the way: *)

Theorem plus_0_r_secondtry : forall n:nat,
  plus n 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
Admitted.

(** To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.

    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that P holds for ALL numbers [n], we can
    reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].
    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)

Theorem plus_0_r : forall n:nat, plus n 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.
*)

lemma myplus_n_0 :"myplus n 0 = n"
apply (induct n)
by (simp_all)

(* CL:  induction in Isabelle is with the induct rule *)

lemma "myplus n 0 = n"
proof (induct n)
case (Suc i)
 from Suc show ?case by simp
qed simp

(* CL:  an Isar style proof where we only prove the interesting case in the Isar style and declare that the remaining 
goals should be solved by simp *)

(* CL:  Similar to cases, we use induct_tac when the variable is universally quantified - though we really shouldn't *)

lemma "\<And> n. myplus n 0 = n"
apply (induct_tac n)
by simp_all

(* 
(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [plus 0 0 = 0], which follows by simplification.
    In the second, [n] is replaced by [S n'] and the assumption [plus
    n' 0 = n'] is added to the context (with the name [IHn'], i.e.,
    the Induction Hypothesis for [n']).  The goal in this case becomes
    [plus (S n') 0 = S n'], which simplifies to [S (plus n' 0) = S
    n'], which in turn follows from the induction hypothesis. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 1 star (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  mult n 0 = 0.
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.
*)

(* 
Theorem plus_n_Sm : forall n m : nat, 
  S (plus n m) = plus n (S m).
Proof. 
  (* SOLUTION: *)
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_comm : forall n m : nat,
  plus n m = plus m n.
Proof.
  (* SOLUTION: *)
  intros n m. induction m as [| m'].
  Case "m = 0".
    simpl. rewrite -> plus_n_O. reflexivity.
  Case "m = S m'".
    simpl. rewrite <- IHm'. rewrite <- plus_n_Sm.
    reflexivity.  Qed.
(** [] *)
*)

(* By declaring this lemma with the [simp] attribute, the
   rewrite rule is added to the simp set *)

lemma [simp]:"myplus n (Suc m) = Suc (myplus n m)"
apply (induct n)
by simp_all

lemma "myplus n m = myplus m n"
apply (induct m)
by (simp_all add: myplus_n_0)

lemma "myplus n m = myplus m n"
proof (induct m)
case (Suc i)
 from Suc show ?case by simp
qed (simp add: myplus_n_0)
(*

(* ###################################################################### *)
(** * Formal vs. informal proof *)

(** The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millenia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or, sometimes, spoken)
    text that instills in the reader or hearer the certainty that [P]
    is true.  That is, a proof is an act of communication.

    Now, acts of communication may involve different sorts of readers.
    On one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipies are called "formal proof".

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily "informal".  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.

    Because we will be using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead, a
    mathematician would write it like this: *)
(** - _Theorem_: For any [n], [m] and [p],
[[
      plus n (plus m p) = plus (plus n m) p.
]]
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
[[
        plus 0 (plus m p) = plus (plus 0 m) p.  
]]
      This follows directly from the definition of [plus].

    - Next, suppose [n = S n'], with
[[
        plus n' (plus m p) = plus (plus n' m) p.
]]
      We must show
[[
        plus (S n') (plus m p) = plus (plus (S n') m) p.
]]
      By the definition of [plus], this follows from
[[
        S (plus n' (plus m p)) = S (plus (plus n' m) p),
]]
      which is immediate from the induction hypothesis. [] *)

(** The overall form of the proof is basically similar.  (This
    is no accident, of course: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.)
    But there are significant differences of detail: the formal proof
    is much more explicit in some ways (e.g., the use of
    [reflexivity]) but much less explicit in others; in particular,
    the "proof state" at any given point in the Coq proof is
    completely implicit, whereas the informal proof reminds the reader
    several times where things stand. *)

(** Here is a formal proof that shows the structure more
clearly: *)

Theorem plus_assoc : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercise: 2 stars, optional (plus_comm_informal) *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: plus is commutative.
 
    Proof: (* SOLUTION: *)
       Let natural numbers [n] and [m] be given.  We show [plus n m = plus m
       n] by induction on [m].
 
       - First, suppose [m = 0].  By the definition of [plus], we know
         [plus 0 n = 0].  We have already shown (lemma [plus_n_0])
         that [plus n 0 = 0].  Thus, [plus n 0 = plus 0 n].
 
       - Next, suppose [m = S m'] for some [m'], such that [plus n m'] =
         [plus m' n].  By the definition of [plus] and the inductive
         hypothesis, [plus (S m') n = S (plus m' n) = S (plus n m')].  It
         remains to show [plus n (S m') = S (plus n m')] as well, but this
         is precisely lemma [plus_n_Sm].
[]
*)

(** **** Exercise: 2 stars, optional (bet_nat_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* SOLUTION: *)
       By induction on [n].
 
       - First, suppose [n = 0].  We must show [true = beq_nat 0 0].  This
         follows directly from the definition of [beq_nat].
 
       - Next, suppose [n = S n'], with [true = beq_nat n' n'].  We
         must show [true = beq_nat (S n') (S n')] This follows
         directly from the induction hypothesis and the definition of
         [beq_nat].
[]
 *)

(** **** Exercise: 2 stars *)
Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(** [] *)

(* ###################################################################### *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are very
    often broken into a sequence of theorems, with later proofs
    referring to earlier theorems.  Occasionally, however, a proof
    will need some miscellaneous fact that is too trivial (and of too
    little general interest) to bother giving it its own top-level
    name.  In such cases, it is convenient to be able to simply state
    and prove the needed "sub-theorem" right at the point where it is
    used.  The [assert] tactic allows us to do this.  For example, our
    earlier proof of the [mult_0_plus] theorem referred to a previous
    theorem named [plus_O_n].  We can also use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  mult (plus 0 n) m = mult n m.
Proof.
  intros n m.
  assert (H: plus 0 n = n). 
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.
*)

(* 
(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (Note that we could also name the assertion with
    [as] just as we did above with [destruct] and [induction], i.e.,
    [assert (plus 0 n = n) as H].  Also note that we mark the proof of
    this assertion with a [Case], both for readability and so that,
    when using Coq interactively, we can see when we're finished
    proving the assertion by observing when the ["Proof of assertion"]
    string disappears from the context.)  The second goal is the same
    as the one at the point where we invoke [assert], except that, in
    the context, we have the assumption [H] that [plus 0 n = n].  That
    is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** Actually, [assert] will turn out to be handy in many sorts of
    situations.  For example, suppose we want to prove that [plus
    (plus n m) (plus p q) = plus (plus m n) (plus p q)]. The only
    difference between the two sides of the [=] is that the arguments
    [m] and [n] to the first inner [plus] are swapped, so it seems we
    should be able to use the commutativity of addition ([plus_comm])
    to rewrite one into the other.  However, the [rewrite] tactic is a
    little stupid about _where_ it applies the rewrite.  There are
    three uses of [plus] here, and it turns out that doing [rewrite ->
    plus_comm] will affect only the _outer_ one. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  plus (plus n m) (plus p q) = plus (plus m n) (plus p q).
Proof.
  intros n m p q.
  (* We just need to swap (plus n m) for (plus m n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> plus_comm. 
  (* Doesn't work...Coq rewrote the wrong plus! *)
Admitted.

(** To get [plus_comm] to apply at the point where we want it, we can
    introduce a local lemma stating that [plus n m = plus m n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [plus_comm], and then use this lemma to do the
    desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  plus (plus n m) (plus p q) = plus (plus m n) (plus p q).
Proof.
  intros n m p q.
  assert (H: plus n m = plus m n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** Exercise: 3 stars (mult_comm) *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)
Theorem plus_swap : forall n m p : nat, 
  plus n (plus m p) = plus m (plus n p).
Proof.
  (* SOLUTION: *)
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: plus n m = plus m n).
    Case "Proof of assertion".
    rewrite <- plus_comm. reflexivity.
  rewrite -> H. rewrite -> plus_assoc. reflexivity.  Qed.


Theorem mult_m_Sn : forall m n : nat,
 mult m (S n) = plus m (mult m n).
Proof.
  induction m as [| m'].
  Case "m = 0".
    intros n. simpl. reflexivity.
  Case "m = S m'".
    intros n.
    simpl.
    rewrite -> IHm'.
    rewrite -> plus_swap.
    reflexivity.  Qed.

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_comm : forall m n : nat,
 mult m n = mult n m.
Proof.
  (* SOLUTION: *)
  induction m as [| m'].
  Case "m = 0".
    intros n. simpl. rewrite mult_0_r. reflexivity.
  Case "m = S m'".
    intros n.
    simpl.
    rewrite -> mult_m_Sn.
    rewrite -> IHm'.
    reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* SOLUTION: *)
  intros n.
  induction n as [| n'].
  Case "n = 0".  simpl. reflexivity.
  Case "n = S n'". 
    assert (H: evenb (S (S n')) = evenb n').
      simpl.  reflexivity.
    rewrite -> H. rewrite -> IHn'.  
    rewrite negb_involutive.  reflexivity.  Qed.
(** [] *)

(* ###################################################################### *)
(** * Extra Exercises *)

(** **** Exercise: 3 stars (more_exercises) *)
(** Take a piece of paper.  For each of the following theorems, first THINK
    about whether (a) it can be proved using only simplification and
    rewriting, (b) it also requires case analysis ([destruct]), or (c) it
    also requires induction.  Write down your prediction.  Then fill in the
    proof.  (There is no need to turn in your piece of paper; this is just
    to encourage you to think before hacking!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* SOLUTION: *)
  reflexivity.  Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* SOLUTION: *)
  intros b. destruct b as [| n'].
    reflexivity.
    reflexivity.  Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (plus p n) (plus p m) = true.
Proof.
  (* SOLUTION: *)
  intros n m p. induction p as [| p'].
  Case "p = 0".
    intros H.
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    intros H.
    simpl. rewrite -> IHp'. reflexivity.
    rewrite -> H. reflexivity.  Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* SOLUTION: *)
  reflexivity.  Qed.

Theorem mult_1_l : forall n:nat, mult 1 n = n.
Proof.
  (* SOLUTION: *)
  intros n. simpl. rewrite -> plus_0_r.
  reflexivity.  Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* SOLUTION: *)
  intros b c. destruct b.
    destruct c.
      reflexivity.
      reflexivity.
    destruct c.
      reflexivity.
      reflexivity.  Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  mult (plus n m) p = plus (mult n p) (mult m p).
Proof.
  (* SOLUTION: *)
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'.
    rewrite -> plus_assoc.
    reflexivity.  Qed.

Theorem mult_assoc : forall n m p : nat,
  mult n (mult m p) = mult (mult n m) p.
Proof.
  (* SOLUTION: *)
  intros n m p.  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> mult_plus_distr_r.  rewrite IHn'.  reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** The [pattern] tactic allows you to pick out a particular subterm
    for rewriting. That is, [pattern p] followed by a [rewrite] will
    do rewriting only in the expression [p] (which can be anything at
    all).  Use the [pattern] tactic to do a proof of [plus_swap'],
    just like [plus_swap] but without needing [assert (plus n m = plus
    m n)]. *)

Theorem plus_swap' : forall n m p : nat, 
  plus n (plus m p) = plus m (plus n p).
Proof.
  (* SOLUTION: *)
  intros n m p.
  rewrite -> plus_assoc.
  pattern (plus n m). rewrite plus_swap.
  rewrite plus_assoc.
  reflexivity.  Qed.
(** [] *)


(** **** Exercise: 4 stars (binary) *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    First, write an inductive definition of the type [bin]
    corresponding to this description of binary numbers.

    Next, write an increment function for binary numbers, and a
    function to convert binary numbers to unary numbers.

    Finally, prove that your increment and binary-to-unary functions
    commute: that is, incrementing a binary number and then converting
    it to unary yields the same result as first converting it to unary
    and then incrementing.
*)

(* SOLUTION: *)
Inductive bin : Type :=
  | BZ : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.
*)

datatype bin = BZ | B0 bin | B1 bin

(* 
Fixpoint incr (m:bin) : bin :=
  match m with
  | BZ => B1 BZ
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.
*)

primrec incr :: "bin \<Rightarrow> bin" where
"incr BZ = B1 BZ" |
"incr (B0 m) = B1 m" |
"incr (B1 m) = B0 (incr m)"

(* 
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | BZ    => O
  | B0 m' => 2 * bin_to_nat m'
  | B1 m' => 1 + 2 * bin_to_nat m'
  end.
*)

primrec bin_to_nat :: "bin \<Rightarrow> nat" where
"bin_to_nat BZ = 0" |
"bin_to_nat (B0 m) = 2 * bin_to_nat m" |
"bin_to_nat (B1 m) = 1 + 2 * bin_to_nat m"

theorem "bin_to_nat (incr b) = 1 + bin_to_nat b"
apply (induct b)
by simp_all

end


(* 
Theorem bin_to_nat_pres_incr : forall b : bin, 
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [| b' | b'].
  Case "b = 0". 
    reflexivity. 
  Case "b = 2*b'".
    reflexivity.
  Case "b = 1 + 2*b'".
    simpl. rewrite -> IHb'. 
    simpl. rewrite <- plus_n_Sm.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (decreasing) *)
(** The requirement that some argument to each function be
    "decreasing" is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways.

    To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs but that Coq will _not_ accept
    because of this restriction. *)

(* SOLUTION: *)
(*
Fixpoint factorial_bad (n:nat) : nat := 
  match beq_nat n 0 with
  | true => 1
  | false => mult n (factorial_bad (n-1))
  end.
*)
*)
