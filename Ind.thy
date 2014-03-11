theory Ind
imports Main Basics begin

(* There's some definite differences here between inductive predicates
   in Isabelle and inductive predicates in Coq.  Inductive predicates in
   Isabelle are basically the same as sets: 'a set \<equiv> ('a \<Rightarrow> bool)
*) 

(* 

(* Version of 4/7/2010 *)

Require Export Poly.

Review
We've now seen a bunch of Coq's fundamental tactics -- enough, in fact, to do pretty much everything we'll want for a while. We'll introduce one or two more as we go along through the next few lectures, and later in the course we'll introduce some more powerful automation tactics that make Coq do more of the low-level work in many cases. But basically we've got what we need to get work done.
Here are the ones we've seen:
intros: move hypotheses/variables from goal to context
reflexivity: finish the proof (when the goal looks like e = e)
apply: prove goal using a hypothesis, lemma, or constructor
apply... in H: apply a hypothesis, lemma, or constructor to a hypothesis in the context (forward reasoning)
apply... with...: explicitly specify values for variables that cannot be determined by pattern matching
simpl: simplify computations in the goal
simpl in H: ... or a hypothesis
rewrite: use an equality hypothesis (or lemma) to rewrite the goal
rewrite ... in H: ... or a hypothesis
unfold: replace a defined constant by its right-hand side in the goal
unfold... in H: ... or a hypothesis
destruct... as...: case analysis on values of inductively defined types
induction... with...: induction on values of inductively defined types
inversion: reason by injectivity and distinctness of constructors
case_eq (e): case analysis that introduces equalities so that we can destruct e without "losing" its definition
assert (e) as H: introduce a "local lemma" e and call it H
Programming with Propositions
A proposition is a statement expressing a factual claim, like "two plus two equals four." In Coq, propositions are written as expressions of type Prop. Although we haven't mentioned it explicitly, we have already seen numerous examples.

Check (plus 2 2 = 4).
(* 2 + 2 = 4%nat : Prop *)
*)

term "n=0 \<Longrightarrow> n + n = 2*n"
(* CL: In Isabelle, we prove things that have type prop but I believe there
   is a natural injection of type bool into prop which allows us to prove things of
   type bool just as well as prop.  Essentially, prop involves use of the constructors
   of the metalogic while bool only involves constructors from HOL *)
term "n=0 \<longrightarrow> n + n = 2*n"

(* CL: otice the difference in types between the two statements:  again, I believe this 
is because of the difference between meta-implication \<Longrightarrow> and HOL implication \<longrightarrow> *) 

(*
Check (ble_nat 3 2 = false).
(* ble_nat 3 2 = false : Prop *)

Both provable and unprovable claims are perfectly good propositions. Simply being a proposition is one thing; being provable is something else!

Check (plus 2 2 = 4).
Check (plus 2 2 = 5).
(* 2 + 2 = 5%nat : Prop *)

Both plus 2 2 = 4 and plus 2 2 = 5 are legal expressions of type Prop.
We've seen one way that propositions can be used in Coq: in Theorem (and Lemma and Example) declarations.

Theorem plus_2_2_is_4 : 
  plus 2 2 = 4.
Proof. reflexivity. Qed.

But they can be used in many other ways. For example, we can give a name to a proposition using a Definition, just as we have given names to expressions of other sorts (numbers, functions, types, type functions, ...).

Definition plus_fact : Prop := plus 2 2 = 4.
Check plus_fact.

Now we can use this name in any situation where a proposition is expected -- for example, as the subject of a theorem.

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity. Qed.
*)

definition plus_fact :: "bool" where
"plus_fact \<equiv> (2::nat) + 2 = 4"

theorem plus_fact : "plus_fact" 
by (simp add: plus_fact_def)
(* need to unroll the definition of plus_fact *)


(*
So far, all the propositions we have seen are equality propositions. But can also form new propositions out of old ones. For example, given propositions P and Q, we can form the proposition "P implies Q."

Definition strange_prop1 :=
  (plus 2 2 = 5) -> (plus 99 26 = 42).
*)

definition strange_prop :: "bool" where
"strange_prop \<equiv> (((2::nat) + 2 = 5) \<longrightarrow> ((99::nat) + 26 = 42))"

theorem "strange_prop"
by (simp add: strange_prop_def)

(*
Also, given a proposition P with a free variable n, we can form the proposition forall n, P.

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

We can also define parameterized propositions. For example, what does it mean to claim that "a number n is even"? We have written a function that tests evenness, so one possible definition of what it means to be even is "n is even iff evenb n = true."

Definition even (n:nat) := 
  evenb n = true.
*)

(* CL: Now, the above definition is essentially redundant in Isabelle because the "bool" is used for propositions.  *)

(*
This defines even as a function that, when applied to a number n, yields a proposition asserting that n is even.

Check even.
Check (even 4).

The type of even, nat->Prop, can be pronounced in three ways: (1) "even is a function from numbers to propositions," (2) "even is a family of propositions, indexed by a number n," or (3) "even is a property of numbers."
Propositions -- including parameterized propositions -- are first-class citizens in Coq. We can use them in other definitions:

Definition even_n__even_SSn (n:nat) := (even n) -> (even (S (S n))).

We can define them to take multiple arguments...

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

... and then partially apply them:

Definition teen : nat->Prop := between 13 19.

We can even pass propositions -- including parameterized propositions -- as arguments to functions:

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.
*)

definition true_for_zero :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
"true_for_zero P \<equiv> P 0"

declare true_for_zero_def [simp]

(*
Definition true_for_n__true_for_Sn (P:nat->Prop) (n:nat) : Prop :=
  P n -> P (S n).

(Names like x__y can be read "x implies y.")

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat->Prop) : Prop :=
     (true_for_zero P) ->
     (preserved_by_S P) ->
     (true_for_all_numbers P).

Evidence
We've seen that well-formed expressions of type Prop can embody both provable and unprovable propositions. Naturally, though, we're particularly interested in the provable ones! When P is a proposition and e is a proof of P -- i.e., e is evidence that P is true -- we'll write "e : P." This overloading of the "has type" or "inhabits" notation is not accidental: indeed, we'll see that there is a fundamental and fruitful analogy between data values inhabiting types and evidence "inhabiting" propositions.
The next question is "what are proofs?" -- i.e., what sorts of things we would be willing to accept as evidence that particular propositions are true.
Inductively Defined Propositions
One way to answer this question is to define a new proposition together with a statement of what counts as evidence for its truth. For example, recalling the type day from Basics.v, we might introduce a parameterized proposition good_day : day -> Prop like this:

Inductive good_day : day -> Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.
*)

(* CL: Now, I'm adding the 'intro' attribute to these rules so that they'll
   automatically be used by auto as an introduction rule. I've found that
   this is generally a pretty good practice. *)

inductive good_day :: "day \<Rightarrow> bool" where
 gd_sat [intro]: "good_day Saturday"|
 gd_sun [intro]: "good_day Sunday"

theorem "good_day Sunday"
by (rule gd_sun)

(*
That is, we're defining what we mean by days being good by saying "Saturday is good, sunday is good, and that's all." Then someone can prove that Sunday is good simply by remarking that this is what we said when we defined what good_day meant.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

In other words, the constructor gd_sun is "primitive evidence" -- an axiom -- justifying the claim that Sunday is good.
Similarly, we can define a proposition day_before parameterized by two days, together with axioms stating that Monday comes before Tuesday, Tuesday before Wednesday, and so on.

Inductive day_before : day -> day -> Prop := 
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.

The axioms that we introduce along with an Inductively defined proposition can be richer than what we've seen above. For example, it is well known that every day is a fine day for singing a song...

Inductive fine_day_for_singing : day -> Prop := 
  | fdfs_any : forall d:day, fine_day_for_singing d.
*)

inductive day_before :: "day \<Rightarrow> day \<Rightarrow> bool" where
 db_tue [intro]: "day_before Tuesday Monday" |
 db_wed [intro]: "day_before Wednesday Tuesday" |
 db_thur [intro]: "day_before Thursday Wednesday" |
 db_fri [intro]: "day_before Friday Thursday" |
 db_sat [intro]: "day_before Saturday Friday" |
 db_sun [intro]: "day_before Sunday Saturday" |
 db_mon [intro]: "day_before Monday Sunday"

inductive fine_day_for_singing :: "day \<Rightarrow> bool" where
  any_day : "fine_day_for_singing d"

theorem "fine_day_for_singing Wednesday"
by (rule any_day)

(*
In particular, Wednesday is a fine day for singing.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

The first line here can be read "I'm about to show you some evidence for the proposition fine_day_for_singing wednesday, and I want to introduce the name fdfs_wed to refer to that evidence later on." The second line then instructs Coq how to assemble the evidence.
There's is another, more primitive way to accomplish the same thing: we can use a Definition whose left-hand side is the name we're introducing and whose right-hand side is the evidence itself, rather than a script for how to build it.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

The expression fdfs_any wednesday can be thought of as instantiating the parameterized axiom fdfs_any with the specific argument wednesday. Alternatively, we can think of fdfs_any as a primitive function that takes a day and returns evidence that that day is a fine day for singing; its type, forall d:day, fine_day_for_singing d, expresses this functionality, in the same way that the polymorphic type forall X, list X in the previous chapter expressed the fact that nil can be thought of as a function from types to empty lists with elements of that type. On this reading, fdfs_any wednesday is an ordinary application expression.
Let's take another, slightly more interesting example. Let's say that a day of the week is "ok" if either (1) it is a good day or else (2) it falls the day before an ok day.

Inductive ok_day : day -> Prop := 
  | okd_gd : forall d, good_day d -> ok_day d 
  | okd_before : forall d1 d2, ok_day d2 -> day_before d2 d1 -> ok_day d1.
*)

inductive ok_day :: "day \<Rightarrow> bool" where
  okd_gd [intro]: "good_day d \<Longrightarrow> ok_day d" |
  okd_before [intro]: "\<lbrakk>ok_day d; day_before d d'\<rbrakk> \<Longrightarrow> ok_day d'"
(*
The first constructor can be read "To show that d is an OK day, it suffices to present evidence that d is good." The second can be read, "Another way to show that a day d1 is ok is to present evidence that it is the day before some other day d2 together with evidence that d2 is ok."
Now suppose that we want to prove that wednesday is an ok day. There are two ways to do it. First, we have the primitive way, where we simply write down an expression that has the right type -- a big nested application of constructors:

Definition okdw : ok_day wednesday := 
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday 
         (okd_gd saturday gd_sat) 
         db_sat) 
       db_fri)
    db_thu.

Second, we have the machine-assisted way, where we go into Proof mode and Coq guides us through a series of goals and subgoals until it is finally satisfied:

Theorem okdw' : ok_day wednesday.
Proof.
  (* wednesday is OK because it's the day before an OK day *)
  apply okd_before with (d2:=thursday).
  (* "subgoal: show that thursday is ok". *)
    (* thursday is OK because it's the day before an OK day *)
    apply okd_before with (d2:=friday).
    (* "subgoal: show that friday is ok". *)
      (* friday is OK because it's the day before an OK day *)
      apply okd_before with (d2:=saturday).
        (* "subgoal: show that saturday is ok". *)
          (* saturday is OK because it's good! *)
          apply okd_gd. apply gd_sat.
        (* "subgoal: show that the day before saturday is friday". *)
          apply db_sat.
    (* "subgoal: show that the day before friday is thursday". *)
      apply db_fri.
  (* "subgoal: show that the day before thursday is wednesday". *)
  apply db_thu. Qed.
*)

theorem "ok_day Wednesday"
by (metis ok_day.intros good_day.intros day_before.intros)

(* CL:  This is a cute opportunity to demonstrate a neat little tool that
        comes with Isabelle - metis is, if the problem is within its scope,
        even more powerful than auto.  auto shys from instantiating schematic
        variables as would be needed to do this proof, but metis is a heavy-duty
        decision procedure.  I believe, though, metis is all or nothing.  While
        auto will take care of what it can, metis doesn't modify the proof
        state at all if it can't succeed. 

        We can also get the same effect, in this case, by using a variant of
        auto called force.  We don't have to provide any arguments to force
        in this case because we already provided the [intro] attribute to
        the appropriate rules.
*)

theorem "ok_day Wednesday"
by force

(* CL: finally, let's do it by hand just by applying rules. *)

theorem "ok_day Wednesday"
apply (rule okd_before)
apply (rule okd_before)
apply (rule okd_before)
apply (rule okd_gd)
apply (rule gd_sat)
apply (rule db_sat)
apply (rule db_fri)
apply (rule db_thur)
done


(*
Fundamentally, though, these two ways of making proofs are the same, in the sense that what Coq is actually doing when it's following the commands in a Proof script is literally attempting to construct an expression with the desired type.

Print okdw'.

These expressions are often called proof objects.
Proof objects are the bedrock of reasoning in Coq. Tactic proofs are convenient shorthands that instruct Coq how to construct proof objects for us instead of our writing them out explicitly. Here, of course, the proof object is actually shorter than the tactic proof. But the proof objects for more interesting proofs can become quite large and complex -- building them by hand would be painful. Moreover, we'll see later on in the course that Coq has a number of automation tactics that can construct quite complex proof objects without our needing to specify every step.
The Curry-Howard Correspondence
The analogy
                 propositions  ~  sets / types
                 proofs        ~  data values 
is called the Curry-Howard correspondence (or Curry-Howard isomorphism). We will see that a great many things follow from it.
Just as a set can be empty, a singleton, finite, or infinite -- it can have zero, one, or many inhabitants -- a proposition may be inhabited by zero, one, many, or infinitely many proofs. Each inhabitant of a proposition P is a different way of giving evidence for P. If there are none, then P is not provable. If there are many, then P has many different proofs.
Implication
We've seen that the -> operator (implication) can be used to build bigger propositions from smaller ones. We need to think about what would constitute evidence for propositions built in this way. Consider this one:

Definition okd_before2 := forall d1 d2 d3, 
  ok_day d3 -> 
  day_before d2 d1 -> 
  day_before d3 d2 -> 
  ok_day d1.

In English: if we have three days, d1 which is before d2 which is before d3, and if we know d3 is ok, then so is d1.
It should be easy to imagine how we'd construct a tactic proof of okd_before2...
Exercise: 1 star, optional
Theorem okd_before2_valid : okd_before2.
Proof.
  (* FILL IN HERE *) Admitted.

But what should the corresponding proof object look like?
Answer: We've made a notational pun between -> as implication and -> as the type of functions. If we take this pun seriously, and if we're looking for an expression with type forall d1 d2 d3, ok_day d3 -> day_before d2 d1 -> day_before d3 d2 -> ok_day d1, then what we want is a function that takes six arguments (three days and three pieces of evidence) and returns a piece of evidence! Here it is:

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) => 
  fun (H : ok_day d3) => 
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
    okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Induction Axioms for Inductively Defined Types
Coq provides one more primitive form of evidence. Every time we declare a new Inductive datatype, Coq automatically generates an axiom that embodies the induction principle for this type.
The induction principle for a type t is called t_ind. Here is the one for natural numbers:

Check nat_ind.
(*  ===> nat_ind : forall P : nat -> Prop,
                      P 0  ->
                      (forall n : nat, P n -> P (S n))  ->
                      forall n : nat, P n  *)
*)

thm "nat.induct"

(*
Note that this is exactly the our_nat_induction property from above.
The induction tactic is a straightforward wrapper that, at its core, simply performs apply t_ind. To see this more clearly, let's experiment a little with using apply nat_ind directly, instead of the induction tactic, to carry out some proofs. Here, for example, is an alternate proof of a theorem that we saw in the Basics chapter.

Theorem mult_0_r' : forall n:nat, 
  mult n 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    simpl. reflexivity. Qed.

Several details in this proof are worth noting. First, in the induction step of the proof (the "S" case), we have to do a little bookkeeping manually (the intros) that induction does automatically.
Second, we do not introduce n into the context before applying nat_ind -- the conclusion of nat_ind is a quantified formula, and apply needs this conclusion to exactly match the shape of the goal state, including the quantifier. The induction tactic works either with a variable in the context or a quantified variable in the goal.
Third, the apply tactic automatically chooses variable names for us (in the second subgoal, here), whereas induction lets us specify (with the as... clause) what names should be used. The automatic choice is actually a little unfortunate, since it re-uses the name n for a variable that is different from the n in the original theorem. This is why the Case annotation is just S -- if we tried to write it out in the more explicit form that we've been using for most proofs, we'd have to write n = S n, which doesn't make a lot of sense! All of these conveniences make induction nicer to use in practice than applying induction principles like nat_ind directly. But it is important to realize that, modulo this little bit of bookkeeping, applying nat_ind is what we are really doing.
Exercise: 2 stars
Complete this proof without using the induction tactic.

Theorem plus_one_r' : forall n:nat, 
  plus n 1 = S n.
Proof.
  (* FILL IN HERE *) Admitted.
☐

*)
(*
The induction principles that Coq generates for other datatypes defined with Inductive follow a similar pattern. If we define a type t with constructors c1 ... cn, Coq generates an axiom with this shape:
    t_ind :
       forall P : t -> Prop,
            ... case for c1 ... ->
            ... case for c2 ... ->
            ... ->
            ... case for cn ... ->
            forall n : t, P n
The specific shape of each case depends on the arguments to the corresponding constructor. Before trying to write down a general rule, let's look at some more examples. First, an example where the constructors take no arguments:

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.
(* ===> yesno_ind
            : forall P : yesno -> Prop, 
                   P yes  ->
                   P no  ->
                   forall y : yesno, P y *)

Exercise: 1 star
Write out the induction principle that Coq will generate for the following datatype. Write down your answer on paper, and then compare it with what Coq prints.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
(* Check rgb_ind. *)
☐
Here's another example, this time with one of the constructors taking some arguments.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> (modulo a little tidying)
        natlist_ind :
           forall P : natlist -> Prop,
              P nnil  ->
              (forall (n : nat) (l : natlist), P l -> P (ncons n l))  ->
              forall n : natlist, P n *)

Exercise: 1 star
Suppose we had written the above definition a little differently:

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

Now what will the induction principle look like? ☐
From these examples, we can extract this general rule:
each constructor c takes argument types a1...an
each ai can be either t (the datatype we are defining) or some other type s
the corresponding case of the induction principle says (in English):
"for all values x1...xn of types a1...an, if P holds for each of the xs of type t, then P holds for c x1 ... xn".
Exercise: 1 star (ExSet)
Here is an induction principle for an inductively defined set.
      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e
Give an Inductive definition of ExSet:

(* Inductive ExSet : Type :=
(* FILL IN HERE *)
*)
*)
datatype exset = Con1 bool | Con2 nat exset
thm "exset.induct"

(*
☐
Next, what about polymorphic datatypes?
The inductive definition of polymorphic lists
      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
is very similar. The main difference is that, here, the whole definition is paramterized on a set X -- that is, we are defining a family of inductive types list X, one for each X. Note that, wherever list appears in the body of the declaration, it is always applied to the parameter X. The induction principle is likewise parameterized on X:
     list_ind :
       forall (X : Type) (P : list X -> Prop),
            P [] ->
            (forall (x : X) (l : list X), P l -> P (x :: l)) ->
            forall l : list X, P l
Note the wording here (and, accordingly, the form of list_ind): The whole induction principle is parameterized on X. That is, list_ind can be thought of as a polymorphic function that, when applied to a type X, gives us back an induction principle specialized to the type list X.
Exercise: 1 star
Write out the induction principle that Coq will generate for the following datatype. Compare your answer with what Coq prints.
Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
(* Check tree_ind. *)
*)

datatype 'a mytree = myleaf 'a | mynode "'a mytree" "'a mytree" "'a mytree"
thm mytree.induct

(*
☐
Exercise: 1 star (mytype)
Find an inductive definition that gives rise to the following induction principle:
      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m -> 
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m
☐
Exercise: 1 star, optional (foo)
Find an inductive definition that gives rise to the following induction principle:
      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2
☐
Exercise: 1 star, optional
Consider the following inductive definition:
Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

What induction principle will Coq generate for foo'? Fill in the blanks, then check your answer with Coq.)
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ -> 
                    _______________________ ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
☐
Induction Hypotheses
Where does the phrase "induction hypothesis" fit into this picture?
The induction principle for numbers
       forall P : nat -> Prop,
            P 0 ->
            (forall n : nat, P n -> P (S n)) ->
            forall n : nat, P n
is a generic statement that holds for all propositions P (strictly speaking, for all families of propositions P indexed by a number n). Each time we use this principle, we are choosing P to be a particular expression of type nat->Prop.
We can make the proof more explicit by giving this expression a name. For example, instead of stating the theorem mult_0_r as "forall n, mult n 0 = 0," we can write it as "forall n, P_m0r n", where P_m0r is defined as...

Definition P_m0r (n:nat) : Prop := 
  mult n 0 = 0.

... or equivalently...

Definition P_m0r' : nat->Prop := 
  fun n => mult n 0 = 0.

Now when we do the proof it is easier to see where P_m0r appears.

Theorem mult_0_r'' : forall n:nat, 
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
    (* Note the proof state at this point! *)
    unfold P_m0r. simpl. intros n' IHn'.
    apply IHn'. Qed.

This extra naming step isn't something that we'll do in normal proofs, but it is useful to do it explicitly for an example or two, because it allows us to see exactly what the induction hypothesis is. If we prove forall n, P_m0r n by induction on n (using either induction or apply nat_ind), we see that the first subgoal requires us to prove P_m0r 0 ("P holds for zero"), while the second subgoal requires us to prove forall n', P_m0r n' -> P_m0r n' (S n') (that is "P holds of S n' if it holds of n'" or, more elegantly, "P is preserved by S"). The induction hypothesis is the premise of this latter implication -- the assumption that P holds of n', which we are allowed to use in proving that P holds for S n'.
A Closer Look at the induction Tactic
(This section can be skimmed.)
The induction tactic actually does even more low-level bookkeeping for us than we discussed above.
Recall the informal statement of the induction principle for natural numbers:
If P n is some proposition involving a natural number n, and we want to show that P holds for all numbers n, we can reason like this:
show that P O holds
show that, if P n' holds, then so does P (S n')
conclude that P n holds for all n.
So, when we begin a proof with intros n and then induction n, we are first telling Coq to consider a particular n (by introducing it into the context) and then telling it to prove something about all numbers (by using induction).
What Coq actually does in this situation, internally, is to "re-generalize" the variable we perform induction on. For example, in the proof above that plus is associative...

Theorem plus_assoc' : forall n m p : nat, 
  plus n (plus m p) = plus (plus n m) p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary n, m, and
     p..." *)
  intros n m p.
  (* ...We now use the induction tactic to prove P n (that
     is, plus n (plus m p) = plus (plus n m) p) for _all_ n,
     and hence also for the particular n that is in the context
     at the moment. *)
  induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'".
    (* In the second subgoal generated by induction -- the
       "inductive step" -- we must prove that P n' implies 
       P (S n') for all n'.  The induction tactic 
       automatically introduces n' and P n' into the context
       for us, leaving just P (S n') as the goal. *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

It also works to apply induction to a variable that is quantified in the goal.

Theorem plus_comm' : forall n m : nat, 
  plus n m = plus m n.
Proof.
  induction n as [| n'].
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Note that induction n leaves m still bound in the goal -- i.e., what we are proving inductively is a statement beginning with forall m.
If we do induction on a variable that is quantified in the goal after some other quantifiers, the induction tactic will automatically introduce the variables bound by these quantifiers into the context.

Theorem plus_comm'' : forall n m : nat, 
  plus n m = plus m n.
Proof.
  (* Let's do induction on m this time, instead of n... *)
  induction m as [| m'].
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.
*)

(* CL: I believe that, in Isabelle, you can only ever do induction after applying the appropriate intro rules if it's quantified in the object logic. *)

(*
Exercise: 1 star, optional (plus_explicit_prop)
Rewrite both plus_assoc' and plus_comm' and their proofs in the same style as mult_0_r'' above -- that is, for each theorem, give an explicit Definition of the proposition being proved by induction, and state the theorem and proof in terms of this defined proposition.
(* FILL IN HERE *)
☐
One more quick digression, for adventurous souls: if we can define parameterized propositions using Definition, then can we also define them using Fixpoint? Of course we can! However, this kind of "recursive parameterization" doesn't correspond to anything very familiar from everyday mathematics. The following exercise gives a slightly contrived example.
Exercise: 4 stars, optional
Define a recursive function true_upto_n_implies_true_everywhere that makes true_upto_n_example work. << Fixpoint true_upto_n__true_everywhere (* FILL IN HERE *)
Example true_upto_n_example : (true_upto_n__true_everywhere 3 (fun n => even n)) = (even 3 -> even 2 -> even 1 -> forall m : nat, even m). Proof. reflexivity. Qed. >> ☐
Reasoning by Induction Over Evidence
Some of the examples in the opening discussion of propositions involved the concept of evenness. We began with a computation evenb n that checks evenness, yielding a boolean. From this, we built a proposition even n (defined in terms of evenb) that asserts that n is even. That is, we defined "n is even" to mean "evenb returns true when applied to n."
An alternative is to define the concept of evenness directly. This allows us, instead of going "indirectly" via the evenb function, to say straight out what we would be willing to accept as evidence that a given number is even.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).
*)

inductive ev :: "nat \<Rightarrow> bool" where
ev_0 [intro]: "ev 0" |
ev_SS [intro]: "ev n \<Longrightarrow> ev (Suc (Suc n))"


(*
Informally, this definition says that there are two ways to give evidence that a number m is even: either observe that it is zero, or else observe that n = S (S m) for some m and give further evidence that m itself is even. The constructors ev_0 and ev_SS are names for these different ways of giving evidence for evenness.
The Inductive keyword means exactly the same thing whether we are using it to define sets of data values (in the Type world) or sets of evidence (in the Prop world). Consider the parts of the inductive definition of ev above:
The first line declares that ev is a proposition indexed by a natural number.
The second line declares that the constructor ev_0 can be taken as evidence for the assertion ev O.
The third line declares that, if n is a number and E is evidence for the assertion ev n), then ev_SS n E can be taken as evidence for ev (S (S n)). That is, we can construct evidence that S (S n) is even by applying the constructor ev_SS to evidence that n is even.
Exercise: 1 star, optional
Give a tactic proof and a proof object showing that four is even.
(* FILL IN HERE *)
☐
Exercise: 2 stars
Give a tactic proof and a proof object showing that, if n is even, then so is 4+n.
(* FILL IN HERE *)
*)

(* CL: In Coq you can apply a theorem to arguments to get a new theorem.  
       You can do this in Isabelle in two ways - first, with [of \<dots>] which
       allows you to feed *terms* to a theorem, instantiating schematic varibles.  You can also feed theorems to a rule with [OF \<dots>] to immediately discharge
   hypotheses.*)

theorem "ev n \<Longrightarrow> ev (Suc (Suc (Suc (Suc n))))"
apply (rule ev_SS [of "(Suc (Suc n))"])
apply (rule ev_SS)
by assumption

(* CL: Isar proof! *)

theorem assumes H: "ev n"
        shows "ev (Suc (Suc (Suc (Suc n))))"
proof -
  have "ev (Suc (Suc n))" using H by (rule ev_SS)
  thus "ev (Suc (Suc (Suc (Suc n))))" by (rule ev_SS)
qed

(*
Exercise: 2 stars
Construct a tactic proof of the following proposition.

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
*)

theorem "ev (2*n)"
apply (induct n)
apply (simp, rule ev_0)
apply simp
by (rule ev_SS)

theorem "ev (2*n)"
apply (induct n)
by (auto intro: ev.intros)

(*
☐
Exercise: 4 stars, optional (double_even_pfobj)
Try to predict what proof object is constructed by the above tactic proof. (Before checking your answer, you'll want to strip out any uses of Case, as these will make the proof object a bit cluttered.)
☐
Besides constructing evidence of evenness, we can also reason about evidence of evenness. The fact that we introduced ev with an Inductive declaration tells us not only that the constructors ev_O and ev_SS are ways to build evidence of evenness, but also that these two constructors are the only ways that evidence of evenness can be built.
In other words, if someone gives us evidence E justifying the assertion ev n, then we know that E can only have one of two forms: either E is ev_0 (and n is O), or E is ev_SS n' E' (and n is S (S n')) and E' is evidence that n' is even.
Thus, it makes sense to use the tactics that we have already seen for inductively defined data to reason instead about inductively defined evidence.
For example, here we use a destruct on evidence that n is even in order to show that ev n implies ev (n-2).

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.



Exercise: 1 star (ev_minus2_n)
What happens if we try to destruct on n instead of E? ☐
We can also perform induction on evidence that n is even. Here we use it show that the old evenb function returns true on n when n is even according to ev.

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. simpl. unfold even in IHE'. apply IHE'. Qed.
*)

term myeven
theorem "ev n \<Longrightarrow> myeven n"
apply (erule ev.induct)
by simp_all

(* CL:  In order to more directly invoke the induction rule we want,
        we can use the induct tactic but set the rule used to be the induction
        rule of the ev predicate. *)

theorem "ev n \<Longrightarrow> myeven n"
apply (induct n rule: ev.induct)
by simp_all

(* 
(Of course, we'd expect that even n -> ev n also holds. We'll see that it does in the next chapter.)
Exercise: 1 star (ev_even_n)
Could this proof be carried out by induction on n instead of E? ☐
The induction principle for inductively defined propositions does not follow quite the same form as that of inductively defined sets. For now, take the intuitive view that induction on evidence ev n is similar to induction on n, but restricts our attention to only those numbers for which evidence ev n could be generated. We will look at the induction principle of ev in more depth below, to explain what's really going on.
Exercise: 1 star (l_fails)
The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
Briefly explain why.
(* FILL IN HERE *)
☐
Exercise: 2 stars
Here's another exercise requiring induction.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  (* FILL IN HERE *) Admitted.
*)

theorem "ev n \<Longrightarrow> ev m \<Longrightarrow> ev (n+m)"
apply (rule ev.induct [of "n"])
apply assumption
apply simp
apply simp
apply (rule ev_SS)
apply assumption
done

(* OR!! *)
theorem "\<lbrakk>ev n; ev m\<rbrakk> \<Longrightarrow> ev (n+m)"
apply (rule ev.induct [of "n"])
by auto

(* OR!! *)

theorem "\<lbrakk>ev n; ev m\<rbrakk> \<Longrightarrow> ev (n+m)"
apply (induct n rule: ev.induct)
by auto

theorem assumes H1 : "ev m"
        shows "ev n \<Longrightarrow> ev (n + m)"
proof (induct n rule: ev.induct)
  case ev_0 
   show ?case using H1 by auto
  case (ev_SS n)
   thus ?case using H1 by auto
qed

(*
☐
Here's another situation where we want to analyze evidence for evenness and build two sub-goals.

Theorem SSev_ev_firsttry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  (* Oops. destruct destroyed far too much! 
     In the first sub-goal, we don't know that n is 0. *)
Admitted.
*)

theorem "ev (Suc (Suc n)) \<Longrightarrow> ev n"
by (erule ev.cases, simp_all)

(*
The right thing to use here is inversion (!)

Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.

(* Print SSev_even. *)

This use of inversion may seem a bit mysterious at first. Until now, we've only used inversion on equality propositions, to utilize injectivity of constructors or to discriminate between different constructors. But we see here that inversion can also be applied to analyzing evidence for inductively defined propositions.
Here's how inversion works in general. Suppose the name I refers to an assumption P in the current context, where P has been defined by an Inductive declaration. Then, for each of the constructors of P, inversion I generates a subgoal in which I has been replaced by the exact, specific conditions under which this constructor could have been used to prove P. Some of these subgoals will be self-contradictory; inversion throws these away. The ones that are left represent the cases that must be proved to establish the original goal.
In this particular case, the inversion analyzed the construction ev (S (S n)), determined that this could only have been constructed using ev_SS, and generated a new subgoal with the arguments of that constructor as new hypotheses. (It also produced an auxiliary equality, which happens to be useless.) We'll begin exploring this more general behavior of inversion in what follows.
Exercise: 1 star (inversion_practice)

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.
*)

theorem "ev (Suc (Suc (Suc (Suc n)))) \<Longrightarrow> ev n"
by (erule ev.cases, simp_all)+

theorem "ev (Suc (Suc (Suc (Suc n)))) \<Longrightarrow> ev n"
by (auto elim: ev.cases)

(*
inversion can also be used to derive goals by showing absurdity of a hypothesis.

Theorem even5_nonsense : 
  ev 5 -> plus 2 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
☐
*)

(* CL: At this point let's just call the numeral rule a thing and be
       done with it *)

declare eval_nat_numeral [simp]

theorem "ev 5 \<Longrightarrow> 2 + 2 = 9"
apply (erule ev.cases)
apply simp_all
apply (erule ev.cases)
apply simp_all
apply (erule ev.cases)
apply simp_all
done

(* OR *)

theorem "ev 5 \<Longrightarrow> 2 + 2 = 9"
by (erule ev.cases, simp_all)+

(* CL:  I've been using the '+' a few times now without explicitly stating what
        it does.  It repeatedly applies the rule it was applied to until 
        all the goals have been discharged or it fails. *)

theorem "ev 5 \<Longrightarrow> 2 + 2 = 9"
by (auto elim: ev.cases)

thm ev.cases

(*

We can generally use inversion instead of destruct on inductive propositions. This illustrates that in general, we get one case for each possible constructor. Again, we also get some auxiliary equalities that are rewritten in the goal but not in the other hypotheses.

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Exercise: 3 stars
Finding the appropriate thing to do induction on is a bit tricky here.

Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
*)
(*
theorem "\<lbrakk>ev (n+m); ev n\<rbrakk> \<Longrightarrow> ev m" 
proof -
  assume "ev n" and "ev (n+m)" then show "ev m" 
  proof (induct n)
  case ev_0 then show ?case by simp
  next
  case (ev_SS n) thus ?case apply -
apply simp
apply ()
by simp_all
qed
qed
This proof needs to be redone completely - it's a really bad example of Isar
style

- CL

*)
(*
☐
Exercise: 1 star
Here's something we could have proved a long time ago...
Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars
Here's an exercise that just requires applying existing lemmas. No induction or even case analysis is needed, but some of the rewriting may be tedious.
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
☐
Why Define Propositions Inductively?
We have seen that the proposition "some number is even" can be phrased in two different ways -- indirectly, via a testing function evenb, or directly, by inductively describing what constitutes evidence for evenness. These two ways of defining evenness are about equally easy to state and work with. Which we choose is basically a question of taste.
However, for many other properties of interest, the direct inductive definition is preferable, since writing a testing function may be awkward or even impossible. For example, consider the property MyProp defined as follows:
the number 4 has property MyProp
if n has property MyProp, then so does 4+n
if n+2 has property MyProp, then so does n
no other numbers have property MyProp
This is a perfectly sensible definition of a set of numbers, but we cannot translate this definition directly as a Coq Fixpoint (or translate it directly into a recursive function in any other programming language). We might be able to find a clever way of testing this property using a Fixpoint (indeed, it is not even too hard to find one in this case), but in general this could require arbitrarily much thinking.
In fact, if the property we are interested in is uncomputable, then we cannot define it as a Fixpoint no matter how hard we try, because Coq requires that all Fixpoints correspond to terminating computations.
On the other hand, writing an inductive definition of what it means to give evidence for the property MyProp is straightforward:

Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp (plus 4 n)
  | MyProp3 : forall n:nat, MyProp (plus 2 n) -> MyProp n.
*)

inductive MyProp :: "nat \<Rightarrow> bool" where
MyProp1 [intro]: "MyProp (Suc (Suc (Suc (Suc 0))))" |
MyProp2 [intro]: "MyProp n \<Longrightarrow> MyProp (Suc (Suc (Suc (Suc  n))))" |
MyProp3 [intro]: "MyProp (Suc (Suc n)) \<Longrightarrow> MyProp n"

(*
The first three clauses in the informal definition of MyProp above are reflected in the first three clauses of the inductive definition. The fourth clause is the precise force of the keyword Inductive.
As we did with evenness, we can now construct evidence that certain numbers satisfy MyProp.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  assert (12 = plus 4 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12.
  apply MyProp2.
  assert (8 = plus 4 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1. Qed.

Exercise: 2 stars (MyProp)
Here are two useful facts about MyProp. The proofs are left to you.

Theorem MyProp_0 : MyProp 0.
Proof.
  (* FILL IN HERE *) Admitted.
*)

theorem MyProp_0: "MyProp 0"
apply (rule MyProp3)
apply (rule MyProp3)
apply (rule MyProp1)
done

(*
Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  (* FILL IN HERE *) Admitted.
☐
With these, we can show that MyProp holds of all even numbers, and vice versa.
*)

theorem "MyProp n \<Longrightarrow> MyProp (2+n)"
apply (rule MyProp3)
apply (simp)
by (rule MyProp2)

(*
Theorem MyProp_ev : forall n:nat, 
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'. Qed.
*)

theorem "ev n \<Longrightarrow> MyProp n"
apply (induct n set: ev)
apply (rule MyProp_0)
apply (rule MyProp3)
apply (rule MyProp2)
apply assumption
done

theorem "ev n \<Longrightarrow> MyProp n"
apply (induct n set: ev)
by (auto simp: MyProp_0)

(*
Here's an informal proof of this theorem:
Theorem : For any nat n, if ev n then MyProp n.
Proof: Let a nat n and a derivation E of ev n be given. We go by induction on E. There are two case:
If the last step in E is a use of ev_0, then n is 0. But we know by lemma MyProp_0 that MyProp 0, so the theorem is satisfied in this case.
If the last step in E is by ev_SS, then n = S (S n') for some n' and there is a derivation of ev n'. By lemma MyProp_plustwo, it's enough to show MyProp n'. This follows directly from the inductive hypothesis for the derivation of ev n'. ☐
Exercise: 3 stars
Theorem ev_MyProp : forall n:nat, 
  MyProp n -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.
*)

theorem "MyProp n \<Longrightarrow> ev n"
apply (induct n set: MyProp)
apply (rule ev_SS)
apply (rule ev_SS)
apply (rule ev_0)
apply (rule ev_SS, rule ev_SS, assumption)
apply (erule ev.cases)
apply simp
apply simp
done

theorem "MyProp n \<Longrightarrow> ev n"
apply (induct n set: MyProp)
by (auto elim: ev.cases)

theorem "MyProp n \<Longrightarrow> ev n"
proof (induct n set: MyProp)
case MyProp1
  show ?case by (auto intro: ev.intros)
case (MyProp2 i)
  assume H : "ev i"
  thus ?case by (auto intro: ev.intros)
case (MyProp3 i)
  assume H : "ev (Suc (Suc i))"
  thus ?case by (auto elim: ev.cases intro: ev.intros)
qed
(*

☐
Exercise: 3 stars, optional (ev_MyProp_informal)
Write an informal proof corresponding to your formal proof of ev_MyProp:
Theorem: For any nat n, if MyProp n then ev n.
Proof: (* FILL IN HERE *)
☐
Exercise: 4 stars, optional (MyProp_pfobj)
Prove MyProp_ev and ev_MyProp again by constructing explicit proof objects by hand (as we did above in ev_plus4, for example).
(* FILL IN HERE *)
☐
Exercise: 3 stars, optional
Complete this proof using apply MyProp_ind instead of the induction tactic.

Theorem ev_MyProp' : forall n:nat, 
  MyProp n -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Induction Principles in Prop
Earlier, we looked in detail at the induction principles that Coq generates for inductively defined sets. Inductively defined propositions are handled slightly differently. For example, from what we've said so far, you might expect the inductive definition of ev
    Inductive ev : nat -> Prop :=
       | ev_0 : ev O
       | ev_SS : forall n:nat, ev n -> ev (S (S n)).
to give rise to an induction principle that looks like this...
    ev_ind_max :
       forall P : (forall n : nat, ev n -> Prop),
            P O ev_0 ->
            (forall (n : nat) (e : ev n), 
              P n e -> P (S (S n)) (ev_SS n e)) ->
            forall (n : nat) (e : ev n), P n e
... because:
Since ev is indexed by a number n (every ev object e is a piece of evidence that some particular number n is even), the proposition P is parameterized by both n and e -- that is, the induction principle can be used to prove assertions involving both an even number and the evidence that it is even.
Since there are two ways of giving evidence of evenness (ev has two constructors), applying the induction principle generates two subgoals:
We must prove that P holds for O and ev_0.
We must prove that, whenever n is an even number and e is evidence of its evenness, if P holds of n and e, then it also holds of S (S n) and ev_SS n e.
If these subgoals can be proved, then the induction principle tells us that P is true for all even numbers n and evidence e of their evenness.
But this is a little more flexibility than we actually need or want: it is giving us a way to prove logical assertions where the assertion involves properties of some piece of evidence of evenness, while all we really care about is proving properties of numbers that are even -- we are interested in assertions about numbers, not about evidence. It would therefore be more convenient to have an induction principle for proving propositions P that are parameterized just by n and whose conclusion establishes P for all even numbers n:
       forall P : nat -> Prop,
          ... ->
             forall n : nat, ev n -> P n
For this reason, Coq actually generates the following simplified induction principle for ev:
     ev_ind :
       forall P : nat -> Prop,
            P O ->
            (forall n : nat, ev n -> P n -> P (S (S n))) ->
            forall n : nat, ev n -> P n
In particular, Coq has dropped the evidence term e as a parameter of the the proposition P, and consequently has rewritten the assumption forall (n:nat) (e:ev n), ... to be forall (n:nat), ev n -> ...; i.e., we no longer require explicit evidence of the provability of ev n.

Module P.

Exercise: 3 stars (p_provability)
Consider the following inductively defined proposition:

    Inductive p : (tree nat) -> nat -> Prop :=
      | c1 : forall n, p (leaf _ n) 1
      | c2 : forall t1 t2 n1 n2,
                p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (plus n1 n2)
      | c3 : forall t n, p t n -> p t (S n).

Describe, in English, the conditions under which the proposition p t n is provable.
(* FILL IN HERE *)
☐

End P.

Proofs About Inductively Defined Propositions
The induction principles for inductively defined propositions like ev are a tiny bit more complicated than the ones for inductively defined sets. Intuitively, this is because we want to use them to prove things by inductively considering the possible shapes that something in ev can have -- either it is evidence that 0 is even, or else it is evidence that, for some n, S (S n) is even, and it includes evidence that n itself is. But the things we want to prove are not statements about evidence, they are statements about numbers. So we want an induction principle that allows reasoning by induction on the former to prove properties of the latter.
In English, the induction principle for ev goes like this:
Suppose, P is a property of natural numbers (that is, P n is a Prop for every n). To show that P n holds whenever n is even, it suffices to show:
P holds for 0
for any n, if n is even and P holds for n, then P holds for S (S n).
Formally:

Check ev_ind.
(* =====>  ev_ind
             : forall P : nat -> Prop,
               P 0 ->
               (forall n : nat, ev n -> P n -> P (S (S n))) ->
               forall n : nat, ev n -> P n *)

We can apply ev_ind directly instead of using induction, following pretty much the same pattern as above.

Theorem ev_even' : forall n,
  ev n -> even n.
Proof.
  apply ev_ind.
  Case "ev_0". unfold even. reflexivity.
  Case "ev_SS". intros n H IHE. unfold even. apply IHE. Qed.

Exercise: 3 stars, optional (prop_ind)
Write out the induction principles that Coq will generate for the inductive declarations list and MyProp. Compare your answers against the results Coq prints for the following queries.

(* Check list_ind. *)
(* Check MyProp_ind. *)
☐
The Big Picture: Coq's Two Universes
Expressions in Coq live in two distinct universes:
Type is the universe of computations and data.
Prop is the universe of logical assertions and evidence.
The two universes have some deep similarities -- in each, we can talk about values, inductive definitions, quantification, etc. -- but they play quite different roles in defining and reasoning about mathematical structures.
Values
Both universes start with an infinite set of constructors. Constructors have no internal structure: they are just atomic symbols. Examples:
true, false, O, S, nil, cons, ev_0, ev_SS, ...
The simplest values are expressions consisting entirely of constructor applications. Examples:
true
O
S (S (S O))
ev_0
ev_SS (S (S O)) ev_0
ev_SS (S (S (S (S O)))) (ev_SS (S (S O)) ev_0)
Such expressions can be though of as trees. Their leaves are nullary constructors (applied to no arguments), and their internal nodes are applications of constructors to one or more values. In the universe Type, we think of values as data. In Prop, we think of values as evidence. Values in Prop are sometimes called derivation trees.
Inductive Definitions
Inductive declarations give names to subsets of the set of all values. For example, the declaration of the inductive type nat defines a set whose elements are values representing natural numbers. That is, it picks out a subset nat of the set of all values that satisfies the following properties:
the value O is in this set;
the set is closed under applications of S (i.e., if a value n is in the set, then S n is too);
it is the smallest set satisfying these conditions (i.e., the only values in nat are the ones that must be, according to the previous two conditions... there is no other "junk").
Inductively defined sets can themselves appear as arguments to constructors in compound values. Examples:
nat
nil nat
cons nat O (cons nat (S O) (nil nat))
Also, we can write functions that take sets as arguments and return sets as results. For example, list is a function of type Type->Type: it takes a set X as argument and returns as result the set list X (whose members are lists with elements drawn from X).
Similarly, the declaration of the inductive type ev defines a family of propositions whose elements are values representing evidence that numbers are even. That is, for each n, the definition picks out a subset ev n of the set of all values satisfying the following properties:
the value ev_0 is in the set ev O
the sets are closed under well-typed applications of ev_SS -- i.e., if e is in the set ev n, then ev_SS n e is in the set ev (S (S n))
it is the smallest family of sets satisfying these conditions (i.e., the only values in any set ev n are the ones that must be, according to the previous two conditions... there is no other junk).
Functions and Quantifiers
The types A->B and forall x:A, B both describe functions from A to B. The only difference is that, in the second case, the expression B -- the type of the result -- can mention the argument x by name. For example:
The function fun x:nat => plus x x has type nat->nat -- that is, it maps each number n to a number.
The function fun X:Type => nil (list X) has type forall X:Type, list (list X) -- that is, it maps each set X to a particular list of lists of Xs. (Of course, nil is usually written as [] instead of nil X.)
In fact, the two ways of writing function types are really the same: In Coq, A->B is actually just an abbreviation for forall x:A, B, where x is some variable name not occurring in B. For example, the type of fun x:nat => plus x x can be written, if we like, as forall x:nat, nat.
Functions and Implications
In both Type and Prop, we can write functions that transform values into other values. Also, functions themselves are values; this means we can
write higher-order functions that take functions as arguments or return functions as results, and
apply constructors to functions to build complex values containing functions.
A function of type P->Q in Prop is something that takes evidence for P as an argument and yields evidence for Q as its result. Such a function can be regarded as evidence that P implies Q, since, whenever we have evidence that P is true, we can apply the function and get back evidence that Q is true: evidence for an implication is a function on evidence. This is why we use the same notation for functions and logical implications in Coq: they are exactly the same thing!
This coincidence between functions and implications is an instance of a deep connection between programming languages and mathematical logic known as the curry-howard correspondence.
Propositions and Booleans
Propositions and booleans are superficially similar, but they are really quite different things!
Booleans are values in the computational world. Every expression of type bool (with no free variables) can be simplified to either true or false.
Propositions are types in the logical world. They are either provable (i.e., there is some expression that has this type) or not (there is no such expression). It doesn't make sense to say that a proposition is "equivalent to true," and it is not necessarily the case that, if a proposition P is not provable, then ~P is provable.
We do sometimes use the words "true" and "false" informally when referring to propositions. Strictly speaking, we should not: a proposition is either provable or it is not.
Generalizing Induction Hypotheses
There is one last point that needs to be discussed in order to turn you loose on this chapter's homework problems.
In the previous chapter, we saw a proof that the double function is injective. The way we start this proof is a little bit delicate: if we begin it with
      intros n. induction n.
all is well. But if we begin it with
      intros n m. induction n.
we get stuck in the middle of the inductive case...

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
      (* Here we are stuck.  We need the assertion in order to
         rewrite the final goal (subgoal 2 at this point) to an
         identity.  But the induction hypothesis, IHn', does
         not give us n' = m' -- there is an extra S in the
         way -- so the assertion is not provable. *)
      Admitted.

What went wrong here?
The problem is that, at the point we invoke the induction hypothesis, we have already introduced m into the context intuitively, we have told Coq, "Let's consider some particular n and m..." and we now have to prove that, if double n = double m for this particular n and m, then n = m.
The next tactic, induction n says to Coq: We are going to show the goal by induction on n. That is, we are going to prove that the proposition
P n = "if double n = double m, then n = m"
holds for all n by showing
P O
(i.e., "if double O = double m then O = m")
P n -> P (S n)
(i.e., "if double n = double m then n = m" implies "if double (S n) = double m then S n = m").
If we look closely at the second statement, it is saying something rather strange: it says that, for any particular m, if we know
"if double n = double m then n = m"
then we can prove
"if double (S n) = double m then S n = m".
To see why this is strange, let's think of a particular m -- say, 5. The statement is then saying that, if we can prove
Q = "if double n = 10 then n = 5"
then we can prove
R = "if double (S n) = 10 then S n = 5".
But knowing Q doesn't give us any help with proving R! (If we tried to prove R from Q, we would say something like "Suppose double (S n) = 10..." but then we'd be stuck: knowing that double (S n) is 10 tells us nothing about whether double n is 10, so Q is useless at this point.)
To summarize: Trying to carry out this proof by induction on n when m is already in the context doesn't work because we are trying to prove a relation involving every n but just a single m.
The good proof of double_injective leaves m in the goal statement at the point where the induction tactic is invoked on n:

*)

(* CL:  Okay, so there's a couple of ways you can do something similar to generalize dependent in Coq.  The way that the Isabelle tutorial recommends is using
allowing the variable you want to quantify over be schematic variable in the
meta-logic and bind the independent variables under the object level
 \<forall> .
  The other option involves the keyword arbitrary in a use of induct, as we've
  already seen. 
*)  


(*

Theorem double_injective' : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for *every* m), but the IH is
       correspondingly more flexible, allowing us to
       choose any m we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular m and introduce the
       assumption that double n = double m.  Since we
       are doing a case analysis on n, we need a case
       analysis on m to keep the two "in sync". *)
    destruct m as [| m'].
    SCase "m = O". inversion eq. (* The 0 case is trivial *)
    SCase "m = S m'".
      (* At this point, since we are in the second
         branch of the destruct m, the m' mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the S branch of
         the induction, this is perfect: if we
         instantiate the generic m in the IH with the
         m' that we are talking about right now (this
         instantiation is performed automatically by
         apply), then IHn' gives us exactly what we
         need to finish the proof. *)
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.

So what we've learned is that we need to be careful about using induction to try to prove something too specific: If we're proving a property of n and m by induction on n, we may need to leave m generic.
However, this strategy doesn't always apply directly; sometimes a little rearrangement is needed. Suppose, for example, that we had decided we wanted to prove double_injective by induction on m instead of n.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        (* Here we are stuck again, just like before. *)
Admitted.

The problem is that, to do induction on m, we must first introduce n. (If we simply say induction m without introducing anything first, Coq will automatically introduce n for us!) What can we do about this?
One possibility is to rewrite the statement of the lemma so that m is quantified before n. This will work, but it's not nice: We don't want to have to mangle the statements of lemmas to fit the needs of a particular strategy for proving them -- we want to state them in the most clear and natural way.
What we can do instead is to first introduce all the quantified variables and then re-generalize one or more of them, taking them out of the context and putting them back at the beginning of the goal. The generalize dependent tactic does this.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.
*)

(*
Let's look at an informal proof of this theorem. Note that the proposition we prove by induction leaves n quantified, corresponding to the use of generalize dependent in our formal proof.
Theorem: For any nats n and m, if double n = double m, then n = m.
Proof: Let a nat m be given. We prove that for any n, if double n = double m then n = m by induction on m.
In the base case, we have m = 0. Let a nat n be given such that double n = double m. Since m = 0, we have double n = 0. If n = S n' for some n', then double n = S (S (double n')) by the definition of double. This would be a contradiction of the assumption that double n = 0, so n = 0, and thus n = m.
In the inductive case, we have m = S m' for some nat m'. Let a nat n be given such that double n = double m. By the definition of double, we therefore have:
      double n = S (S (double m'))
If n = 0, then double n = 0 (by the definition of double), which we have just seen is not the case. Thus, n = S n' for some n', and we have:
      S (S (double n')) = S (S (double m'))
which implies that double n' = double m'.
But observe that our inductive hypothesis here is: for any n, if double n = double m' then n = m'.
Applying this for n' then yields n' = m', and it follows directly that S n' = S m'. Since S n' = n and S m' = m, this is just what we wanted to show. ☐
Exercise: 3 stars (gen_dep_practice)
Carry out this proof by induction on m.
Theorem plus_n_n_injective_take2 : forall n m,
     plus n n = plus m m ->
     n = m.
Proof.
  (* FILL IN HERE *) Admitted.

Now prove this by induction on l.
Theorem index_after_last : forall (n : nat) (X : Type) 
                              (l : list X),
     length l = n ->
     index (S n) l = None.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars, optional (index_after_last_informal)
Write an informal proof corresponding to your Coq proof of index_after_last:
Theorem: For any nat n and list l, if length l = n then index (S n) l = None.
Proof: (* FILL IN HERE *)
☐
Exercise: 3 stars, optional (gen_dep_practice_opt)
Prove this by induction on l.
Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars, optional
Prove this by induction on m.
Theorem eqnat_false_S : forall n m,
  beq_nat n m = false -> beq_nat (S n) (S m) = false.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars, optional
Prove this by induction on l1, without using app_length.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 4 stars, optional
Prove this by induction on l, without using app_length.
Theorem app_length_twice : forall (X:Type) (n:nat) 
                                    (l:list X),
     length l = n ->
     length (l ++ l) = plus n n.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Additional Exercises
Exercise: 4 stars
A palindrome is a sequence that reads the same backwards as forwards.
Define an inductive proposition pal on list nat that captures what it means to be a palindrome. (Hint: You'll need three cases. Your definition should be based on the structure of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
may seem obvious, but will not work very well.)
Prove that
       forall l, pal (l ++ rev l).
Prove that
       forall l, pal l -> l = rev l.
Note: The converse thoerem
     forall l, l = rev l -> pal l.
is much harder!

(* FILL IN HERE *)
☐
Exercise: 4 stars, optional (subsequence)
A list is a subsequence of another list if all of the elements in the first list occur in the same order in the second list, possibly with some extra elements in between. For example,
    [1,2,3]
is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
but it is not a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]
Define an inductive proposition subseq on list nat that captures what it means to be a subsequence. (Hint: You'll need three cases.)
Prove that subsequence is reflexive, that is, any list is a subsequence of itself.
Prove that for any lists l1, l2, and l3, if l1 is a subsequence of l2, then l1 is also a subsequence of l2 ++ l3.
Optional, much harder: prove that subsequence is transitive, that is, if l1 is a subsequence of l2 and l2 is a subsequence of l3, then l1 is a subsequence of l3.
(* FILL IN HERE *)
☐
Exercise: 2 stars, optional
Suppose we make the following inductive definition:
   Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
Fill in the blanks to complete the induction principle that will be generated by Coq.
   foo_ind
        : forall (X Y : Set) (P : foo X Y -> Prop), 
          (forall x : X, __________________________________) ->
          (forall y : Y, __________________________________) ->
          (________________________________________________) ->
           ________________________________________________
☐
Exercise: 2 stars, optional
Consider the following induction principle:
   bar_ind
        : forall P : bar -> Prop,
          (forall n : nat, P (bar1 n)) ->
          (forall b : bar, P b -> P (bar2 b)) ->
          (forall (b : bool) (b0 : bar), P b0 -> P (bar3 b b0)) ->
          forall b : bar, P b
Write out the corresponding inductive set definition.
   Inductive bar : Set :=
     | bar1 : ________________________________________
     | bar2 : ________________________________________
     | bar3 : ________________________________________.
☐
Exercise: 2 stars, optional
Given the following inductively defined proposition:
  Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
    | nlt_nil : forall n, no_longer_than X [] n
    | nlt_cons : forall x l n, no_longer_than X l n -> 
                               no_longer_than X (x::l) (S n)
    | nlt_succ : forall l n, no_longer_than X l n -> 
                             no_longer_than X l (S n).
write the induction principle generated by Coq.
  no_longer_than_ind
       : forall (X : Set) (P : list X -> nat -> Prop),
         (forall n : nat, ____________________) ->
         (forall (x : X) (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         (forall (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         forall (l : list X) (n : nat), no_longer_than X l n -> 
           ____________________
☐
Exercise: 1 star, optional
Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
Which of the following propositions are provable?
R 2 [1,0]
R 1 [1,2,1,0]
R 6 [3,2,1,0]
*)

end