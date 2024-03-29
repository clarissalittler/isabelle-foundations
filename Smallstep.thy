theory Smallstep
imports Imp Rel Main begin

(*

(** * Smallstep: Small-step Operational Semantics *)
(* Version of 5/10/2010 *)

    

Require Export Imp.
Require Import Relations.


(** The evaluators we have seen so far (e.g., the ones for [aexp]s,
    [bexp]s, and commands) have been formulated in a "big-step"
    style -- they specify how a given expression can be evaluated to
    its final value (or a command plus a store to a final store) "all
    in one big step."
 
    This style is simple and natural for many purposes, but it there
    are some things it does not do well.  In particular, it does not
    give us a natural way of talking about _concurrent_ programming
    languages, where the "semantics" of a program -- i.e., the essence
    of how it behaves -- is not just which input states get mapped to
    which output states, but also includes the intermediate states
    that it passes through along the way, since these states can also
    be observed by concurrently executing code.

    Another shortcoming of the big-step style is more technical, but
    critical for some applications.  Consider the variant of Imp with
    lists that we introduced at the end of MoreHoare.v.  We chose to
    define the meaning of programs like [0 + nil] by specifying that a
    list should be interpreted as [0] when it occurs in a context
    expecting a number, but this was a bit of a hack.  It would be
    better simply to say that the behavior of such a program is
    _undefined_ -- it doesn't evaluate to any result.  We could easily
    do this: we'd just have to change the definitions of [aeval] and
    [beval] from Fixpoints to inductive propositions, so that we can
    make them partial functions instead of total ones.

    However, this way of defining Imp has a serious deficiency.  In
    this language, a command might _fail_ to map a given starting
    state to any ending state for two quite different reasons: either
    because the execution gets into an infinite loop or because, at
    some point, the program tries to do an operation that makes no
    sense, such as taking the successor of a boolean variable, and
    none of the evaluation rules can be applied.
 
    These two outcomes -- nontermination vs. getting stuck in an
    erroneous configuration -- are quite different.  In particular, we
    want to allow the first (permitting the possibility of infinite
    loops is the price we pay for the convenience of programming with
    general looping constructs like [while]) but prevent the
    second (which is just wrong), for example by adding some form of
    _typechecking_ to the language.  Indeed, this will be a major
    topic for the rest of the course.  As a first step, we need a
    different way of presenting the semantics that allows us to
    distinguish nontermination from erroneous "stuck states."
 
    So, for lots of reasons, we'd like to have a finer-grained way of
    defining and reasoning about program behaviors.  This is the topic
    of the present chapter.  We replace the "big-step" [eval] relation
    with a "small-step" relation that specifies, for a given program,
    how the "atomic steps" of computation are performed. *)

(* ########################################################### *)
(** * A Toy Language *)

(** To save space in the discussion, let's start with an incredibly
    simple language containing just constants and addition.  At the
    end of the chapter, we'll see how to apply the same techniques to
    the full Imp language. *)
*)

datatype tm = tm_const nat | tm_plus tm tm

(* 
Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) tactic(c) :=
  first;
  [ c "tm_const" | c "tm_plus" ].

Module SimpleArith0.

(** Here is a standard evaluator for this language, written in the
    same (big-step) style as we've been using up to this point. *)
*)

primrec eval :: "tm \<Rightarrow> nat" where
"eval (tm_const n) = n" |
"eval (tm_plus a a') = (eval a) + (eval a')"
(* 
Fixpoint eval (t : tm) : nat :=
  match t with
  | tm_const n => n
  | tm_plus a1 a2 => plus (eval a1) (eval a2)
  end.

(** We write [t ==> n] for "[t] evaluates to [n]." *)

Notation " t '==>' n " := (eval t = n) (at level 40).

End SimpleArith0.

Module SimpleArith1.

(** Now, here is the same evaluator, written in exactly the same
    style, but formulated as an inductively defined relation.  Again,
    we use the notation [t ==> n] for "[t] evaluates to [n]." *)

Reserved Notation " t '==>' n " (at level 40).
*)

inductive evalr :: "tm \<Rightarrow> nat \<Rightarrow> bool" where
e_const [intro]: "evalr (tm_const n) n" |
e_plus  [intro]: "n1+n2 = n3 \<Longrightarrow> evalr t1 n1 \<Longrightarrow> evalr t2 n2 \<Longrightarrow> evalr (tm_plus t1 t2) n3"

(* 
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      tm_const n ==> n
  | E_Plus : forall t1 t2 n1 n2, 
      t1 ==> n1 -> 
      t2 ==> n2 ->
      tm_plus t1 t2 ==> plus n1 n2

  where " t '==>' n " := (eval t n).

End SimpleArith1.

(** Here is a slight variation, still in big-step style, where the
    final result of evaluating a term is also a term, rather than a
    bare number. *)

Reserved Notation " t '==>' t' " (at level 40).
*)

inductive evalr' :: "tm \<Rightarrow> tm \<Rightarrow> bool" where
 e_const' [intro]: "evalr' (tm_const n) (tm_const n)" |
 e_plus'  [intro]: "n1 + n2 = n3 \<Longrightarrow>
            evalr' t1 (tm_const n1) \<Longrightarrow>
            evalr' t2 (tm_const n2) \<Longrightarrow> 
            evalr' (tm_plus t1 t2) (tm_const n3)"

(* 
Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n1,
        tm_const n1 ==> tm_const n1
  | E_Plus : forall t1 n1 t2 n2,
        t1 ==> tm_const n1 ->
        t2 ==> tm_const n2 ->
        tm_plus t1 t2 ==> tm_const (plus n1 n2)

  where " t '==>' t' " := (eval t t').

Tactic Notation "eval_cases" tactic(first) tactic(c) :=
  first;
  [ c "E_Const" | c "E_Plus" ].

Module SimpleArith2.

(** Now, here is a small-step version. *)

Reserved Notation " t '-->' t' " (at level 40).
*)

inductive step :: "tm \<Rightarrow> tm \<Rightarrow> bool" where
 ST_PlusConstConst [intro]: "n1 + n2 = n3 \<Longrightarrow> 
                      step (tm_plus (tm_const n1) (tm_const n2))
                           (tm_const n3)" |
 ST_Plus1 [intro]: "step t1 t1' \<Longrightarrow>
             step (tm_plus t1 t2) (tm_plus t1' t2)" |
 ST_Plus2 [intro]: "step t2 t2' \<Longrightarrow>
             step (tm_plus (tm_const n) t2) (tm_plus (tm_const n) t2')"

inductive_cases step_const [elim] : "step (tm_const n) y"
inductive_cases step_plus [elim] : "step (tm_plus t1 t2) y"

thm step_plus

(*
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' -> 
      tm_plus (tm_const n1) t2 --> tm_plus (tm_const n1) t2'

  where " t '-->' t' " := (step t t').

(** Things to notice:
 
    - We are defining just a single reduction step, in which
      one [tm_plus] node is replaced by its value.

    - Each step finds the _leftmost_ [tm_plus] node that is ready to
      go (both of its operands are constants) and rewrites it in
      place.  The first rule tells how to rewrite this [tm_plus] node
      itself; the other two rules tell how to find it.

    - A term that is just a constant cannot take a step.
*)

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_PlusConstConst" | c "ST_Plus1" | c "ST_Plus2" ].

(** A couple of examples of reasoning with the [step]
    relation... *)

(** If [t1] can take a step to [t1'], then [tm_plus t1 t2] steps
    to [plus t1' t2]: *)
*)

lemma "step (tm_plus (tm_plus (tm_const 0) (tm_const 3))
                     (tm_plus (tm_const 2) (tm_const 4)))
            (tm_plus (tm_const 3)
                     (tm_plus (tm_const 2) (tm_const 4)))"
apply (rule ST_Plus1)
apply (rule ST_PlusConstConst)
by simp

(* 
Example test_step_1 : 
      tm_plus 
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
      -->
      tm_plus 
        (tm_const (plus 0 3))
        (tm_plus (tm_const 2) (tm_const 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

(** **** Exercise: 2 stars (test_step_2) *)
(** Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [tm_plus (tm_const n) t2] steps to [tm_plus (tm_const n)
    t2']: *)

Example test_step_2 : 
      tm_plus 
        (tm_const 0)
        (tm_plus 
          (tm_const 2) 
          (tm_plus (tm_const 0) (tm_const 3)))
      -->
      tm_plus 
        (tm_const 0)
        (tm_plus 
          (tm_const 2) 
          (tm_const (plus 0 3))).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** One interesting property of the [-->] relation is that, like the
    evaluation relation for our language of Imp programs, it is
    _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that
    [t --> t'] is provable.  Formally, this is the same as saying that
    [-->] is a partial function.

    _Proof sketch_: We must show that if [x] steps to both [y1] and
    [y2] then [y1] and [y2] are equal.  Consider the last rules used
    in the derivations of [step x y1] and [step x y2].

      - If both are [ST_PlusConstConst], the result is immediate.

      - It cannot happen that one is [ST_PlusConstConst] and the other
        is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
        the form [tm_plus t1 t2] where both [t1] and [t2] are
        constants (by [ST_PlusConstConst]) _and_ one of [t1] or [t2] has
        the form [tm_plus ...].

      - Similarly, it cannot happen that one is [ST_Plus1] and the other
        is [ST_Plus2], since this would imply that [x] has the form
        [tm_plus t1 t2] where [t1] has both the form [tm_plus t1 t2] and
        the form [tm_const n].

      - The cases when both derivations end with [ST_Plus1] or
        [ST_Plus2] follow by the induction hypothesis.  [] *)
*)

term single_valued
(* CL: So this is the proper Isabelle definition for partial_function, but
   it only applies to uncurried predicates, i.e. 
   if our predicate had type "(tm \<times> tm) \<Rightarrow> bool" instead of
   tm \<Rightarrow> tm \<Rightarrow> bool.
   Instead of going through that mess, I think I'll just prove the unrolled
   theorem anyway.  *)

lemma "step x y1 \<Longrightarrow> step x y2 \<Longrightarrow> y1 = y2"
apply (induct x y1 arbitrary: y2 rule: step.induct)
by fast+

theorem step_deterministic : "step x y1 \<Longrightarrow> step x y2 \<Longrightarrow> y1 = y2"
proof (induct x y1 arbitrary: y2 rule: step.induct)
 case (ST_PlusConstConst n1 n2 n3)
   show "tm_const n3 = y2" using ST_PlusConstConst by auto
next        
 case (ST_Plus1 t1 t1' t2)
 show "tm_plus t1' t2 = y2" using ST_Plus1(1,3) by (auto intro: ST_Plus1(2))
next
 case (ST_Plus2 t2 t2' v)
 show "tm_plus (tm_const v) t2' = y2" using ST_Plus2(1,3) by (auto intro: ST_Plus2(2))
qed
 
(* 
Theorem step_deterministic:
  partial_function step.
Proof.
  unfold partial_function. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case.
    Case "ST_PlusConstConst". intros y2 Hy2. step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". reflexivity.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2". inversion H2.
    Case "ST_Plus1". intros y2 Hy2. step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst".
        rewrite <- H0 in Hy1. inversion Hy1.
      SCase "ST_Plus1".
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      SCase "ST_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2". intros y2 Hy2. step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H1 in Hy1. inversion Hy1.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2".
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption.  Qed.

End SimpleArith2.

(* ########################################################### *)
(** ** Values *)

(** Let's take a moment to slightly generalize the way we state the
    definition of single-step reduction.  It is useful to think of the
    [-->] relation as defining a sort of _abstract machine_ for
    evaluating programs:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _final states_ of the machine are ones where there is no
        more computation to be done.

    We can then think about executing a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [-->] relation to find a sequence of
        machine states such that each steps to the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution.

    Intuitively, it is clear that the final states of the machine are
    always terms of the form [tm_const n] for some [n].  We call such
    terms _values_. *)

Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).
*)

inductive val :: "tm \<Rightarrow> bool" where
  v_const : "val (tm_const n)"

inductive_cases val_plus [elim] : "val (tm_plus t1 t2)"

thm val_plus

(* 
(** Having introduced the idea of values, we can use it in the
    definition of the [-->] relation to write [ST_Plus2] rule in a
    slightly more intuitive way: *)

Reserved Notation " t '-->' t' " (at level 40).
*)

inductive step' :: "tm \<Rightarrow> tm \<Rightarrow> bool" where
  ST_PlusConstConst' [intro]: "n1 + n2 = n3 \<Longrightarrow>
                  step' (tm_plus (tm_const n1) (tm_const n2)) (tm_const n3)" |
  ST_Plus1' [intro]: "step' t1 t1' \<Longrightarrow>
               step' (tm_plus t1 t2) (tm_plus t1' t2)" |
  ST_Plus2' [intro]: "val v \<Longrightarrow>
               step' t2 t2' \<Longrightarrow>
               step' (tm_plus v t2) (tm_plus v t2')"

inductive_cases step'_const [elim] : "step' (tm_const n) y"
inductive_cases step'_plus [elim] : "step' (tm_plus t1 t2) y"               

(* 
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          tm_plus (tm_const n1) (tm_const n2)
      --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *) 
        t2 --> t2' ->
        tm_plus v1 t2 --> tm_plus v1 t2'

  where " t '-->' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_PlusConstConst" | c "ST_Plus1" | c "ST_Plus2" ].
*)

lemma val_normal : "val t \<Longrightarrow> \<not> (step' t t')"
apply (induct t)
by (auto)

theorem step'_deterministic : "step' x y1 \<Longrightarrow> step' x y2 \<Longrightarrow> y1 = y2"
proof (induct x y1 arbitrary: y2 rule: step'.induct)
  case (ST_PlusConstConst' n1 n2 n3)
   show "tm_const n3 = y2" using ST_PlusConstConst' by auto
next        
 case (ST_Plus1' t1 t1' t2)
 show "tm_plus t1' t2 = y2" using ST_Plus1'(3,1) by (auto simp: val_normal elim: ST_Plus1'(2))
next
 case (ST_Plus2' v t2 t2')
 show "tm_plus v t2' = y2" using ST_Plus2'(4,1,2) by (auto simp: val_normal intro: ST_Plus2'(3))
qed

(*
(** **** Exercise: 3 stars (redo_determinacy) *)
(** As a sanity check on this change, let's re-verify determinacy 

    Proof sketch: We must show that if [x] steps to both [y1] and [y2]
    then [y1] and [y2] are equal.  Consider the final rules used in
    the derivations of [step x y1] and [step x y2].

    - If both are [ST_PlusConstConst], the result is immediate.

    - It cannot happen that one is [ST_PlusConstConst] and the other
      is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
      the form [tm_plus t1 t2] where both [t1] and [t2] are
      constants (by [ST_PlusConstConst]) AND one of [t1] or [t2] has
      the form [tm_plus ...].

    - Similarly, it cannot happen that one is [ST_Plus1] and the other
      is [ST_Plus2], since this would imply that [x] has the form
      [tm_plus t1 t2] where [t1] both has the form [tm_plus t1 t2] and
      is a value (hence has the form [tm_const n]).

    - The cases when both derivations end with [ST_Plus1] or
      [ST_Plus2] follow by the induction hypothesis. [] *)

(** Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write it from
    scratch and just use the earlier one if you get stuck. *)

Theorem step_deterministic :
  partial_function step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ########################################################### *)
(** ** Normal Forms *)

(** _Theorem_: For all [t:tm], either [t] is a value, or there exists
    a term [t'] such that [t --> t'].

    _Proof_: By induction on [t].

    - Suppose [t = tm_const n]. Then [t] is a [value].

    - Suppose [t = tm_plus t1 t2], where (by the IH) [t1] is either a
      value or can step to some [t1'], and where [t2] is either a
      value or can step to some [t2']. We must show [tm_plus t1 t2] is
      either a value or steps to some [t'].

      - If [t1] and [t2] are both values, then [t] can take a step, by
        [ST_PlusConstConst].

      - If [t1] is a value and [t2] can take a step, then so can [t],
        by [ST_Plus2].

      - If [t1] can take a step, then so can [t], by [ST_Plus1].  [] *)

(** This important property is called _progress_, because every term
    either is a value or can "make progress" by stepping to some other
    term. *)
*)

theorem progress : "val t \<or> (\<exists> t'. step' t t')"
apply (induct t)
apply (rule disjI1)
apply (rule v_const)
apply (rule disjI2)
apply auto
apply (erule val.cases)
apply (erule val.cases)
apply (erule ssubst)
apply (erule ssubst)
apply (rule_tac x="tm_const (n + na)" in exI)
apply (rule ST_PlusConstConst', simp)
done

(* CL:  TODO - automate the above proof more.  A little tricky since it's really just manually ripping apart
        \<exists> *)

(* 
Theorem progress : forall t,
  value t \/ (exists t', t --> t').
Proof.  
  tm_cases (induction t) Case.
    Case "tm_const". left. apply v_const.
    Case "tm_plus". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (tm_const (plus n n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (tm_plus t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0]. 
          exists (tm_plus t' t2).
          apply ST_Plus1. apply H0.  Qed.

(** The idea of "making progress" can be extended to tell us something
    interesting about [value]s: they are exactly the terms that
    _cannot_ make progress in this sense.  To state this fact, let's
    begin by giving a name to terms that cannot make progress: We'll
    call them _normal forms_. *)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
*)

definition normal :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"normal r t \<equiv> \<not> (\<exists> t'. r t t')"

(* 
(** We've actually defined what it is to be a normal form for an
    arbitrary relation [R] over an arbitrary set [X], not just for the
    particular reduction relation over terms that we are interested in
    at the moment.  We'll re-use the same terminology for talking
    about other relations later in the course. *)

(** We can use this terminology to generalize the observation we made
    in the progress theorem: normal forms and values are actually the
    same thing. *)

(** Note that we state and prove this result as two different lemmas,
    rather than using an if-and-only-if ([<->]).  That's because it
    will be easier to apply the separate lemmas later on; as noted
    before, Coq's facilities for dealing "in-line" with [<->]
    statements are a little awkward. *)
*)

lemma value_is_nf : "val t \<Longrightarrow> normal step' t"
by (auto simp: normal_def val_normal)

lemma nf_is_value : "normal step' t \<Longrightarrow> val t"
proof (unfold normal_def)
  fix t
  assume H : "\<not> (\<exists>t'. step' t t')"  
  have L : "val t \<or> (\<exists>t'. step' t t')" by (rule progress)
  show "val t" using H L by simp
qed
(* 
Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  intros t H. unfold normal_form. intros contra. inversion H.
  rewrite <- H0 in contra. destruct contra as [t' P]. inversion P.   Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  (* This is a corollary of [progress]. *)
  intros t H.
  unfold normal_form in H.
  assert (value t \/ exists t', t --> t') as G.
    SCase "Proof of assertion". apply progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

(** Why are these last two facts interesting?  For two reasons:
 
    - Because [value] is a syntactic concept -- it is a defined by
      looking at the form of a term -- while [normal_form] is a
      semantic one -- it is defined by looking at how the term steps.
      Is it not obvious that these concepts should coincide.
 
    - Indeed, there are lots of languages in which the concepts of
      normal form and value do _not_ coincide. *)
 
(** Let's examine how this can happen... *)

(* ##################################################### *)

(** We might, for example, accidentally define [value] so that it
    includes some terms that are not finished reducing. *)

Module Temp1. 
(* Open an inner module so we can redefine value and step. *)

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n)
| v_funny : forall t1 n2,                       (* <---- *)
              value (tm_plus t1 (tm_const n2)).  


Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_plus v1 t2 --> tm_plus v1 t2'

  where " t '-->' t' " := (step t t').

(** **** Exercise: 3 stars (value_not_same_as_normal_form) *)
Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Temp1.

(* ########################################################### *)

(** Alternatively, we might accidentally define [step] so that it
    permits something designated as a value to reduce further. *)

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,                         (* <---- *)
      tm_const n --> tm_plus (tm_const n) (tm_const 0)
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_plus v1 t2 --> tm_plus v1 t2'

  where " t '-->' t' " := (step t t').

(** **** Exercise: 3 stars (value_not_same_as_normal_form) *)
Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Temp2.

(* ########################################################### *)

(** Finally, we might accidentally define [value] and [step] so that
    there is some term that is not a value but that cannot take a step
    in the [step] relation.  Such terms are said to be _stuck_. *)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (tm_const n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_plus t1 t2 --> tm_plus t1' t2

  where " t '-->' t' " := (step t t').

(** Note that [ST_Plus2] is missing.  *)

(** **** Exercise: 3 stars (value_not_same_as_normal_form') *)
Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Temp3.

(* ########################################################### *)
(** ** Exercises *)

Module Temp4.

(** Here is another very simple language whose terms, instead of being
    just plus and numbers, are just the booleans true and false and a
    conditional expression... *)


Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3

  where " t '-->' t' " := (step t t').

(** **** Exercise: 1 star (smallstep_bools) *) 
(** Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Coq.) *)

Definition bool_step_prop1 :=
  tm_false --> tm_false.

(* FILL IN HERE *)

Definition bool_step_prop2 :=
     tm_if
       tm_true
       (tm_if tm_true tm_true tm_true)
       (tm_if tm_false tm_false tm_false)
  --> 
     tm_true.

(* FILL IN HERE *)

Definition bool_step_prop3 :=
     tm_if
       (tm_if tm_true tm_true tm_true)
       (tm_if tm_true tm_true tm_true)
       tm_false
   --> 
     tm_if
       tm_true
       (tm_if tm_true tm_true tm_true)
       tm_false.

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (progress_bool) *)
(** Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well. *)

Theorem progress : forall t,
  value t \/ (exists t', t --> t').
Proof.  
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (step_deterministic) *)
Theorem step_deterministic :
  partial_function step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module Temp5. 

(** **** Exercise: 2 stars (smallstep_bool_shortcut) *) 
(** Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the [then] and
    [else] branches of a conditional are the same value (either
    [tm_true] or [tm_false]) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable: *)

(** Write an extra clause for the step relation that achieves this
    effect and prove [bool_step_prop4]. *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
(* FILL IN HERE *)

  where " t '-->' t' " := (step t t').
(** [] *)

(** **** Exercise: 2 stars (bool_step_prop4_holds) *)
(** To check that your previous answer is correct, prove that the
    following step is now possible. *)

Definition bool_step_prop4 :=
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     --> 
         tm_false.

Example bool_step_prop4_holds : 
  bool_step_prop4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (properties_of_altered_step) *)
(** It can be shown that the determinism and progress theorems
    for the step relation in the lecture notes also hold for the
    definition of step given above.  After we add the clause
    [ST_ShortCircuit]...

    - Does step_deterministic still hold? Write yes or no and
      briefly (1 sentence) explain your answer.

      Optional exercise: prove your answer correct in Coq.
*)

(* FILL IN HERE *)

(**
   - Does a progress theorem hold? Write yes or no and briefly
     (1 sentence) explain your answer.

     Optional exercise: prove your answer correct in Coq.
*)

(* FILL IN HERE *)

(**
   - In general, is there any way we could cause progress to fail
     if we took away one or more constructors from the original
     step relation? Write yes or no and briefly (1 sentence)
     explain your answer.

  (* FILL IN HERE *)
*)
(** [] *)
End Temp5.
End Temp4.


(* ########################################################### *)
(** * Multi-Step Reduction *)

(** Until now, we've been working with the _single-step reduction_
    relation [-->], which formalizes the individual steps of _abstract
    machine_ for executing programs.  It is also interesting to use
    this machine to reduce programs to completion, to find out what
    final result they yield.  This can be formalized in two steps.

    - First, we define a _multi-step reduction relation_ [stepmany],
      which relates terms [t] and [t'] if [t] can reach [t'] by any
      number (including 0) of single reduction steps.

    - Then we can define a "result" of a term [t] as a normal form
      that [t] can reach by some number of reduction steps.  Formally,
      we write [normal_form_of t t'] to mean that [t'] is a normal
      form reachable from [t] by many-step reduction.
 *)


(* ########################################################### *)
(** ** Multi-Step Reduction *)

(** Now we're ready to define the _multi-step reduction_ relation. *)

Definition stepmany := refl_step_closure step.
*)

definition stepmany where
"stepmany \<equiv> refl_step_closure step'"

(* 
Notation " t '-->*' t' " := (stepmany t t') (at level 40).

(** A few examples... *)
*)

lemma "stepmany (tm_plus (tm_plus (tm_const 0) (tm_const 3))
                         (tm_plus (tm_const 2) (tm_const 4)))
                (tm_const 9)"
unfolding stepmany_def
apply (rule rsc_step)
apply (rule ST_Plus1')
apply (rule ST_PlusConstConst')
apply simp
apply (rule rsc_step)
apply (rule ST_Plus2')
apply (rule v_const)
apply (rule ST_PlusConstConst')
apply simp
apply (rule rsc_step)
apply (rule ST_PlusConstConst')
apply simp
apply simp
apply (rule rsc_refl)
done

(* 
Lemma test_stepmany_1:
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
   -->* 
      tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  apply rsc_step with 
            (tm_plus
                (tm_const (plus 0 3))
                (tm_plus (tm_const 2) (tm_const 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply rsc_step with
            (tm_plus
                (tm_const (plus 0 3))
                (tm_const (plus 2 4))).
  apply ST_Plus2. apply v_const. 
  apply ST_PlusConstConst. 
  apply rsc_R. 
  apply ST_PlusConstConst.  Qed.

(** Here's an alternate proof that uses [eapply] to avoid explicitly
    constructing all the intermediate terms. *)

Lemma test_stepmany_1':
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
  -->*
      tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  eapply rsc_step. apply ST_Plus1. apply ST_PlusConstConst.
  eapply rsc_step. apply ST_Plus2. split. apply ST_PlusConstConst.
  eapply rsc_step. apply ST_PlusConstConst.
  apply rsc_refl.  Qed.

(** **** Exercise: 1 star (test_stepmany_2) *)
Lemma test_stepmany_2:
  tm_const 3 -->* tm_const 3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (test_stepmany_3) *)
Lemma test_stepmany_3:
      tm_plus (tm_const 0) (tm_const 3)
   -->*
      tm_plus (tm_const 0) (tm_const 3).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (test_stepmany_4) *)
Lemma test_stepmany_4:
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_plus (tm_const 0) (tm_const 3)))
  -->*
      tm_plus
        (tm_const 0)
        (tm_const (plus 2 (plus 0 3))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ########################################################### *)
(** ** Normal Forms Again *)

(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)
*)

definition step_normal_form where
"step_normal_form = normal step'"

definition normal_form_of where
"normal_form_of t t' \<equiv> (stepmany t t' \<and> step_normal_form t')"


(* 
Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

(** We have already seen that single-step reduction is
    deterministic -- i.e., a given term can take a single step in
    at most one way.  It follows from this that, if [t] can reach
    a normal form, then this normal form is unique -- i.e.,
    [normal_form_of] is a partial function.  In other words, we
    can actually pronounce [normal_form t t'] as "[t'] is _the_
    normal form of [t]." *)
*)

thm converse_rtranclpE

lemma "\<lbrakk>normal_form_of t t'; normal_form_of t t''\<rbrakk> \<Longrightarrow> t' = t''"
unfolding normal_form_of_def stepmany_def step_normal_form_def normal_def
apply (elim conjE)
apply (induct t t' arbitrary: t'' rule: refl_step_closure.induct)
apply (erule refl_step_closure.cases, simp, simp)
apply (erule refl_step_closure.cases)
back
apply clarify
apply (erule notE)
back
apply (rule_tac x="y" in exI) 
apply simp
apply clarify
apply (subgoal_tac "y=ya")
apply simp
by (rule step'_deterministic)

(* CL:  TODO - Find a cuter way to handle things other than "back" *)

(* 
(** **** Exercise: 3 stars, optional (test_stepmany_3) *)
Theorem normal_forms_unique:
  partial_function normal_form_of.
Proof.
  unfold partial_function. unfold normal_form_of.  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12]. destruct P2 as [P21 P22]. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  (* FILL IN HERE *) Admitted.
(** [] *)
  
(** Indeed, something stronger is true for this language (though not
    for all languages): the reduction of _any_ term [t] will
    eventually reach a normal form -- i.e., [normal_form_of] is a
    _total_ function.  Formally, we say the [step] relation is
    _normalizing_. *)
*)



(* 
Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (refl_step_closure R) t t' /\ normal_form R t'.

(** To prove that [step] is normalizing, we need a couple of lemmas.
    First, we observe that, if [t] reduces to [t'] in many steps, then
    the same sequence of reduction steps is possible when [t] appears
    as the left-hand child of a [tm_plus] node, and similarly when [t]
    appears as the right-hand child of a [tm_plus] node whose
    left-hand child is a value. *)

Lemma stepmany_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     tm_plus t1 t2 -->* tm_plus t1' t2.
Proof.
  intros t1 t1' t2 H. rsc_cases (induction H) Case.
    Case "rsc_refl". apply rsc_refl. 
    Case "rsc_step". apply rsc_step with (tm_plus y t2). 
        apply ST_Plus1. apply H. 
        apply IHrefl_step_closure.  Qed.

(** **** Exercise: 2 stars *)
Lemma stepmany_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 -->* t2' ->
     tm_plus t1 t2 -->* tm_plus t1 t2'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** _Theorem_: The [step] function is normalizing -- i.e., for every
    [t] there exists some [t'] such that [t] steps to [t'] and [t'] is
    a normal form.

    _Proof sketch_: By induction on terms.  There are two cases to
    consider:

    - [t = tm_const n] for some [n].  Here [t] doesn't take a step,
      and we have [t' = t].  We can derive the left-hand side by
      reflexivity and the right-hand side by observing (a) that values
      are normal forms (by [value_is_nf]) and (b) that t is a
      value (by [v_const]).
      
    - [t = tm_plus t1 t2] for some [t1] and [t2].  By the IH, both
      [t1] and [t2] normalize to normal forms [t1'] and [t2'],
      respectively.  Recall that normal forms are values (by
      [nf_is_value]); we know that [t1' = tm_const n1] and [t2' =
      tm_const n2], for some [n1] and [n2].  We can combine the [-->*]
      derivations for [t1] and [t2] to prove that [tm_plus t1 t2]
      reduces in many steps to [tm_const (plus n1 n2)].

      It is clear that our choice of [t' = tm_const (plus n1 n2)] is a
      value, which is in turn a normal form. [] *)

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  tm_cases (induction t) Case.
    Case "tm_const". 
      exists (tm_const n). 
      split.
      SCase "l". apply rsc_refl. 
      SCase "r". apply value_is_nf. apply v_const.
    Case "tm_plus".
      destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
      destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
      apply nf_is_value in H12. apply nf_is_value in H22.
      inversion H12 as [n1]. inversion H22 as [n2]. 
      rewrite <- H in H11. 
      rewrite <- H0 in H21.
      exists (tm_const (plus n1 n2)).
      split.
        SCase "l". 
          apply rsc_trans with (tm_plus (tm_const n1) t2).
          apply stepmany_congr_1. apply H11.
          apply rsc_trans with 
             (tm_plus (tm_const n1) (tm_const n2)).
          apply stepmany_congr_2. apply v_const. apply H21.
          apply rsc_R. apply ST_PlusConstConst.
        SCase "r". 
          apply value_is_nf. apply v_const.  Qed.

(* ########################################################### *)
(** ** Equivalence of Big-Step and Small-Step Reduction *)

(** Having defined the operational semantics of our tiny programming
    language in two different styles, it makes sense to ask whether
    these definitions actually define the same thing!  They do, but it
    is not completely straightforward to show this, or even to see how
    to state it exactly, since one of the relations only goes a small
    step at a time while the other proceeds in large chunks. *)

Lemma eval__value : forall t1 t2,
     eval t1 t2 ->
     value t2.
Proof.
  intros t1 t2 HE.
  (eval_cases (inversion HE) Case); apply v_const.  Qed.

(** **** Exercise: 3 stars (eval__stepmany) *)
(** You'll want to use the congruences and some properties of
    [rsc] for this. *)

Theorem eval__stepmany : forall t v,
  eval t v -> t -->* v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (eval__stepmany_inf) *)
(** Write an informal version of the proof of eval__stepmany.
(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars (step__eval) *)
Theorem step__eval : forall t t' v,
     t --> t' ->
     t' ==> v ->
     t ==> v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem stepmany__eval : forall t v,
  normal_form_of t v -> t ==> v.
Proof.
  intros t v Hnorm.
  unfold normal_form_of in Hnorm.
  inversion Hnorm as [Hs Hnf]; clear Hnorm.
  (* v is a normal form -> v = tm_const n for some n *)
  apply nf_is_value in Hnf. inversion Hnf. clear Hnf.
  (rsc_cases (induction Hs) Case); subst.
  Case "rsc_refl".
    apply E_Const.
  Case "rsc_step".
    eapply step__eval. eassumption. apply IHHs. reflexivity.  Qed.

(** Bringing it all together, we can crisply say that the [v] is the
    normal form of [t] iff [t] evaluates to [v]. *)

Corollary stepmany_iff_eval : forall t v,
  normal_form_of t v <-> t ==> v.
Proof.
  split.
  Case "->". apply stepmany__eval.
  Case "<-". unfold normal_form_of. intros E. split. apply eval__stepmany. 
    assumption. apply value_is_nf. eapply eval__value. eassumption.  Qed.

(* ########################################################### *)
(** ** Additional exercises *)

(** **** Exercise: 4 stars (combined_properties) *)
(** We've considered the arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)

Module Combined.

Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) tactic(c) :=
  first;
  [ c "tm_const" | c "tm_plus" |
    c "tm_true" | c "tm_false" | c "tm_if" ].

Inductive value : tm -> Prop :=
  | v_const : forall n, value (tm_const n)
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) --> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      tm_plus t1 t2 --> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->     
      t2 --> t2' ->
      tm_plus v1 t2 --> tm_plus v1 t2'
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3

  where " t '-->' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) tactic(c) :=
  first;
  [ c "ST_PlusConstConst" | c "ST_Plus1" | c "ST_Plus2" |
    c "ST_IfTrue" | c "ST_IfFalse" | c "ST_If" ].

(** Earlier, we separately proved for both plus- and if-expressions

    - that the step relation was a partial function (i.e., it was
      deterministic), and

    - a progress lemma, stating that every term is either a value
      or can take a step.

    Prove or disprove these for the combined langauge. *)
(* FILL IN HERE *)
(** [] *)
End Combined.


(* ########################################################### *)
(** * Small-Step Imp *)

(** Here is the small-step version of the Imp operational semantics.
    Although the definitions are bigger, the basic ideas are exactly
    the same as what we've seen above. *)

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '-->a' t' " (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i, 
    AId i / st -->a ANum (st i)
  | AS_Plus : forall st n1 n2,
    APlus (ANum n1) (ANum n2) / st -->a ANum (plus n1 n2)
  | AS_Plus1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
    (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
    (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (AMult (a1) (a2)) / st -->a (AMult (a1') (a2))
  | AS_Mult2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (AMult v1 a2) / st -->a (AMult v1 a2')

  where " t '/' st '-->a' t' " := (astep st t t').

Reserved Notation " t '/' st '-->b' t' " (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b 
    (if (beq_nat n1 n2) then BTrue else BFalse)
  | BS_Eq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BEq a1 a2) / st -->b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
    aval v1 -> 
    a2 / st -->a a2' ->
    (BEq v1 a2) / st -->b (BEq v1 a2')
  | BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b 
             (if (ble_nat n1 n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BLe a1 a2) / st -->b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BLe v1 a2) / st -->b (BLe v1 (a2'))
  | BS_NotTrue : forall st,
    (BNot BTrue) / st -->b BFalse
  | BS_NotFalse : forall st,
    (BNot BFalse) / st -->b BTrue
  | BS_NotStep : forall st b1 b1',
    b1 / st -->b b1' ->
    (BNot b1) / st -->b (BNot b1')
  | BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st -->b BTrue
  | BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st -->b BFalse
  | BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st -->b BFalse
  | BS_AndTrueStep : forall st b2 b2',
    b2 / st -->b b2' ->
    (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
    b1 / st -->b b1' ->
    (BAnd b1 b2) / st -->b (BAnd b1' b2)

  where " t '/' st '-->b' t' " := (bstep st t t').

(** Notice that we didn't actually bother to define boolean values --
    they aren't needed in the definition of [-->b] (why?), though
    they might be if our language were a bit larger. *)

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [SKIP] as a "command value" -- i.e., a command that
         has reached a normal form.  

            - An assignment command reduces to [SKIP] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [SKIP], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [WHILE] command by transforming it into a
         conditional followed by the same [WHILE].  There are other
         ways of achieving the desired effect, but they all have the
         common feature that the original [WHILE] command needs to be
         saved somewhere off on the side while a single copy of the
         loop body is being evaluated. *)

Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
    a / st -->a a' ->
    (i ::= a) / st --> (i ::= a') / st 
  | CS_Ass : forall st i n, 
    (i ::= (ANum n)) / st --> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st --> c1' / st' ->
    (c1 ; c2) / st --> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
    (SKIP ; c2) / st --> c2 / st
  | CS_IfTrue : forall st c1 c2,
    IFB BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
    IFB BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
    b / st -->b b' ->
    IFB b THEN c1 ELSE c2 FI / st --> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
        (WHILE b DO c1 END) / st
    --> (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* ########################################################### *)
(** * Concurrent Imp *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Tactic Notation "com_cases" tactic(first) tactic(c) :=
  first;
  [ c "SKIP" | c "::=" | c ";" | c "IFB" | c "WHILE" | c "PAR" ].

Notation "'SKIP'" := 
  CSkip.
Notation "l '::=' a" := 
  (CAss l a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" := 
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
    a / st -->a a' -> 
    (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n, 
    (i ::= (ANum n)) / st --> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st --> c1' / st' ->
    (c1 ; c2) / st --> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
    (SKIP ; c2) / st --> c2 / st
  | CS_IfTrue : forall st c1 c2,
    (IFB BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
    (IFB BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
    b /st -->b b' -> 
    (IFB b THEN c1 ELSE c2 FI) / st --> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
    (WHILE b DO c1 END) / st --> 
             (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st
  (* New: *)
  | CS_Par1 : forall st c1 c1' c2 st',
    c1 / st --> c1' / st' -> 
    (PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
    c2 / st --> c2' / st' ->
    (PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
    (PAR SKIP WITH SKIP END) / st --> SKIP / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cstepmany := refl_step_closure cstep. 

Notation " t '/' st '-->*' t' '/' st' " := 
   (refl_step_closure cstep  (t,st) (t',st')) (at level 40, st at level 39, t' at level 39).  

(** A small example: the following program can terminate with X set to
    any value. *)

Definition par_loop_init : com :=
  X ::= ANum 0;
  Y ::= ANum 1.

Definition par_loop_body : com :=
  PAR
    Y ::= ANum 0
  WITH
    WHILE BNot (BEq (AId Y) (ANum 0)) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

Definition par_loop : com :=
  par_loop_init;
  par_loop_body.

Example par_loop_example_0:
  exists st',
       par_loop / empty_state  -->* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply rsc_step. apply CS_SeqStep. unfold par_loop_init. apply CS_SeqStep. apply CS_Ass. 
  eapply rsc_step. apply CS_SeqStep. apply CS_SeqFinish.
  eapply rsc_step. apply CS_SeqStep. apply CS_Ass. 
  eapply rsc_step. apply CS_SeqFinish.
  eapply rsc_step. unfold par_loop_body. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq. simpl. 
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotTrue. 
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse. 
  eapply rsc_step. apply CS_ParDone. 
  eapply rsc_refl. 
  reflexivity. Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_state -->* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply rsc_step. apply CS_SeqStep. apply CS_SeqStep. apply CS_Ass. 
  eapply rsc_step. apply CS_SeqStep. apply CS_SeqFinish.
  eapply rsc_step. apply CS_SeqStep. apply CS_Ass. 
  eapply rsc_step. apply CS_SeqFinish.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq. simpl. 
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotFalse. 
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue. 
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.  
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.

  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq. simpl. 
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotFalse. 
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue. 
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.  
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply rsc_step. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotStep. apply BS_Eq. simpl. 
  eapply rsc_step. apply CS_Par2. apply CS_IfStep. 
    apply BS_NotTrue. 
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse. 
  eapply rsc_step. apply CS_ParDone. 
  eapply rsc_refl. 
  reflexivity. Qed.

(** More generally... *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 1 ->
  par_loop_body / st -->* par_loop_body / (update st X (S n)).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 1 ->
  exists st',
    par_loop_body / st -->*  par_loop_body / st' /\ st' X = n /\ st' Y = 1.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state -->*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n. 
  destruct (par_body_n n (update (update empty_state X 0) Y 1)). auto.
  destruct H as [H' [HX HY]]. 

  exists (update x Y 0). split.
  eapply rsc_step. apply CS_SeqStep. apply CS_SeqStep. apply CS_Ass.
  eapply rsc_step. apply CS_SeqStep. apply CS_SeqFinish.
  eapply rsc_step. apply CS_SeqStep. apply CS_Ass.
  eapply rsc_step. apply CS_SeqFinish.

  eapply rsc_trans with (par_loop_body,x). apply H'. 
    
  eapply rsc_step. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_NotStep. apply BS_Eq1. apply AS_Id. rewrite update_eq.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_NotStep. apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_NotTrue.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  apply rsc_refl.

  rewrite update_neq. assumption. auto.
Qed.


End CImp.

*)

end