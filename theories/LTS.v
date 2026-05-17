(** * Labeled Transition Systems

    A foundational LTS framework for reasoning about distributed algorithms.
    An LTS is a tuple (State, Label, initial, transition).  We build on top
    of it reachability, invariants, and trace semantics. *)

From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** 1. Core LTS definition *)

Record LTS : Type := mkLTS {
  lts_state : Type;
  lts_label : Type;
  lts_init  : lts_state -> Prop;
  lts_trans : lts_state -> lts_label -> lts_state -> Prop;
}.

(* ------------------------------------------------------------------ *)
(** ** 2. Reachability *)

Section Reachability.

  Variable M : LTS.

  (** [reachable s] holds iff [s] is reachable from some initial state. *)
  Inductive reachable : lts_state M -> Prop :=
  | reach_init : forall s, lts_init M s -> reachable s
  | reach_step : forall s lbl s',
      reachable s ->
      lts_trans M s lbl s' ->
      reachable s'.

End Reachability.

(* ------------------------------------------------------------------ *)
(** ** 3. Finite traces *)

Section Traces.

  Variable M : LTS.

  (** A trace step pairs a label with the state *after* the transition. *)
  Record step_item : Type := mkStep {
    si_label : lts_label M;
    si_state : lts_state M;
  }.

  (** A finite trace is a list of step items together with an initial state. *)
  Record trace : Type := mkTrace {
    tr_init  : lts_state M;
    tr_steps : list step_item;
  }.

  (** Validity of a trace: the initial state is initial, and each consecutive
      pair of states is connected by the transition relation. *)
  Fixpoint valid_trace_steps (s : lts_state M) (steps : list step_item) : Prop :=
    match steps with
    | nil => True
    | item :: rest =>
        lts_trans M s (si_label item) (si_state item) /\
        valid_trace_steps (si_state item) rest
    end.

  Definition valid_trace (tr : trace) : Prop :=
    lts_init M (tr_init tr) /\
    valid_trace_steps (tr_init tr) (tr_steps tr).

  (** The final state of a trace. *)
  Definition trace_final (tr : trace) : lts_state M :=
    match List.rev (tr_steps tr) with
    | nil => tr_init tr
    | item :: _ => si_state item
    end.

End Traces.

(* ------------------------------------------------------------------ *)
(** ** 4. Safety invariants *)

Section Invariants.

  Variable M : LTS.

  (** [is_invariant P] means P holds on every reachable state. *)
  Definition is_invariant (P : lts_state M -> Prop) : Prop :=
    forall s, reachable M s -> P s.

  (** Inductive proof obligation: prove P on initial states and show it is
      preserved by every transition.  This is sufficient for [is_invariant]. *)
  Lemma invariant_by_induction (P : lts_state M -> Prop) :
    (forall s, lts_init M s -> P s) ->
    (forall s lbl s', P s -> lts_trans M s lbl s' -> P s') ->
    is_invariant P.
  Proof.
    intros Hinit Hstep s Hreach.
    induction Hreach as [s Hi | s lbl s' Hr IH Ht].
    - apply Hinit; exact Hi.
    - apply Hstep with (s := s) (lbl := lbl); [exact IH | exact Ht].
  Qed.

  (** If two invariants hold, their conjunction is an invariant. *)
  Lemma invariant_conj (P Q : lts_state M -> Prop) :
    is_invariant P -> is_invariant Q -> is_invariant (fun s => P s /\ Q s).
  Proof.
    intros HP HQ s Hr; split; [apply HP | apply HQ]; exact Hr.
  Qed.

End Invariants.

(* ------------------------------------------------------------------ *)
(** ** 5. LTS composition (two components sharing a label type) *)

Section Composition.

  (** Product composition: two LTSs step independently.  The composed label
      tags each step with which component moved. *)
  Variable A B : LTS.

  Inductive comp_label : Type :=
  | CompLeft  : lts_label A -> comp_label
  | CompRight : lts_label B -> comp_label.

  Definition comp_state : Type := lts_state A * lts_state B.

  Definition comp_init (s : comp_state) : Prop :=
    lts_init A (fst s) /\ lts_init B (snd s).

  Inductive comp_trans : comp_state -> comp_label -> comp_state -> Prop :=
  | comp_step_left : forall sa lbl sa' sb,
      lts_trans A sa lbl sa' ->
      comp_trans (sa, sb) (CompLeft lbl) (sa', sb)
  | comp_step_right : forall sa sb lbl sb',
      lts_trans B sb lbl sb' ->
      comp_trans (sa, sb) (CompRight lbl) (sa, sb').

  Definition compose : LTS := mkLTS
    comp_state
    comp_label
    comp_init
    comp_trans.

End Composition.
