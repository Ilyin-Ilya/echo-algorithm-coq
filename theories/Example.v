(** * Worked Example: Echo on a Three-Node Line Graph

    Nodes: 0 - 1 - 2   (a path graph)
    Initiator: node 0

    We execute the echo algorithm step-by-step and verify the final state.

    [Line3Config] implements the correctness configuration signature.
    [Echo3] and [Echo3Correctness] are the resulting model and proof modules. *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
Import ListNotations.
Require Import LTS.
Require Import EchoAlgorithm.
Require Import EchoCorrectness.

(* ------------------------------------------------------------------ *)
(** ** 1. Concrete correctness configuration *)

Module Line3Config <: ECHO_CORRECTNESS_CONFIG.
  Definition node := nat.
  Definition node_eq : forall (n m : node), {n = m} + {n <> m} := Nat.eq_dec.

  Definition adj (u v : node) : bool :=
    match u, v with
    | 0, 1 | 1, 0 => true
    | 1, 2 | 2, 1 => true
    | _, _         => false
    end.

  Definition all_nodes : list node := [0; 1; 2].
  Definition initiator : node := 0.

  Lemma adj_sym : forall n m, adj n m = true -> adj m n = true.
  Proof.
    intros [|[|[|n]]] [|[|[|m]]]; simpl; intros H;
      try discriminate; reflexivity.
  Qed.

  Lemma adj_irrefl : forall n, adj n n = false.
  Proof. intros [|[|[|n]]]; reflexivity. Qed.

  Lemma initiator_in_nodes : In initiator all_nodes.
  Proof. simpl; auto. Qed.

  Lemma nodup_nodes : NoDup all_nodes.
  Proof.
    constructor.
    - simpl; intuition congruence.
    - constructor.
      + simpl; intuition congruence.
      + constructor.
        * simpl; intuition congruence.
        * constructor.
  Qed.
End Line3Config.

(** Compatibility names used in the calculations below. *)
Definition node3_eq := Line3Config.node_eq.
Definition line3_adj := Line3Config.adj.
Definition nodes3 := Line3Config.all_nodes.
Definition init0 := Line3Config.initiator.

(* ------------------------------------------------------------------ *)
(** ** 2. Instantiate the model and its correctness library *)

Module Echo3 := MakeEcho Line3Config.
Module Echo3Correctness := MakeEchoCorrectness Line3Config.

Definition echo3_LTS : LTS := Echo3.lts.

(* ------------------------------------------------------------------ *)
(** ** 3. Build the initial state *)

Definition start_state : Echo3.State :=
  mkEchoState (fun _ => Echo3.initial_process) [].

(** The initial state satisfies [echo_init]. *)
Lemma start_is_initial : Echo3.init start_state.
Proof.
  split.
  - intros n. reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 4. Step-by-step execution *)

(** Step 1: initiator fires — node 0 becomes Active, sends Token to node 1. *)
Definition after_start :=
  Echo3.start start_state.

Lemma after_start_initiator_active :
  (after_start.(es_procs) 0).(ps_phase) = Active.
Proof. reflexivity. Qed.

Lemma after_start_pending_one :
  (after_start.(es_procs) 0).(ps_pending) = 1.
Proof. reflexivity. Qed.

Lemma after_start_token_in_bag :
  In (mkPkt 0 1 Token) after_start.(es_msgs).
Proof. vm_compute. left. reflexivity. Qed.

(** Step 2: deliver Token(0→1).  Node 1 becomes Active, parent=0,
    forwards Token to node 2. *)
Definition pkt_01_tok : @echo_packet nat := mkPkt 0 1 Token.

Definition after_deliver_01 :=
  Echo3.deliver
    1
    (mkEchoState
       after_start.(es_procs)
       (Echo3.remove pkt_01_tok after_start.(es_msgs)))
    pkt_01_tok.

Lemma node1_active :
  (after_deliver_01.(es_procs) 1).(ps_phase) = Active.
Proof. reflexivity. Qed.

Lemma node1_parent :
  (after_deliver_01.(es_procs) 1).(ps_parent) = Some 0.
Proof. reflexivity. Qed.

Lemma token_to_2_in_bag :
  In (mkPkt 1 2 Token) after_deliver_01.(es_msgs).
Proof. vm_compute. left. reflexivity. Qed.

(** Step 3: deliver Token(1→2).  Node 2 is a leaf — it echoes immediately. *)
Definition pkt_12_tok : @echo_packet nat := mkPkt 1 2 Token.

Definition after_deliver_12 :=
  Echo3.deliver
    2
    (mkEchoState
       after_deliver_01.(es_procs)
       (Echo3.remove pkt_12_tok after_deliver_01.(es_msgs)))
    pkt_12_tok.

Lemma node2_active :
  (after_deliver_12.(es_procs) 2).(ps_phase) = Active.
Proof. reflexivity. Qed.

Lemma node2_parent :
  (after_deliver_12.(es_procs) 2).(ps_parent) = Some 1.
Proof. reflexivity. Qed.

(** Step 4: deliver Echo(2→1).  Node 1's pending drops to 0; it echoes to 0. *)
Definition pkt_21_echo : @echo_packet nat := mkPkt 2 1 Echo.

Definition after_echo_21 :=
  Echo3.deliver
    1
    (mkEchoState
       after_deliver_12.(es_procs)
       (Echo3.remove pkt_21_echo after_deliver_12.(es_msgs)))
    pkt_21_echo.

Lemma node1_echoes_back :
  In (mkPkt 1 0 Echo) after_echo_21.(es_msgs).
Proof. vm_compute. left. reflexivity. Qed.

(** Step 5: deliver Echo(1→0).  Node 0 has pending=1; it decides. *)
Definition pkt_10_echo : @echo_packet nat := mkPkt 1 0 Echo.

Definition after_echo_10 :=
  Echo3.deliver
    0
    (mkEchoState
       after_echo_21.(es_procs)
       (Echo3.remove pkt_10_echo after_echo_21.(es_msgs)))
    pkt_10_echo.

(** The initiator decides — algorithm terminates. *)
Lemma initiator_decides :
  (after_echo_10.(es_procs) 0).(ps_phase) = Decided.
Proof. reflexivity. Qed.

(** No messages remain in flight. *)
Lemma no_msgs_left : after_echo_10.(es_msgs) = [].
Proof. reflexivity. Qed.

(** The spanning tree is correct: 0→1→2. *)
Lemma spanning_tree_correct :
  (after_echo_10.(es_procs) 0).(ps_children) = [1] /\
  (after_echo_10.(es_procs) 1).(ps_children) = [2].
Proof. split; reflexivity. Qed.
