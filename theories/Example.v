(** * Worked Example: Echo on a Three-Node Line Graph

    Nodes: 0 - 1 - 2   (a path graph)
    Initiator: node 0

    We execute the echo algorithm step-by-step and verify the final state.

    Function signatures after section closure:
      echo_init      : node -> echo_state -> Prop
      initiator_start: node -> node_eq -> initiator -> all_nodes -> adj -> echo_state -> echo_state
      handle_msg     : node -> node_eq -> all_nodes -> adj -> self -> echo_state -> pkt -> echo_state
      remove_pkt     : node -> node_eq -> pkt -> list pkt -> list pkt  *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
Import ListNotations.
Require Import LTS.
Require Import EchoAlgorithm.

(* ------------------------------------------------------------------ *)
(** ** 1. Concrete node type *)

Definition node3_eq : forall (n m : nat), {n = m} + {n <> m} := Nat.eq_dec.

Definition line3_adj (u v : nat) : bool :=
  match u, v with
  | 0, 1 | 1, 0 => true
  | 1, 2 | 2, 1 => true
  | _, _         => false
  end.

Definition nodes3 : list nat := [0; 1; 2].
Definition init0  : nat := 0.

(* ------------------------------------------------------------------ *)
(** ** 2. Instantiate the LTS *)

Definition echo3_LTS : LTS :=
  echo_LTS nat node3_eq init0 nodes3 line3_adj.

(* ------------------------------------------------------------------ *)
(** ** 3. Build the initial state *)

Definition start_state : @echo_state nat :=
  mkEchoState (fun _ => @initial_proc nat) [].

(** The initial state satisfies [echo_init]. *)
Lemma start_is_initial : echo_init start_state.
Proof.
  split.
  - intros n. reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** 4. Step-by-step execution *)

(** Step 1: initiator fires — node 0 becomes Active, sends Token to node 1. *)
Definition after_start :=
  initiator_start node3_eq init0 nodes3 line3_adj start_state.

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
  handle_msg node3_eq nodes3 line3_adj
    1
    (mkEchoState
       after_start.(es_procs)
       (remove_pkt node3_eq pkt_01_tok after_start.(es_msgs)))
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
  handle_msg node3_eq nodes3 line3_adj
    2
    (mkEchoState
       after_deliver_01.(es_procs)
       (remove_pkt node3_eq pkt_12_tok after_deliver_01.(es_msgs)))
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
  handle_msg node3_eq nodes3 line3_adj
    1
    (mkEchoState
       after_deliver_12.(es_procs)
       (remove_pkt node3_eq pkt_21_echo after_deliver_12.(es_msgs)))
    pkt_21_echo.

Lemma node1_echoes_back :
  In (mkPkt 1 0 Echo) after_echo_21.(es_msgs).
Proof. vm_compute. left. reflexivity. Qed.

(** Step 5: deliver Echo(1→0).  Node 0 has pending=1; it decides. *)
Definition pkt_10_echo : @echo_packet nat := mkPkt 1 0 Echo.

Definition after_echo_10 :=
  handle_msg node3_eq nodes3 line3_adj
    0
    (mkEchoState
       after_echo_21.(es_procs)
       (remove_pkt node3_eq pkt_10_echo after_echo_21.(es_msgs)))
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
