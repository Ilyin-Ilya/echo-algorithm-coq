(** * The Echo Algorithm

    Segall/Chang's Echo algorithm constructs a spanning tree rooted at an
    initiator via a two-phase wave:
      1. Tokens flow outward (initiator -> all nodes)
      2. Echoes flow inward  (leaves -> initiator)

    When the initiator has received an echo on every incident edge it
    *decides* — the spanning tree is complete.

    We model each process as a state machine with:
      - A phase     ∈ { Idle | Active | Decided }
      - An optional parent (set on first token receipt)
      - A counter   of echoes still expected

    Network labels are packets; the global LTS is the product of all
    per-process state machines sharing the message pool. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import LTS.

(* ------------------------------------------------------------------ *)
(** ** 1. Abstract node type

    We leave the node type abstract and only require decidable equality
    and a finite list of all nodes. *)

Section EchoAlgorithm.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.

(** The initiator.  Exactly one node acts as the wave source. *)
Variable initiator : node.

(** A finite list of all nodes (no duplicates assumed for proofs). *)
Variable all_nodes : list node.

(** Adjacency: [adj u v] means there is an undirected edge between u and v. *)
Variable adj : node -> node -> bool.

(* ------------------------------------------------------------------ *)
(** ** 2. Message type *)

Inductive echo_msg : Type :=
  | Token : echo_msg   (* broadcast wave from parent  *)
  | Echo  : echo_msg.  (* reply wave back to parent   *)

(* ------------------------------------------------------------------ *)
(** ** 3. Per-process state *)

Inductive phase : Type :=
  | Idle    : phase   (* has not yet seen a Token          *)
  | Active  : phase   (* has received a Token; awaiting echoes from children (leaf nodes echo immediately) *)
  | Decided : phase.  (* initiator only: all echoes received *)

Record proc_state : Type := mkProc {
  ps_phase    : phase;
  (** For a non-initiator: the neighbor from which the first Token arrived. *)
  ps_parent   : option node;
  (** Number of echoes still expected before this node can echo its parent
      (or decide, for the initiator). *)
  ps_pending  : nat;
  (** Collected spanning tree children (neighbors that echoed back). *)
  ps_children : list node;
}.

(* ------------------------------------------------------------------ *)
(** ** 4. Packets *)

Record echo_packet : Type := mkPkt {
  ep_src  : node;
  ep_dst  : node;
  ep_body : echo_msg;
}.

(* ------------------------------------------------------------------ *)
(** ** 5. Global state *)

Record echo_state : Type := mkEchoState {
  es_procs : node -> proc_state;
  es_msgs  : list echo_packet;
}.

(** Update one node's process state. *)
Definition update_proc
    (f : node -> proc_state) (n : node) (s : proc_state)
    : node -> proc_state :=
  fun m => if node_eq n m then s else f m.

(** Neighbors of node [n]. *)
Definition nbrs (n : node) : list node :=
  List.filter (fun m => adj n m) all_nodes.

(** Make a packet list sending [msg] from [src] to each node in [dsts]. *)
Definition send_to_all (src : node) (dsts : list node) (msg : echo_msg)
    : list echo_packet :=
  List.map (fun dst => mkPkt src dst msg) dsts.

(* ------------------------------------------------------------------ *)
(** ** 6. Initiator startup action

    The initiator fires first: it moves from Idle to Active and floods
    Token messages to all its neighbors. *)

(** The initiator's one-time startup action.
    It atomically moves itself from Idle to Active, sets pending = |neighbors|
    (it must hear back from every neighbor before it can decide), and floods
    a Token to every neighbor.  No parent is recorded — the initiator is the
    root of the spanning tree. *)
Definition initiator_start (gs : echo_state) : echo_state :=
  let init_p := gs.(es_procs) initiator in
  let my_nbrs := nbrs initiator in
  let new_p := mkProc
                 Active
                 None                    (* initiator has no parent *)
                 (List.length my_nbrs)   (* expect echoes from all neighbors *)
                 [] in
  mkEchoState
    (update_proc gs.(es_procs) initiator new_p)
    (gs.(es_msgs) ++ send_to_all initiator my_nbrs Token).

(* ------------------------------------------------------------------ *)
(** ** 7. Per-node message handler *)

(** Per-node message handler — the core of the algorithm.
    Six cases, two of which are the interesting ones:
      Token / Idle   → become Active, set parent, forward Tokens or echo immediately
      Echo  / Active → decrement pending; if it hits 0, echo parent (or decide if root)
    The remaining four cases (Token/Active, Echo/Idle, Echo/Decided, Token/Decided)
    are either duplicate messages or messages that arrive too late and are dropped. *)
Definition handle_msg (self : node) (gs : echo_state) (pkt : echo_packet)
    : echo_state :=
  let p := gs.(es_procs) self in
  match ep_body pkt, ps_phase p with

  (* ---- Token received by an Idle node --------------------------------- *)
  | Token, Idle =>
      let sender   := ep_src pkt in
      let my_nbrs  := nbrs self in
      (* Neighbors to forward to: all except sender (our new parent). *)
      let forwards := List.filter
                        (fun m => if node_eq m sender then false else true)
                        my_nbrs in
      let pending  := List.length forwards in
      if Nat.eqb pending 0 then
        (* Leaf node: immediately echo back to parent. *)
        let new_p := mkProc Active (Some sender) 0 [] in
        let out   := [mkPkt self sender Echo] in
        mkEchoState
          (update_proc gs.(es_procs) self new_p)
          (gs.(es_msgs) ++ out)
      else
        (* Internal node: forward Token to all non-parent neighbors. *)
        let new_p := mkProc Active (Some sender) pending [] in
        let out   := send_to_all self forwards Token in
        mkEchoState
          (update_proc gs.(es_procs) self new_p)
          (gs.(es_msgs) ++ out)

  (* ---- Token received by an already-Active node (duplicate) ---------- *)
  (* Already-active node receives a duplicate Token: send Echo back to sender. *)
  | Token, Active =>
      let sender := ep_src pkt in
      let out    := [mkPkt self sender Echo] in
      mkEchoState gs.(es_procs) (gs.(es_msgs) ++ out)

  (* ---- Echo received by an Active non-initiator ----------------------- *)
  | Echo, Active =>
      let sender  := ep_src pkt in
      let new_p   := mkProc
                       Active
                       (ps_parent p)
                       (Nat.pred (ps_pending p))
                       (sender :: ps_children p) in
      if Nat.eqb (ps_pending p) 1 then
        (* Last echo: send Echo to parent (if we have one). *)
        match ps_parent p with
        | None =>
            (* We are the initiator — decide. *)
            let decided := mkProc Decided None 0 (ps_children new_p) in
            mkEchoState
              (update_proc gs.(es_procs) self decided)
              gs.(es_msgs)
        | Some par =>
            let out := [mkPkt self par Echo] in
            mkEchoState
              (update_proc gs.(es_procs) self new_p)
              (gs.(es_msgs) ++ out)
        end
      else
        (* Still waiting for more echoes. *)
        mkEchoState
          (update_proc gs.(es_procs) self new_p)
          gs.(es_msgs)

  (* ---- Echo received by Decided / Idle: ignore ----------------------- *)
  | Echo, Decided => gs
  | Echo, Idle    => gs   (* should not happen in a correct execution *)

  (* ---- Token received by Decided: ignore ----------------------------- *)
  | Token, Decided => gs
  end.

(* ------------------------------------------------------------------ *)
(** ** 8. Global step relation *)

(** Remove the first packet equal to [pkt] from the bag.
    We compare src, dst, and body structurally. *)
Fixpoint remove_pkt (pkt : echo_packet) (bag : list echo_packet)
    : list echo_packet :=
  match bag with
  | [] => []
  | hd :: tl =>
      match node_eq (ep_src hd) (ep_src pkt),
            node_eq (ep_dst hd) (ep_dst pkt) with
      | left _, left _ =>
          match ep_body hd, ep_body pkt with
          | Token, Token | Echo, Echo => tl        (* found; remove *)
          | _, _                      => hd :: remove_pkt pkt tl
          end
      | _, _ => hd :: remove_pkt pkt tl
      end
  end.

Inductive echo_label : Type :=
  | ELStart  : echo_label           (* initiator fires the first token wave *)
  | ELDeliver : echo_packet -> echo_label.  (* one packet is delivered *)

Inductive echo_step : echo_state -> echo_label -> echo_state -> Prop :=

  (** The initiator starts the algorithm from the initial quiescent state. *)
  | step_start :
      forall gs,
        ps_phase (gs.(es_procs) initiator) = Idle ->
        echo_step gs ELStart (initiator_start gs)

  (** A packet is delivered to its destination. *)
  | step_deliver :
      forall gs pkt gs',
        In pkt gs.(es_msgs) ->
        gs' = handle_msg (ep_dst pkt)
                         (mkEchoState
                           gs.(es_procs)
                           (remove_pkt pkt gs.(es_msgs)))
                         pkt ->
        echo_step gs (ELDeliver pkt) gs'.

(* ------------------------------------------------------------------ *)
(** ** 9. Initial global state *)

(** Every node starts Idle with no parent and zero pending. *)
Definition initial_proc : proc_state :=
  mkProc Idle None 0 [].

Definition echo_init (gs : echo_state) : Prop :=
  (forall n, gs.(es_procs) n = initial_proc) /\
  gs.(es_msgs) = [].

(* ------------------------------------------------------------------ *)
(** ** 10. The Echo Algorithm LTS *)

Definition echo_LTS : LTS := mkLTS
  echo_state
  echo_label
  echo_init
  echo_step.

End EchoAlgorithm.

(* ------------------------------------------------------------------ *)
(** ** Make [node] implicit in record projections so callers can write
       [gs.(es_procs) n] and [p.(ps_parent)] without supplying the type. *)

Arguments proc_state  {node}.
Arguments mkProc      {node}.
Arguments ps_phase    {node}.
Arguments ps_parent   {node}.
Arguments ps_pending  {node}.
Arguments ps_children {node}.

Arguments echo_packet {node}.
Arguments mkPkt       {node}.
Arguments ep_src      {node}.
Arguments ep_dst      {node}.
Arguments ep_body     {node}.

Arguments echo_state  {node}.
Arguments mkEchoState {node}.
Arguments es_procs    {node}.
Arguments es_msgs     {node}.

Arguments echo_label  {node}.
Arguments ELStart     {node}.
Arguments ELDeliver   {node}.

Arguments initial_proc    {node}.
Arguments update_proc     {node} node_eq.
Arguments nbrs            {node}.
Arguments send_to_all     {node}.
Arguments remove_pkt      {node} node_eq.
Arguments initiator_start {node} node_eq.
Arguments handle_msg      {node} node_eq.
Arguments echo_init       {node}.
Arguments echo_step       {node node_eq initiator all_nodes adj}.
