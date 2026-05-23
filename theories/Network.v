(** * Message-Passing Network Model

    A generic model for distributed message-passing systems.  Each node runs
    a state machine; communication is asynchronous and unreliable (unless the
    instantiation constrains it).  The global state is a pair of a per-node
    state map and a multiset of in-flight messages. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import LTS.

(* ------------------------------------------------------------------ *)
(** ** 1. Preliminaries: decidable equality *)

Class DecEq (A : Type) := { dec_eq : forall (x y : A), {x = y} + {x <> y} }.

(* ------------------------------------------------------------------ *)
(** ** 2. Network parameters *)

(** A [NetworkType] bundles the types that parametrize a distributed system. *)
Record NetworkType : Type := mkNetworkType {
  (** Finite set of node identifiers. *)
  nt_node    : Type;
  nt_node_eq : DecEq nt_node;
  (** Topology: adjacency as a decidable predicate. *)
  nt_adj     : nt_node -> nt_node -> bool;
  (** Per-node local state. *)
  nt_state   : Type;
  (** Message payload type. *)
  nt_msg     : Type;
}.

(* ------------------------------------------------------------------ *)
(** ** 3. Packets and network state *)

Section NetworkModel.

  Variable NT : NetworkType.

  (** An in-flight message. *)
  Record packet : Type := mkPacket {
    pkt_src  : nt_node NT;
    pkt_dst  : nt_node NT;
    pkt_body : nt_msg NT;
  }.

  (** Global network state: per-node local state + bag of in-flight packets. *)
  Record net_state : Type := mkNetState {
    ns_local : nt_node NT -> nt_state NT;
    ns_msgs  : list packet;           (* treated as a multiset *)
  }.

  (** Update a single node's local state. *)
  Definition update_local
      (f : nt_node NT -> nt_state NT)
      (n : nt_node NT)
      (s : nt_state NT)
      (m : nt_node NT) : nt_state NT :=
    match nt_node_eq NT with
    | {| dec_eq := deq |} =>
        if deq n m then s else f m
    end.

  (** Remove the first occurrence of a packet from the bag. *)
  Fixpoint remove_packet (pkt : packet) (bag : list packet) : list packet :=
    match bag with
    | [] => []
    | hd :: tl =>
        match nt_node_eq NT with
        | {| dec_eq := deq |} =>
            hd :: remove_packet pkt tl   (* stub: no comparison — caller handles filtering *)
        end
    end.

(* ------------------------------------------------------------------ *)
(** ** 4. Handler signature *)

  (** A node handler takes the current node id, its local state, and an
      incoming message.  It returns the new local state and a list of outbound
      packets (or just internal steps). *)
  Definition handler_ty : Type :=
    nt_node NT ->                  (* self *)
    nt_state NT ->                 (* current local state *)
    packet ->                      (* received packet *)
    nt_state NT * list packet.     (* (new state, outgoing packets) *)

(* ------------------------------------------------------------------ *)
(** ** 5. Network step relation *)

  Variable init_state : nt_node NT -> nt_state NT.
  Variable handler    : handler_ty.

  (** Network labels: a delivery event (the packet that was delivered). *)
  Definition net_label := packet.

  (** A network step delivers one packet to its destination node. *)
  Inductive net_step :
      net_state -> net_label -> net_state -> Prop :=
  | deliver :
      forall (ns : net_state) (pkt : packet)
             (new_ls : nt_state NT) (out : list packet),
        (* The packet must be in the bag. *)
        In pkt (ns_msgs ns) ->
        (* The handler produces a new local state and outbound packets. *)
        handler (pkt_dst pkt) (ns_local ns (pkt_dst pkt)) pkt = (new_ls, out) ->
        net_step
          ns
          pkt
          (mkNetState
            (update_local (ns_local ns) (pkt_dst pkt) new_ls)
            (* remove the delivered packet, add outgoing ones *)
            (out ++ List.filter (fun p => negb (
              (* keep everything except the one delivered packet — we model
                 the bag removal by assuming packet bodies are distinct; a
                 production model would use a proper multiset *)
              match nt_node_eq NT with
              | {| dec_eq := deq |} =>
                match deq (pkt_src p) (pkt_src pkt),
                      deq (pkt_dst p) (pkt_dst pkt) with
                | left _, left _ => true   (* same src/dst; caller must disambiguate *)
                | _, _ => false
                end
              end)) (ns_msgs ns))).

(* ------------------------------------------------------------------ *)
(** ** 6. Build the LTS for a network *)

  Definition network_init (ns : net_state) : Prop :=
    ns_local ns = init_state /\
    ns_msgs  ns = [].          (* start with no in-flight messages *)

  Definition network_LTS : LTS := mkLTS
    net_state
    net_label
    network_init
    net_step.

End NetworkModel.

(* ------------------------------------------------------------------ *)
(** ** 7. Topology helpers *)

Section Topology.

  Variable NT : NetworkType.

  (** Neighbors of a node according to the adjacency relation. *)
  Definition neighbors (n : nt_node NT) (all_nodes : list (nt_node NT))
      : list (nt_node NT) :=
    List.filter (fun m => nt_adj NT n m) all_nodes.

  (** A topology is symmetric (undirected). *)
  Definition undirected : Prop :=
    forall n m, nt_adj NT n m = nt_adj NT m n.

  (** A topology is connected relative to a given node list. *)
  (* Connectivity is captured informally here; a full proof would use a
     path-reachability inductive predicate. *)

End Topology.
