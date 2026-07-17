# Echo Algorithm — Rocq/Coq Proof

A mechanized proof of decision-time correctness for the **Echo
(Segall/Chang) distributed algorithm** in [Rocq 9.0](https://rocq-prover.org/).

The Echo algorithm constructs a spanning tree rooted at an initiator via a two-phase token wave:
1. Tokens flow outward from the initiator to all nodes.
2. Echoes flow inward from leaves back to the initiator.
The initiator *decides* once it has received an echo on every incident edge.
The main theorem proves that whenever this decision state is reached, the
resulting parent pointers form a complete rooted spanning structure.

---

## Building

Requires Rocq 9.0 and GNU Make. If the Rocq tools are on `PATH`, build with:

```bash
make -j2
```

For an installation whose tools are not on `PATH`, pass its binary and library
directories explicitly. For example, with Rocq Platform 9.0 on macOS:

```bash
make -j2 \
  COQBIN="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/bin" \
  ROCQLIB="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/lib/coq"
```

Run `make clean` with the same optional path arguments to remove generated
proof artifacts. GitHub Actions rebuilds the complete development with Rocq
9.0 on every push and pull request.

---

## File layout

| File | Description |
|------|-------------|
| `theories/LTS.v` | Generic labeled transition system framework (reachability, invariants, composition) |
| `theories/Network.v` | Generic asynchronous message-passing network model |
| `theories/EchoAlgorithm.v` | Echo state machine, `ECHO_CONFIG`, and the `MakeEcho` model functor |
| `theories/EchoCorrectness.v` | `ECHO_CORRECTNESS_CONFIG` and the parameterized correctness functor |
| `theories/Example.v` | Concrete 3-node configuration, model, proof instance, and execution |

---

## Module architecture

`ECHO_CONFIG` specifies the node type, decidable equality, initiator, finite
node list, and adjacency function needed by the algorithm. `MakeEcho(C)` turns
any implementation of that signature into a namespaced transition system.

`ECHO_CORRECTNESS_CONFIG` extends the algorithm signature with symmetry,
irreflexivity, initiator-membership, and no-duplicate obligations.
`MakeEchoCorrectness(C)` checks these obligations once and supplies the complete
invariant and correctness library for that configuration. `Example.v`
demonstrates both functors with `Line3Config`.

The generic transition-system framework remains a `Record`, allowing an LTS to
be passed to ordinary definitions such as `reachable` and `is_invariant`.

---

## What is proved

All results are proved by `Qed` (no `Admitted`).

| Result | Statement |
|--------|-----------|
| `INV_init` | Every initial state satisfies the invariant |
| `INV_step_start` | Invariant preserved by the initiator startup step |
| `deliver_token_idle` | INV preserved when an Idle node receives a Token |
| `deliver_token_active` | INV preserved when an Active node receives a duplicate Token |
| `deliver_echo_active` | INV preserved when an Active node receives an Echo |
| `deliver_ignored` | INV preserved for the three dropped-message cases |
| `INV_step_deliver` | INV preserved by any packet delivery |
| `INV_holds` | INV is an invariant of the Echo LTS |
| `tree_invariant_holds` | Parent pointers stay on real edges; no self-parent; initiator has no parent |
| `children_are_neighbors_holds` | Children lists stay on real edges |
| `valid_packets_holds` | Every in-flight packet travels along an existing edge |
| `parent_in_all_nodes_holds` | Every parent pointer targets a node in `all_nodes` |
| `active_non_init_parent_holds` | Non-initiator nodes in Active always have `ps_parent = Some _` (invariant) |
| `non_init_not_decided_holds` | Non-initiator nodes never reach the Decided phase (invariant) |
| `no_token_idle_decided` | At decision, no in-flight Token targets an Idle node |
| `decided_implies_all_active` | When the initiator decides, every non-initiator node is Active |
| `decided_reaches_initiator` | When the initiator decides, every node has a `ps_parent` chain to it |
| `start_decreases_idle` | Firing `step_start` strictly decreases the number of Idle nodes |

---

## Parameters and assumptions

The development contains no `Axiom`, `Admitted`, or `admit`. Running
`Print Assumptions Echo3Correctness.decided_reaches_initiator` reports `Closed
under the global context`. The algorithm data and graph obligations are fields
of the module signatures; the connectivity certificate remains an explicit
parameter of the two decision-time theorems.

| Parameter or hypothesis | Meaning |
|-------------------------|---------|
| `node` | Abstract type of node identifiers |
| `node_eq` | Decidable equality on nodes |
| `initiator` | Root of the Echo wave |
| `all_nodes` | Finite list of nodes covered by the theorem |
| `adj` | Boolean adjacency test |
| `adj_sym` | The graph is undirected: if `u-v` then `v-u` |
| `adj_irrefl` | No self-loops: `adj n n = false` |
| `initiator_in_nodes` | The initiator appears in `all_nodes` |
| `nodup_nodes` | `all_nodes` has no duplicates |
| `wave_depth` | Natural-valued connectivity certificate; it is not read by the algorithm |
| `wave_depth_props` | The root has depth zero and every listed non-root node has an adjacent listed node of smaller depth |

The parent-chain, one-hop propagation, pending-chain, and
`decided_implies_all_active` results are proved theorems, not additional
assumptions.

### What is not assumed or proved

There is no `reliable_delivery` or fairness premise. The transition relation may
deliver any packet currently in the bag, so the safety theorem covers every
finite delivery order. It does not prove that every execution eventually
decides: a scheduler may stop while packets remain in flight. The current
startup rule also leaves a one-node network Active with pending count zero.

For a guided explanation of the proof and its invariants, see
[`PROOF_EXPLAINED.md`](PROOF_EXPLAINED.md).

## Citation and license

Release metadata is provided in [`CITATION.cff`](CITATION.cff). The source is
available under the [MIT License](LICENSE).

---

## Algorithm model

Each process has:
- `ps_phase ∈ { Idle | Active | Decided }` — lifecycle phase
- `ps_parent : option node` — the neighbor from which the first Token arrived (None for the initiator)
- `ps_pending : nat` — echoes still awaited before echoing the parent (or deciding)
- `ps_children : list node` — neighbors that have echoed back (spanning tree children)

The global LTS has two transition kinds:
- `step_start` — initiator fires once, moving Idle → Active and flooding Tokens to all neighbors
- `step_deliver pkt` — one packet is delivered to its destination, which runs `handle_msg`
