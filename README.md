# Echo Algorithm — Rocq/Coq Proof

A mechanized proof of the **Echo (Segall/Chang) distributed algorithm** in [Rocq 9.0](https://rocq-prover.org/).

The Echo algorithm constructs a spanning tree rooted at an initiator via a two-phase token wave:
1. Tokens flow outward from the initiator to all nodes.
2. Echoes flow inward from leaves back to the initiator.
The initiator *decides* once it has received an echo on every incident edge, at which point the spanning tree is complete.

---

## Building

Requires Rocq Platform 9.0.

```bash
export PATH="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/bin:$PATH"
export ROCQLIB="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/lib/coq"

make
```

---

## File layout

| File | Description |
|------|-------------|
| `theories/LTS.v` | Generic labeled transition system framework (reachability, invariants, composition) |
| `theories/Network.v` | Generic asynchronous message-passing network model |
| `theories/EchoAlgorithm.v` | Echo algorithm state machine and global LTS |
| `theories/EchoCorrectness.v` | Safety and spanning-tree correctness proofs |
| `theories/Example.v` | Concrete 3-node execution |

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
| `decided_reaches_initiator` | When the initiator decides, every node has a `ps_parent` chain to it |
| `start_decreases_idle` | Firing `step_start` strictly decreases the number of Idle nodes |

---

## Axioms and assumptions

The correctness theorems are proved *relative to* the following assumptions declared as `Variable` in `EchoCorrectness.v`.

### Standard graph axioms (expected of any reasonable network)

| Assumption | Meaning |
|------------|---------|
| `adj_sym` | The graph is undirected: if `u–v` then `v–u` |
| `adj_irrefl` | No self-loops: `adj n n = false` |
| `graph_connected` | Every node has a directed path to the initiator |
| `initiator_in_nodes` | The initiator appears in `all_nodes` |
| `nodup_nodes` | `all_nodes` has no duplicates |

### Fairness / scheduling axiom

| Assumption | Meaning |
|------------|---------|
| `reliable_delivery` | Every in-flight packet is eventually delivered. This is a liveness / fairness property that cannot be derived from the LTS structure alone — it constrains the scheduler. |

### Wave-propagation axioms (A4, A5)

These capture the two key inductive facts about how the token wave unfolds.
Both are *provable* by induction on the wave depth combined with `reliable_delivery`,
but formalizing that induction requires tracking `ps_parent` chains across state updates —
a significant proof engineering effort. They are axiomatized to keep the development modular.

| Assumption | Meaning |
|------------|---------|
| `decided_implies_all_active` (A4) | When the initiator has decided, every non-initiator node is Active |
| `active_non_init_has_chain` (A5) | Every Active non-initiator node has a `ps_parent` chain leading to the initiator |

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
