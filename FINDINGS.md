# Echo Algorithm Coq Proof — Session Findings

## Project layout

| File | Status |
|------|--------|
| `theories/LTS.v` | Complete and compiles |
| `theories/Network.v` | Complete and compiles |
| `theories/EchoAlgorithm.v` | Complete and compiles |
| `theories/EchoCorrectness.v` | **Partially proved — see below** |
| `theories/Example.v` | Complete (concrete 3-node execution) |

Coq binary: `/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/bin/coqc`  
Env needed:  
```
export PATH="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/bin:$PATH"
export ROCQLIB="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/lib/coq"
```

## Current compile error

File: `theories/EchoCorrectness.v`, ~line 411 (shifts after edits).

In `deliver_echo_active`, the `upd_self` rewrite fails in the
`pending = 1`, `parent = Some par` subcase.  After `cbn -[update_proc]`
the goal has `update_proc node_eq f self new_p self` but the goal is
about `parent_is_neighbor`, which asks for `ps_parent` of `new_p` —
the `upd_self` tactic fires too early and finds nothing to rewrite.

**Fix needed**: in that branch, the `parent_is_neighbor` bullet for
`n = self` should use `upd_self` only after introducing `par'` and
`Hpar'`, then simplify `new_p.(ps_parent)` which equals `p.(ps_parent)`.
Concretely change:
```coq
-- subst n. rewrite upd_self. intros par' Hpar'. exact (Hpin self par' Hpar').
```
to something like:
```coq
-- subst n. rewrite upd_self. simpl ps_parent.
   intros par' Hpar'. exact (Hpin self par' Hpar').
```
But the exact fix depends on what `cbn` leaves in the goal context —
**needs interactive inspection in CoqIDE / Proof General**.

## What is already proved

Everything in `INV_holds` except for the two `Admitted` items below:

- `INV_init` — base case ✓  
- `INV_step_start` — invariant preserved by step_start ✓  
- `deliver_token_idle` — Token/Idle handler preserves INV ✓  
- `deliver_token_active` — Token/Active handler preserves INV ✓  
- `deliver_echo_active` — Echo/Active handler preserves INV (compile error, likely fixable) ~  
- `deliver_ignored` — ignored cases preserve INV ✓  
- `INV_step_deliver` — INV preserved by step_deliver ✓  
- `INV_holds` — main invariant theorem ✓  
- Corollaries: `tree_invariant_holds`, `children_are_neighbors_holds`, `valid_packets_holds` ✓  

## Admitted goals remaining

### 1. `decided_reaches_initiator`

```coq
Theorem decided_reaches_initiator :
  forall gs,
    reachable ELts gs ->
    initiator_decided gs ->
    forall n, In n all_nodes -> reaches_initiator gs n.
```

**What it says**: when the initiator has decided, every node has a chain
of `ps_parent` pointers that leads back to the initiator.

**Proof sketch**:  
By induction on the spanning-tree depth induced by the Token wave:
- Depth 0: the initiator itself — trivially `reaches_initiator gs initiator`.
- Depth k+1: node `n` received a Token from some `par` at depth k.
  By `tree_invariant_holds`, `n.(ps_parent) = Some par` and `par` is a neighbor.
  Inductively `reaches_initiator gs par`, so `reaches_initiator gs n` via one more hop.

**Requires**: `graph_connected` (connectivity) + `reliable_delivery` (all Tokens
delivered, so all nodes transition out of Idle) + the already-proved `tree_invariant`.

The hard part in Coq: we need a *depth* measure on the implicit spanning
tree, which requires a well-founded induction.  One approach is induction
on `length (filter Idle all_nodes)` decreasing along the execution.

### 2. `start_decreases_idle`

```coq
Lemma start_decreases_idle gs :
    (proc_of gs initiator).(ps_phase) = Idle ->
    idle_count (initiator_start node_eq initiator all_nodes adj gs)
    < idle_count gs.
```

**What it says**: firing `step_start` removes the initiator from the
Idle count, strictly decreasing `idle_count`.

**Proof sketch**:
1. Show `filter Idle (initiator_start gs)` = `filter Idle gs` with the
   initiator removed (it is now Active).
2. Use `NoDup all_nodes` + `In initiator all_nodes` to conclude the
   filtered list is strictly shorter.

**Requires**: `initiator_in_nodes` + `nodup_nodes`.

## New assumptions added (EchoCorrectness.v)

Three `Variable` declarations were added right after `adj_irrefl`:

| Variable | Type | Why needed |
|----------|------|-----------|
| `graph_connected` | `forall n, In n all_nodes -> adj_path n initiator` | Ensures every node can reach initiator; needed for `decided_reaches_initiator` |
| `initiator_in_nodes` | `In initiator all_nodes` | Lets `idle_count` count initiator; needed for `start_decreases_idle` |
| `nodup_nodes` | `NoDup all_nodes` | Makes `length (filter ...)` arithmetic exact; needed for `start_decreases_idle` |
| `reliable_delivery` | fairness axiom over reachable states | Guarantees Token wave reaches every node; needed for `decided_reaches_initiator` |

The `adj_path` inductive is also defined in the section.

## Suggested next steps (priority order)

1. **Fix the compile error** in `deliver_echo_active` (~line 411).
   Open in CoqIDE, step through the proof, see what the goal looks like
   after `rewrite upd_self` and adjust accordingly.

2. **Prove `start_decreases_idle`** — easier of the two.
   Use `NoDup` list lemmas from `Stdlib.List` (`notin_filter_length` or
   manual induction on `all_nodes`).

3. **Prove `decided_reaches_initiator`** — harder.
   Define a `tree_depth` function or use `adj_path` depth, then
   induct on it.  The `graph_connected` and `reliable_delivery` variables
   are now in scope.
