# The Echo Algorithm Proof — Explained for Non-Rocq Readers

> **Who this is for**: software engineers, distributed-systems practitioners, or anyone
> curious about the proof but unfamiliar with Coq/Rocq or formal verification.
> No prior knowledge of proof assistants is assumed.

---

## Table of Contents

1. [The Echo Algorithm — a concrete walkthrough](#1-the-echo-algorithm--a-concrete-walkthrough)
2. [What we proved, in plain English](#2-what-we-proved-in-plain-english)
3. [Why "formally proved" is stronger than tested](#3-why-formally-proved-is-stronger-than-tested)
4. [How the proof is structured](#4-how-the-proof-is-structured)
5. [The invariants, plain English](#5-the-invariants-plain-english)
6. [The pending-chain argument (the hard part)](#6-the-pending-chain-argument-the-hard-part)
7. [Reading Rocq for the first time](#7-reading-rocq-for-the-first-time)
8. [Where to look in the code](#8-where-to-look-in-the-code)

---

## 1. The Echo Algorithm — a concrete walkthrough

### The setting

You have a network of processes connected by links. Think of it as an undirected graph.
One special node — the **initiator** — wants to learn when every node in the network
has been "activated" and to collect a spanning tree rooted at itself.

Each node has a **phase**:

```
Idle  →  Active  →  Decided (initiator only)
```

Messages are either a **Token** (going outward, activating nodes) or an **Echo**
(going inward, reporting back).

### Example: a 5-node ring

```
        I (initiator)
       / \
      A   B
      |   |
      C - D
```

The algorithm runs like this:

**Step 1 — Initiator fires**

```
I becomes Active.
I sends Token to A and B.
I sets pending = 2  (waiting for 2 Echoes).
```

**Step 2 — A receives Token from I**

```
A's phase: Idle → Active
A sets parent = I
A sends Token to C (its only non-parent neighbor).
A sets pending = 1.
```

**Step 3 — B receives Token from I**

```
B's phase: Idle → Active
B sets parent = I
B sends Token to D.
B sets pending = 1.
```

**Step 4 — C receives Token from A**

```
C: Idle → Active,  parent = A
C has neighbor D. It sends Token to D.
C sets pending = 1.
```

**Step 5 — D receives Token from B first**

```
D: Idle → Active,  parent = B
D has neighbors C. It sends Token to C.
D sets pending = 1.
```

**Step 6 — D receives Token from C (duplicate — D is already Active)**

```
D is already Active.
D sends Echo back to C immediately (you already have a parent, I won't be your child).
```

**Step 7 — C receives Token from D (duplicate — C is already Active)**

```
C sends Echo back to D immediately.
```

**Step 8 — C receives Echo from D**

```
C's pending: 1 → 0
C sends Echo to its parent (A).
```

**Step 9 — D receives Echo from C**

```
D's pending: 1 → 0
D sends Echo to its parent (B).
```

**Step 10 — A receives Echo from C**

```
A's pending: 1 → 0
A sends Echo to its parent (I).
```

**Step 11 — B receives Echo from D**

```
B's pending: 1 → 0
B sends Echo to its parent (I).
```

**Step 12 — I receives Echo from A, then from B**

```
I's pending: 2 → 1 → 0
I DECIDES.
```

The resulting spanning tree (the `parent` pointers):
```
C → A → I
D → B → I
```

### What went right

- Every node became Active.
- Every non-initiator node has exactly one parent pointer.
- Following parent pointers from any node eventually reaches the initiator.
- The initiator's pending counter reached zero — it "knows" everyone has reported in.

The proof shows this **always** happens, for **any** connected graph with **any** message ordering.

---

## 2. What we proved, in plain English

The main theorem (`decided_reaches_initiator`) says:

> **If** the initiator has decided (its phase is Decided), **then** every node in the
> network has a chain of parent pointers leading back to the initiator.

In other words: when the algorithm terminates, the spanning tree is complete and correct.

Two supporting theorems:

- **`decided_implies_all_active`**: When the initiator decides, every non-initiator node
  is Active (it got activated and is part of the tree).

- **`start_decreases_idle`**: Each execution step can only decrease the number of Idle
  nodes — the wave always makes progress, never goes backward.

These are proved for **all** possible graphs satisfying:
- The graph is undirected (`adj_sym`)
- No self-loops (`adj_irrefl`)
- There is a BFS-depth function (`wave_depth`) showing the initiator can reach everyone

And for **all** possible message orderings (any interleaving of delivers).

---

## 3. Why "formally proved" is stronger than tested

| Approach | What it checks |
|----------|----------------|
| Unit tests | Specific inputs on specific machines |
| Simulation / model checking | All interleavings up to some bound |
| Paper proof | Human-readable argument; can contain subtle errors |
| **Formal proof (Rocq)** | **All inputs, all interleavings, all graph sizes, machine-verified** |

A formal proof is a **mathematical object** that a computer program (the Rocq kernel,
~3000 lines of OCaml) verifies. If the kernel accepts it, the statement is true —
period. There is no "it works on my machine" or "we only tested graphs up to 10 nodes."

The catch: the theorem is only as strong as its **assumptions** (see `Variable`
declarations in the code). We do assume the graph is connected (via `wave_depth_props`)
and that the system model is accurate (a global bag of in-flight packets, any order of
delivery). Those assumptions are clearly stated and reasonable.

---

## 4. How the proof is structured

The proof is an **inductive invariant proof**, which is the standard technique for
proving properties of concurrent systems.

### The core idea

Instead of reasoning about entire execution histories (which can be infinite), we find
properties **P** such that:

1. **P holds initially** (trivially, because nothing has happened yet).
2. **Every single step preserves P** (if P holds before, it holds after).

If both hold, then P holds after any number of steps — i.e., P holds on every reachable
state. The main theorems then follow from those invariants.

```
Initial state          After 1 step          After 2 steps       ...
   P holds    →  step preserves P  →  step preserves P  →  ...
```

### The five groups of invariants

The proof in `EchoCorrectness.v` is organized into five groups (A–E), each building on
the previous:

```
Group A — Core structural invariants (INV, TSC)
  ├─ Parent pointers are on real graph edges.
  ├─ No node is its own parent.
  ├─ The initiator has no parent.
  └─ Every Active non-initiator has a parent chain to the initiator.

Group B — Token propagation invariants
  ├─ A. Token senders are never Idle.
  ├─ B. Every Active node has either activated its neighbor or has a Token in flight.
  └─ C. A node's parent is always Active or Decided.

Group C — Supporting invariants (proved independently)
  ├─ C1. Packet endpoints are in all_nodes.
  ├─ C2. No mutual parents (no 2-cycles A→parent=B, B→parent=A).
  ├─ C3. Echo senders are never Idle.
  ├─ C4. Idle nodes never appear in children lists.
  ├─ C5. Tokens target non-parent neighbors only.
  ├─ C6. Decided nodes always have pending = 0.
  ├─ C7. At most one copy of each Token exists.
  ├─ C8. Once Active, the activation Token is gone.
  └─ C9. Active node with pending ≥ 1 hasn't sent its Echo yet.

Group D — The pending-chain argument (no_token_idle_decided)
  Proves: when the initiator decides, no in-flight Token targets an Idle node.
  This is the key fact needed to close the "Token in flight" branch in Group B.

Group E — Main theorems (one_hop_active → decided_implies_all_active → decided_reaches_initiator)
```

The arrow of dependency:

```
A (INV, TSC)
    ↓
B (token propagation)   +   D (no idle Token when decided)
    ↓
E (decided ⟹ all Active ⟹ spanning tree complete)
```

---

## 5. The invariants, plain English

### Group A: Structural shape of the tree

**`tree_invariant`**: The parent pointers form a valid forest:
- Every parent pointer follows a real graph edge.
- No node points to itself as parent.
- The initiator has no parent (it's the root).

**`TSC` (Token Source Chain)**: If a node is Active, it has a parent chain reaching the
initiator. Think of it as "every Active node is connected to the root via parent links."

This is the core correctness property, maintained from the very first step.

### Group B: Tokens are "promises" of future activation

**`token_src_not_idle`**: Every Token in the message bag was sent by a non-Idle node.
An Idle node never sends Tokens — so if a Token is in flight, its sender is Active.

**`token_sent_or_notidle`**: For every non-Idle node m and every adjacent node n (that
isn't m's parent), either n is already non-Idle OR there's a Token from m to n in the
bag. This is the invariant that shows the wave is always "making progress."

**`parent_is_active`**: Every node's parent is Active or Decided. You can only become
someone's parent by sending them a Token, and you have to be non-Idle to send Tokens.

### Group C: Bookkeeping correctness

These are "obvious" things that are annoying but necessary to prove:

- **`no_mutual_parent`**: If A's parent is B, then B's parent is not A. (No 2-cycles.)
- **`echo_src_not_idle`**: Echo senders are not Idle. Makes sense — you can only send an
  Echo after receiving a Token, which makes you Active.
- **`token_from_parent_consumed`**: Once you're Active with parent=p, the Token(p→you)
  is no longer in the bag. It was delivered when you became Active.
- **`pending_pos_active`**: If you're Active and still waiting (pending ≥ 1), you haven't
  sent your Echo yet and you're not in your parent's children list yet.

### Group D: The subtle invariant about Idle nodes

**`no_token_idle_decided`**: When the initiator has decided, there is no Token in the
bag whose destination is an Idle node.

**Why this is hard to prove**: Suppose Token(m→n) is in the bag and n is Idle. Then n
hasn't been activated yet. But if the initiator has decided, n must have echoed back at
some point... but wait, n is Idle, so it can't have echoed. This is a contradiction —
but proving it formally requires a careful argument about pending counts propagating up
the parent chain (§6 below).

**Why this matters**: It's needed to close the proof of `one_hop_active`. The Group B
invariant says "n is not Idle OR there's a Token(m→n) in flight." When the initiator
decides, the "Token in flight" option is ruled out by `no_token_idle_decided`, so n must
be non-Idle — i.e., Active.

### Group E: The main theorems

**`one_hop_active`**: If the initiator has decided and m is Active with m adjacent to n
(and n is closer to the root than m in BFS order), then n is Active.

**`decided_implies_all_active`**: By induction on BFS depth: the initiator (depth 0) is
Decided (non-Idle); by `one_hop_active`, every depth-1 node is Active; then every
depth-2 node; and so on.

**`decided_reaches_initiator`**: Every Active node has a parent chain to the initiator
(Group A, TSC). So every node, now Active, has a parent chain to the initiator. ∎

---

## 6. The pending-chain argument (the hard part)

This is the most non-obvious part of the proof, so it gets its own section.

### What we want to prove

**Goal**: When the initiator decides, no Token is targeting an Idle node.

**Why it's hard**: Suppose Token(m→n) is in the bag and n is Idle. We need a
contradiction. n is Idle means n never got any Token, so n never activated, and never
sent any Echo. But if the initiator decided, its pending counter reached 0, meaning it
received all the Echoes it was waiting for. How can it have received all Echoes if
someone in its subtree (the part of the tree that passes through m and n) never echoed?

### The formal argument

The proof goes:

1. **Token(m→n) is in the bag** → m is not Idle (by `token_src_not_idle`).
   So m is Active or Decided. Since only the initiator can be Decided, m is Active
   (if m ≠ initiator) — or m is the initiator.

2. **m is Active** → m's parent is Active or Decided (invariant `parent_is_active`).

3. **m hasn't been added to its parent's children list yet**: Since Token(m→n) is in
   flight, n hasn't echoed to m yet, so m's pending ≥ 1, so m hasn't sent its own Echo
   to its parent yet, so m is not in its parent's children list.

4. **m's parent still has pending ≥ 1**: It hasn't received all its Echoes, and m is
   one that's still missing. (This is the `pending_propagates` lemma: if m is Active
   with pending ≥ 1, then m's parent also has pending ≥ 1.)

5. **Repeat up the parent chain**: Parent's parent also has pending ≥ 1, and so on all
   the way up to the initiator.

6. **The initiator has pending ≥ 1** — but we assumed it decided! Decided means pending
   = 0. Contradiction.

The key technical lemma is `pending_propagates`:
> If m is Active with pending(m) ≥ 1, then m's parent also has pending(parent) ≥ 1.

Its proof uses several of the Group C invariants in concert:
- m ∉ parent's children (from `pending_pos_active`)
- m ∈ parent's forwarding set (from `act_fwds_spec`)
- parent's remaining forwarding targets ≥ 1 (from `remaining_fwds_pos`)
- parent's pending ≥ remaining targets (from `weak_pending_ge_count`)

Each of those required its own inductive proof, making Group D the deepest part of the
proof development.

---

## 7. Reading Rocq for the first time

Rocq (the new name for Coq) is both a programming language and a proof assistant. Here
is a short glossary for reading `EchoCorrectness.v`.

### Declarations

| Rocq syntax | Plain English |
|-------------|---------------|
| `Variable node : Type.` | Abstract type parameter — "node" is some type, we don't know which |
| `Variable adj : node -> node -> bool.` | Abstract function: adjacency predicate |
| `Definition proc_of gs n := gs.(es_procs) n.` | Helper function: look up node n's state |
| `Inductive phase := Idle \| Active \| Decided.` | Enumeration of three values |
| `Record proc_state := mkProc { ps_phase : phase; ps_parent : option node; ... }.` | A struct with named fields |

### Propositions and proofs

| Rocq syntax | Plain English |
|-------------|---------------|
| `Prop` | The type of logical statements |
| `forall n, P n` | "For all n, P(n)" |
| `exists k, P k` | "There exists some k such that P(k)" |
| `A /\ B` | "A and B" |
| `A \/ B` | "A or B" |
| `A -> B` | "A implies B" (also used for function types) |
| `~ P` | "not P" |
| `a = b` | "a equals b" |
| `Lemma foo : P. Proof. ... Qed.` | Proof that statement P is true |
| `Theorem foo : P. Proof. ... Qed.` | Same — just a naming convention for more important results |

### Proof tactics (the commands inside `Proof ... Qed`)

| Tactic | What it does |
|--------|-------------|
| `intros h1 h2.` | Introduce hypotheses; move `forall` variables into the context |
| `destruct x.` | Case-split on x (e.g., if x is `option`, gives `None` and `Some _` cases) |
| `induction n.` | Proof by induction on n |
| `apply lemma.` | Reduce the goal to the premises of `lemma` |
| `exact h.` | The hypothesis `h` directly proves the goal |
| `rewrite h.` | Replace something using the equation `h` |
| `reflexivity.` | Prove `a = a` |
| `discriminate.` | Prove False from an impossible equality (e.g., `Token = Echo`) |
| `contradiction.` | Prove anything from `False` in the context |
| `unfold f.` | Expand the definition of `f` |
| `simpl.` | Simplify by computation |
| `split.` | Split an `A /\ B` goal into two subgoals |
| `left.` / `right.` | Prove `A \/ B` by proving A (or B) |

### Common patterns

**Proving an invariant by induction on executions**:
```
Lemma foo_holds : is_invariant ELts foo.
Proof.
  apply invariant_by_induction.
  - apply foo_base.    (* prove it holds initially *)
  - apply foo_step.    (* prove each step preserves it *)
Qed.
```

**Case-splitting on what just happened**:
```
destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
(* First case:  step_start (initiator just fired) *)
(* Second case: step_deliver (a packet was delivered) *)
```

**Case-splitting on body/phase of a delivered packet**:
```
destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
(* 6 cases: Token/Idle, Token/Active, Token/Decided, Echo/Idle, Echo/Active, Echo/Decided *)
```

### Notation for structured proofs

The `+`, `-`, `*`, `--`, `++` bullets introduce subcases. They're purely visual — they
don't mean anything mathematical, just "here is the proof of this subgoal."

---

## 8. Where to look in the code

Here is a reading order from simplest to most complex.

### Start here

**`theories/EchoAlgorithm.v`** (306 lines)
- The algorithm itself: `handle_msg` (lines 133–204) is the heart. Read this first.
- Each case of the `match` is one message-handling rule.

**`theories/LTS.v`** (~100 lines)
- The generic framework: what `is_invariant`, `reachable`, and `invariant_by_induction`
  mean. Short and worth reading completely.

### Understand the model

**`theories/EchoCorrectness.v`, lines 1–190**
- Section variables: what the proof is parameterized over.
- Definitions of `proc_of`, `INV`, `TSC`, `parent_is_neighbor`, etc.
- Helper lemmas about `update_proc` (lines 81–107): these are the "CRUD" of the proof —
  reading back what you just wrote, not writing what you didn't.

### Follow the main argument

**Group A** (lines ~191–570): `active_non_init_parent`, `non_init_not_decided`, `INV`,
`TSC`. These are the structural invariants. The step proofs are long but mechanical:
case-split on body/phase, most cases are no-ops (`noop_procs_tac`), the interesting
case is Token/Idle.

**Group E** (lines ~6838–6970): `one_hop_active`, `decided_implies_all_active`,
`decided_reaches_initiator`. Read the theorem statements and their one-paragraph
explanations. The proofs are short given the invariants.

**Group D** (lines ~6610–6835): `pending_propagates`, `pending_chain_to_initiator`,
`no_token_idle_decided`. This is the hardest piece. Read the prose comment at lines
19–22 in the file header, then read `pending_propagates` and `pending_chain_to_initiator`
— they are short and have inline comments explaining each step.

### The mega-step lemma

**`token_echo_accounting_step`** (lines ~5343–5997, ~650 lines): The longest proof in
the file. It proves 6 sub-invariants simultaneously (they need each other). You don't
need to read it all — just read the docstring explaining why they're combined, and look
at one case (e.g., the Token/Active case at ~line 5575) to see the pattern.

### The concrete example

**`theories/Example.v`**: A specific 3-node triangle graph where the algorithm is
verified by computation (no `Variable` parameters — actual node names). Good for
intuition.

---

## Summary

The proof establishes that the Echo algorithm is correct on **any** connected undirected
graph, for **any** message ordering. The key steps:

1. Invariants about tree shape (Group A) are proved by simple induction.
2. Invariants about the wave propagation (Group B) are proved using A.
3. A careful counting argument (Group D) shows that if the initiator decided, no Token
   is targeting an Idle node.
4. Putting B and D together (Group E): every adjacent-to-Active node is Active when the
   initiator decides; by connectivity, all nodes are Active.
5. From TSC: every Active node has a parent chain to the initiator — the spanning tree
   is complete.

Total proof size: ~7000 lines of Rocq for a ~300-line algorithm definition.  
Every `Qed` is machine-verified. No `Admitted`. No gaps.
