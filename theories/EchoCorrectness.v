(** * Correctness of the Echo Algorithm

    Main theorem: [decided_reaches_initiator] — when the initiator decides,
    every node has a parent chain to the initiator (the spanning tree is complete).

    Proof roadmap:
    1. [INV_holds]:                 Structural invariants (parent pointers, packet validity).
    2. [TSC_holds]:                 Every active non-initiator traces back to the initiator.
    3. [one_hop_active]:            If m is active and adj m n (m closer), then n is active.
       Proved from three sub-invariants:
         - token_src_not_idle:       Token senders are never idle.
         - token_sent_or_notidle:    Active node m has either activated n, or a Token is in flight.
         - parent_is_active:         A node's parent is always active.
       Plus [no_token_idle_decided]: When the initiator decides, no in-flight Token targets an idle node.
       [no_token_idle_decided] is proved via a pending-chain argument (see §8 below).
    4. [decided_implies_all_active]: Consequence of one_hop_active + connectivity (wave_depth).
    5. [decided_reaches_initiator]:  Combines 4 with TSC.

    §8 — Pending-chain argument for no_token_idle_decided:
    If Token(m→n) is in the bag and n is Idle, then m's pending count >= 1
    (n hasn't echoed back yet).  Propagating up the parent chain shows the
    initiator's pending >= 1, contradicting Decided (which sets pending to 0). *)

From Stdlib Require Import List Arith Bool Arith.Wf_nat Init.Wf Wellfounded.Inverse_Image Lia.
Import ListNotations.
Require Import LTS.
Require Import EchoAlgorithm.

Section EchoCorrectness.

Variable node      : Type.
Variable node_eq   : forall (n m : node), {n = m} + {n <> m}.
Variable initiator : node.
Variable all_nodes : list node.
Variable adj       : node -> node -> bool.

(** Graph assumptions required for correctness. *)
Variable adj_sym    : forall n m, adj n m = true -> adj m n = true.
Variable adj_irrefl : forall n,   adj n n = false.

(** A2. Bookkeeping assumptions on [all_nodes].
    [initiator ∈ all_nodes] is needed so idle_count counts the initiator.
    [NoDup all_nodes] ensures filter / length arithmetic is exact. *)
Variable initiator_in_nodes : In initiator all_nodes.
Variable nodup_nodes        : NoDup all_nodes.

(** Why this helps [start_decreases_idle]:
    idle_count is [length (filter Idle all_nodes)].  With NoDup and
    initiator_in_nodes we can show that removing the initiator from the
    Idle set (it becomes Active after step_start) strictly decreases the
    count. *)

Let ELts   := echo_LTS node node_eq initiator all_nodes adj.
Let EState := @echo_state node.

Definition proc_of (gs : EState) (n : node) : @proc_state node :=
  gs.(es_procs) n.

(* ================================================================== *)
(** ** 1. Helper lemmas *)

(** update_proc: reading back the written slot vs any other slot. *)
Lemma upd_self (f : node -> @proc_state node) n s :
    update_proc node_eq f n s n = s.
Proof.
  unfold update_proc.
  destruct (node_eq n n) as [_ | Hc]; [reflexivity | exact (False_ind _ (Hc eq_refl))].
Qed.

Lemma upd_other (f : node -> @proc_state node) n s m :
    n <> m -> update_proc node_eq f n s m = f m.
Proof.
  intros Hne. unfold update_proc.
  destruct (node_eq n m) as [Heq | _]; [exact (False_ind _ (Hne Heq)) | reflexivity].
Qed.

Lemma upd_eq (f : node -> @proc_state node) n m s :
    n = m -> update_proc node_eq f n s m = s.
Proof. intros ->; apply upd_self. Qed.

(** proc_of a state whose procs = update_proc node_eq f self s. *)
Lemma proc_of_upd (n self : node) (f : node -> @proc_state node)
                  (s : @proc_state node) (msgs : list (@echo_packet node)) :
    proc_of (mkEchoState (update_proc node_eq f self s) msgs) n =
    if node_eq self n then s else f n.
Proof.
  unfold proc_of, update_proc. simpl.
  destruct (node_eq self n); reflexivity.
Qed.

(** Keep cbn/simpl from unfolding update_proc; we drive it via upd_self/upd_other/proc_of_upd. *)
Local Opaque update_proc.

(** A packet in remove_pkt's output was in the original bag. *)
Lemma remove_pkt_in (pkt : @echo_packet node) bag pkt' :
    In pkt' (remove_pkt node_eq pkt bag) -> In pkt' bag.
Proof.
  induction bag as [| hd tl IH]; intro Hin; [contradiction |].
  simpl in Hin.
  destruct (node_eq (ep_src hd) (ep_src pkt)) as [Esrc | Nsrc];
  destruct (node_eq (ep_dst hd) (ep_dst pkt)) as [Edst | Ndst].
  - (* src and dst match — check body *)
    destruct (ep_body hd) eqn:Hbh; destruct (ep_body pkt) eqn:Hbp.
    + (* Token/Token: hd removed, result = tl, Hin : In pkt' tl *)
      right. exact Hin.
    + (* Token/Echo: hd kept *)
      simpl in Hin. destruct Hin as [<- | H]; [left; reflexivity | right; exact (IH H)].
    + (* Echo/Token: hd kept *)
      simpl in Hin. destruct Hin as [<- | H]; [left; reflexivity | right; exact (IH H)].
    + (* Echo/Echo: hd removed, result = tl *)
      right. exact Hin.
  - simpl in Hin. destruct Hin as [<- | H]; [left; reflexivity | right; exact (IH H)].
  - simpl in Hin. destruct Hin as [<- | H]; [left; reflexivity | right; exact (IH H)].
  - simpl in Hin. destruct Hin as [<- | H]; [left; reflexivity | right; exact (IH H)].
Qed.

(** A node is in nbrs iff adj holds. *)
Lemma nbrs_adj n m : In m (nbrs all_nodes adj n) -> adj n m = true.
Proof.
  unfold nbrs. intro H. apply filter_In in H. exact (proj2 H).
Qed.

(** send_to_all packets come from src, go to one of dsts, with msg body. *)
Lemma send_to_all_inv (src : node) (dsts : list node) (msg : echo_msg)
                      (pkt : @echo_packet node) :
    In pkt (send_to_all src dsts msg) ->
    ep_src pkt = src /\ In (ep_dst pkt) dsts /\ ep_body pkt = msg.
Proof.
  unfold send_to_all. intro Hin.
  apply in_map_iff in Hin as [dst [<- Hdst]].
  simpl. auto.
Qed.

(** filter is a sub-list of the original. *)
Lemma filter_subset {A} (f : A -> bool) l x :
    In x (filter f l) -> In x l.
Proof.
  intro H. apply filter_In in H. exact (proj1 H).
Qed.

(* ================================================================== *)
(** ** 1b. Parent-pointer invariant for non-initiators *)

(** If a non-initiator node is Active in a reachable state, its
    ps_parent is set to Some _. This follows because the only way to
    become Active is via Token/Idle, which sets ps_parent = Some sender. *)
Definition active_non_init_parent (gs : EState) : Prop :=
  forall n, n <> initiator ->
    (proc_of gs n).(ps_phase) = Active ->
    exists par, (proc_of gs n).(ps_parent) = Some par.

Lemma active_non_init_parent_base : forall gs, lts_init ELts gs -> active_non_init_parent gs.
Proof.
  intros gs [Hproc Hmsgs] n Hne Hph.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma active_non_init_parent_step gs lbl gs' :
    active_non_init_parent gs ->
    lts_trans ELts gs lbl gs' ->
    active_non_init_parent gs'.
Proof.
  intros IH Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - (* step_start: gs' = initiator_start node_eq initiator all_nodes adj gs0
       For n ≠ initiator, proc_of gs' n = proc_of gs0 n. *)
    intros n Hne Hph.
    assert (Heqn : proc_of (initiator_start node_eq initiator all_nodes adj gs0) n =
                   proc_of gs0 n).
    { unfold proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro Heq; exact (Hne (eq_sym Heq))]. }
    rewrite Heqn in Hph. rewrite Heqn.
    exact (IH n Hne Hph).
  - (* step_deliver: gs0' = handle_msg self gs_mid pkt *)
    subst gs0'.
    set (self := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    (* Use the same structure as INV_step_deliver *)
    intros n Hne Hph.
    (* Use proc_of_upd by rewriting Hph into the canonical form.
       First, establish what proc_of gs' n equals. *)
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    fold gs' in Hph.
    (* Now case-split on body/phase to determine gs' *)
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    (* Token / Idle: self becomes Active with parent = Some sender'.
       Key facts: (1) proc_of gs' self has ps_parent = Some sender',
                  (2) proc_of gs' m = proc_of gs0 m for m ≠ self. *)
    + set (sender' := ep_src pkt).
      (* Fact 1: proc_of gs' n = proc_of gs0 n for n ≠ self *)
      assert (Hother : forall m, m <> self ->
                proc_of gs' m = proc_of gs0 m).
      { intros m Hmne.
        unfold gs', proc_of, handle_msg.
        change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        (* After rewriting, goal is about the Token/Idle branch.
           The condition is (length (filter ...) =? 0).  We destruct on this. *)
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro Heqsm; exact (Hmne (eq_sym Heqsm)). }
      (* Fact 2: (proc_of gs' self).(ps_parent) = Some sender' *)
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender').
      { unfold gs', proc_of, handle_msg.
        change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      (* Now case-split on n = self vs n ≠ self *)
      destruct (node_eq self n) as [Heqs | Hnes].
      * (* n = self *)
        subst n. exists sender'. exact Hself_par.
      * (* n ≠ self: use IH *)
        assert (Hmne' : n <> self) by (intro H; exact (Hnes (eq_sym H))).
        rewrite (Hother n Hmne') in Hph.
        destruct (IH n Hne Hph) as [par' Hpar'].
        exists par'. rewrite (Hother n Hmne'). exact Hpar'.
    (* Token / Active: gs'.(es_procs) = es_procs gs0 *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (IH n Hne Hph).
    (* Token / Decided: gs'.(es_procs) = es_procs gs0 *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (IH n Hne Hph).
    (* Echo / Idle: gs'.(es_procs) = es_procs gs0 *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (IH n Hne Hph).
    (* Echo / Active: three sub-cases on pending and parent *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar.
        -- (* pending=1, parent=Some par: self stays Active, parent unchanged *)
           set (new_p := mkProc Active (Some par) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold new_p. rewrite Hpeq. reflexivity. }
           rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
           rewrite Hgs'eq. rewrite proc_of_upd.
           destruct (node_eq self n) as [Heqs | Hnes].
           ++ simpl in Hph. simpl. exists par. reflexivity.
           ++ exact (IH n Hne Hph).
        -- (* pending=1, parent=None: self decides — n = self → Decided → discriminate *)
           set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold decided. rewrite Hpeq. reflexivity. }
           rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
           rewrite Hgs'eq. rewrite proc_of_upd.
           destruct (node_eq self n) as [Heqs | Hnes].
           ++ simpl in Hph. discriminate.
           ++ exact (IH n Hne Hph).
      * (* pending≠1: self stays Active, parent unchanged *)
        set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
        rewrite Hgs'eq. rewrite proc_of_upd.
        destruct (node_eq self n) as [Heqs | Hnes].
        -- simpl in Hph.
           assert (Hself_act : (proc_of gs0 self).(ps_phase) = Active).
           { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
           assert (Hself_ne : self <> initiator).
           { rewrite Heqs. exact Hne. }
           destruct (IH self Hself_ne Hself_act) as [par' Hpar'].
           unfold proc_of in Hpar'. rewrite <- Hpeq in Hpar'.
           simpl. unfold new_p. simpl. exists par'. exact Hpar'.
        -- exact (IH n Hne Hph).
    (* Echo / Decided: gs'.(es_procs) = es_procs gs0 *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (IH n Hne Hph).
Qed.

Lemma active_non_init_parent_holds : is_invariant ELts active_non_init_parent.
Proof.
  apply invariant_by_induction.
  - apply active_non_init_parent_base.
  - intros gs lbl gs' Hinv Hstep.
    exact (active_non_init_parent_step gs lbl gs' Hinv Hstep).
Qed.

(* ================================================================== *)
(** ** 1c. Non-initiator never decides *)

(** A non-initiator node is never in the Decided phase in any reachable state.
    Proof: by invariant induction.
    - Init: all nodes start Idle ≠ Decided.
    - Step: the only way to reach Decided is via Echo/Active with pending=1 and parent=None
      (the "self decides" branch of handle_msg).  But active_non_init_parent_holds ensures
      non-initiators in Active always have a parent, so parent=None can only happen for
      the initiator.  Therefore the Decided branch is unreachable for non-initiators. *)
Definition non_init_not_decided (gs : EState) : Prop :=
  forall n, n <> initiator -> (proc_of gs n).(ps_phase) <> Decided.

Lemma non_init_not_decided_base : forall gs, lts_init ELts gs -> non_init_not_decided gs.
Proof.
  intros gs [Hproc _] n _ Hph.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma non_init_not_decided_step gs lbl gs' :
    non_init_not_decided gs ->
    active_non_init_parent gs ->
    lts_trans ELts gs lbl gs' ->
    non_init_not_decided gs'.
Proof.
  intros IH Hanip Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - (* step_start: only initiator changes phase Idle→Active *)
    intros n Hne Hdec.
    assert (Heqn : proc_of (initiator_start node_eq initiator all_nodes adj gs0) n =
                   proc_of gs0 n).
    { unfold proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    rewrite Heqn in Hdec. exact (IH n Hne Hdec).
  - (* step_deliver *)
    subst gs0'.
    set (self := ep_dst pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros n Hne Hdec.
    fold gs' in Hdec.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    (* Token / Idle: both branches update self to Active, not Decided *)
    + (* Token/Idle: self becomes Active regardless of leaf/internal *)
      (* Both branches of handle_msg set self to Active, not Decided. *)
      assert (Hother : forall m, m <> self ->
                proc_of gs' m = proc_of gs0 m).
      { intros m Hmne.
        unfold gs', proc_of, handle_msg.
        change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        destruct (Nat.eqb (length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                          (nbrs all_nodes adj self))) 0);
        simpl es_procs; apply upd_other; intro H; exact (Hmne (eq_sym H)). }
      assert (Hself_active : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg.
        change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        destruct (Nat.eqb (length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                          (nbrs all_nodes adj self))) 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      destruct (node_eq self n) as [Heqs | Hnes].
      * (* n = self *)
        subst n. rewrite Hself_active in Hdec. discriminate.
      * (* n ≠ self *)
        rewrite (Hother n (fun H => Hnes (eq_sym H))) in Hdec.
        exact (IH n Hne Hdec).
    (* Token / Active: procs unchanged (only msgs) *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec. exact (IH n Hne Hdec).
    (* Token / Decided: gs' = gs_mid, procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec. exact (IH n Hne Hdec).
    (* Echo / Idle: gs' = gs_mid, procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec. exact (IH n Hne Hdec).
    (* Echo / Active: three sub-cases *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar.
        -- (* pending=1, parent=Some par: self stays Active *)
           assert (Hgs'_procs : es_procs gs' = update_proc node_eq (es_procs gs0) self
                     (mkProc Active (Some par) (Nat.pred (ps_pending p)) (ep_src pkt :: ps_children p))).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. rewrite Hpeq. reflexivity. }
           unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec.
           destruct (node_eq self n) as [Heqs | Hnes].
           ++ rewrite upd_eq in Hdec; [| exact Heqs]. simpl in Hdec. discriminate.
           ++ rewrite (upd_other _ _ _ _ Hnes) in Hdec. exact (IH n Hne Hdec).
        -- (* pending=1, parent=None: ONLY initiator can have parent=None *)
           (* self must be initiator: by active_non_init_parent, if self ≠ initiator and
              self is Active, then self has Some parent.  But Hpar says parent=None.
              So self = initiator. *)
           assert (Hself_init : self = initiator).
           { destruct (node_eq self initiator) as [Heq | Hse]; [exact Heq |].
             (* self ≠ initiator and self is Active: Hanip gives Some parent *)
             assert (Hact : (proc_of gs0 self).(ps_phase) = Active).
             { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
             destruct (Hanip self Hse Hact) as [par' Hpar'].
             unfold proc_of in Hpar'. rewrite <- Hpeq in Hpar'.
             rewrite Hpar in Hpar'. discriminate. }
           (* self = initiator decides: only self's state changes to Decided *)
           assert (Hgs'_procs : es_procs gs' = update_proc node_eq (es_procs gs0) self
                     (mkProc Decided None 0 (ep_src pkt :: ps_children p))).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. rewrite Hpeq. reflexivity. }
           unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec.
           destruct (node_eq self n) as [Heqs | Hnes].
           ++ (* n = self = initiator: contradicts Hne *)
              rewrite Hself_init in Heqs. exact (Hne (eq_sym Heqs)).
           ++ rewrite (upd_other _ _ _ _ Hnes) in Hdec. exact (IH n Hne Hdec).
      * (* pending ≠ 1: self stays Active *)
        assert (Hgs'_procs : es_procs gs' = update_proc node_eq (es_procs gs0) self
                   (mkProc Active (ps_parent p) (Nat.pred (ps_pending p)) (ep_src pkt :: ps_children p))).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
        unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec.
        destruct (node_eq self n) as [Heqs | Hnes].
        -- rewrite upd_eq in Hdec; [| exact Heqs]. simpl in Hdec. discriminate.
        -- rewrite (upd_other _ _ _ _ Hnes) in Hdec. exact (IH n Hne Hdec).
    (* Echo / Decided: gs' = gs_mid, procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in Hdec. rewrite Hgs'_procs in Hdec. exact (IH n Hne Hdec).
Qed.

Theorem non_init_not_decided_holds : is_invariant ELts non_init_not_decided.
Proof.
  (* Prove the conjunction with active_non_init_parent as a combined invariant,
     then project. *)
  assert (Hcombined : is_invariant ELts (fun gs => non_init_not_decided gs /\ active_non_init_parent gs)).
  { apply invariant_by_induction.
    - intros gs Hi. split; [apply non_init_not_decided_base | apply active_non_init_parent_base]; exact Hi.
    - intros gs lbl gs' [Hnind Hanip] Hstep. split.
      + exact (non_init_not_decided_step gs lbl gs' Hnind Hanip Hstep).
      + exact (active_non_init_parent_step gs lbl gs' Hanip Hstep). }
  intros gs Hr. exact (proj1 (Hcombined gs Hr)).
Qed.

(* ================================================================== *)
(** ** 2. Invariants *)

Definition parent_is_neighbor (gs : EState) : Prop :=
  forall n par, (proc_of gs n).(ps_parent) = Some par -> adj n par = true.

Definition no_self_parent (gs : EState) : Prop :=
  forall n, (proc_of gs n).(ps_parent) <> Some n.

Definition initiator_no_parent (gs : EState) : Prop :=
  (proc_of gs initiator).(ps_parent) = None.

Definition tree_invariant (gs : EState) : Prop :=
  parent_is_neighbor gs /\ no_self_parent gs /\ initiator_no_parent gs.

Definition children_are_neighbors (gs : EState) : Prop :=
  forall n child, In child (proc_of gs n).(ps_children) -> adj n child = true.

(** Every in-flight packet travels along an existing edge (src -> dst). *)
Definition valid_packets (gs : EState) : Prop :=
  forall pkt, In pkt gs.(es_msgs) -> adj (ep_src pkt) (ep_dst pkt) = true.

(** Before step_start fires, the bag is empty — so the initiator can never
    receive a Token while still Idle. *)
Definition init_idle_empty (gs : EState) : Prop :=
  (proc_of gs initiator).(ps_phase) = Idle -> gs.(es_msgs) = [].

(** Combined invariant — all four properties must be proved together
    because they form a closed inductive set: each preservation case
    needs one or more of the others.  For example, proving valid_packets
    is preserved by the Token/Idle handler requires adj_sym (from the
    graph assumptions) plus the fact that the packet arrived along an
    existing edge (from valid_packets in the pre-state). *)
Definition INV (gs : EState) : Prop :=
  tree_invariant gs /\ children_are_neighbors gs /\
  valid_packets gs /\ init_idle_empty gs.

(* ================================================================== *)
(** ** 3. Base case *)

(** Base case: every initial state (all Idle, empty bag) trivially satisfies INV.
    All parent/children fields are vacuously empty, so every ∀-quantified
    condition holds without needing any proof work. *)
Lemma INV_init : forall gs, lts_init ELts gs -> INV gs.
Proof.
  intros gs [Hproc Hmsgs].
  unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
         initiator_no_parent, children_are_neighbors, valid_packets,
         init_idle_empty, proc_of.
  repeat split.
  - intros n par. rewrite Hproc. simpl. discriminate.
  - intros n.     rewrite Hproc. simpl. discriminate.
  - rewrite Hproc. simpl. reflexivity.
  - intros n child. rewrite Hproc. simpl. contradiction.
  - intros pkt. rewrite Hmsgs. simpl. contradiction.
  - intros _. exact Hmsgs.
Qed.

(* ================================================================== *)
(** ** 4. Preservation — step_start *)

(** step_start fires exactly once: the initiator moves Idle → Active and
    sends Tokens to all neighbors.  Key obligations:
    - parent_is_neighbor: initiator's new parent is None (no case to check);
      all other nodes unchanged.
    - init_idle_empty: initiator is now Active, so the hypothesis (Idle)
      is false — the obligation vacuously holds. *)
Lemma INV_step_start gs :
    INV gs ->
    ps_phase (gs.(es_procs) initiator) = Idle ->
    INV (initiator_start node_eq initiator all_nodes adj gs).
Proof.
  intros [Htree [Hchn [Hvpkt Hidle]]] Hph.
  destruct Htree as [Hpin [Hself Hinop]].
  unfold initiator_start.
  set (my_nbrs := nbrs all_nodes adj initiator).
  set (new_p   := mkProc Active None (length my_nbrs) []).
  set (gs'     := mkEchoState (update_proc node_eq (es_procs gs) initiator new_p)
                              (es_msgs gs ++ send_to_all initiator my_nbrs Token)).
  unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
         initiator_no_parent, children_are_neighbors, valid_packets,
         init_idle_empty, proc_of; cbn -[update_proc].
  repeat split.

  (* parent_is_neighbor *)
  - intros n par Hpar.
    destruct (node_eq initiator n) as [Heq | Hne].
    + subst. rewrite upd_self in Hpar. simpl in Hpar. discriminate.
    + rewrite (upd_other _ _ _ _ Hne) in Hpar. exact (Hpin n par Hpar).

  (* no_self_parent *)
  - intros n Hcontra.
    destruct (node_eq initiator n) as [Heq | Hne].
    + subst. rewrite upd_self in Hcontra. simpl in Hcontra. discriminate.
    + rewrite (upd_other _ _ _ _ Hne) in Hcontra. exact (Hself n Hcontra).

  (* initiator_no_parent *)
  - rewrite upd_self. simpl. reflexivity.

  (* children_are_neighbors *)
  - intros n child Hchild.
    destruct (node_eq initiator n) as [Heq | Hne].
    + subst. rewrite upd_self in Hchild. simpl in Hchild. contradiction.
    + rewrite (upd_other _ _ _ _ Hne) in Hchild. exact (Hchn n child Hchild).

  (* valid_packets *)
  - intros pkt Hin.
    apply in_app_iff in Hin as [Hold | Hnew].
    + exact (Hvpkt pkt Hold).
    + apply send_to_all_inv in Hnew as [Hsrc [Hdst Hbody]].
      rewrite Hsrc. apply nbrs_adj. exact Hdst.

  (* init_idle_empty: initiator is now Active, so hypothesis is false *)
  - intro Hph'. rewrite upd_self in Hph'. simpl in Hph'. discriminate.
Qed.

(* ================================================================== *)
(** ** 5. Preservation — step_deliver, per handler case *)

(** We factor out the key argument: for any node [n], its process state
    in [gs'] either equals [new_p] (if [n = self]) or equals [gs.(es_procs) n]. *)

(** Tactic-level helper: resolve [update_proc] at [self] vs [n]. *)
Ltac upd_self_in_hyps self :=
  repeat match goal with
  | H : context [update_proc node_eq ?f self ?s self] |- _ =>
      rewrite (upd_self f self s) in H
  end;
  try match goal with
  | |- context [update_proc node_eq ?f self ?s self] =>
      rewrite (upd_self f self s)
  end.

Ltac upd_other_in_hyps self n Hne :=
  repeat match goal with
  | H : context [update_proc node_eq ?f self ?s n] |- _ =>
      rewrite (upd_other f self s n Hne) in H
  end;
  try match goal with
  | |- context [update_proc node_eq ?f self ?s n] =>
      rewrite (upd_other f self s n Hne)
  end.

Ltac upd_case self n :=
  destruct (node_eq self n) as [Heq | Hne];
  [ subst n; upd_self_in_hyps self
  | upd_other_in_hyps self n Hne ].

(* ------------------------------------------------------------------ *)
(** 5a. Token received by Idle node *)

(** Token received by an Idle node — the main inductive step of the wave.
    Self goes Idle → Active and sets parent = Some sender.
    Two subcases depending on whether self is a leaf (pending = 0) or
    internal (pending > 0); in both cases parent = Some sender, so
    parent_is_neighbor reduces to adj_sym applied to the incoming edge. *)
Lemma deliver_token_idle gs self sender body pkt :
    pkt = mkPkt sender self body ->
    ep_body pkt = Token ->
    (proc_of gs self).(ps_phase) = Idle ->
    INV gs ->
    In pkt gs.(es_msgs) ->
    let gs0   := mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs)) in
    let gs'   := handle_msg node_eq all_nodes adj self gs0 pkt in
    INV gs'.
Proof.
  intros Hpkt Hbody Hphase [Htree [Hchn [Hvpkt Hidle]]] Hin.
  destruct Htree as [Hpin [Hself Hinop]].
  subst pkt. simpl ep_src. simpl ep_dst. simpl ep_body.
  (* adj sender self from valid_packets *)
  assert (Hadj_s_self : adj sender self = true) by (exact (Hvpkt _ Hin)).
  (* adj self sender from symmetry *)
  assert (Hadj_self_s : adj self sender = true) by (apply adj_sym; exact Hadj_s_self).
  (* sender ≠ self: adj self self = false but adj self sender = true *)
  assert (Hsne : sender <> self).
  { intro Heq. subst. rewrite adj_irrefl in Hadj_self_s. discriminate. }
  (* self ≠ initiator: because initiator's phase is Idle => msgs = [],
     but pkt is in msgs, so msgs ≠ [] => initiator phase ≠ Idle.
     Combined with Hphase (self is Idle), if self = initiator then
     initiator is Idle and msgs ≠ [], contradicting Hidle. *)
  assert (Hself_not_init : self <> initiator).
  { intro Heq. subst.
    unfold init_idle_empty, proc_of in Hidle.
    assert (Hempty := Hidle Hphase).
    rewrite Hempty in Hin. contradiction. }
  (* unfold handle_msg for Token/Idle *)
  unfold handle_msg, proc_of in *. cbn -[update_proc] in *.
  subst body. (* reduce match body with after cbn gives Hbody : body = Token *)
  rewrite Hphase. (* ps_phase p = Idle *)
  (* case split on whether the node is a leaf *)
  set (my_nbrs := nbrs all_nodes adj self).
  set (forwards := filter (fun m => if node_eq m sender then false else true) my_nbrs).
  set (pending := length forwards).
  (* We prove INV for both sub-cases (leaf / internal) *)
  destruct (Nat.eqb pending 0) eqn:Hpend.
  - (* leaf: sends Echo back, new_p has parent = Some sender, pending = 0 *)
    set (new_p := mkProc Active (Some sender) 0 []).
    unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
           initiator_no_parent, children_are_neighbors, valid_packets,
           init_idle_empty, proc_of; cbn -[update_proc]; repeat split.
    + intros n par Hpar.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self in Hpar. cbn in Hpar.
        injection Hpar as <-. exact Hadj_self_s.
      * rewrite (upd_other _ _ _ _ Hne) in Hpar. exact (Hpin n par Hpar).
    + intros n Hcontra.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self in Hcontra. cbn in Hcontra.
        injection Hcontra as Heq. exact (Hsne Heq).
      * rewrite (upd_other _ _ _ _ Hne) in Hcontra. exact (Hself n Hcontra).
    + rewrite (upd_other _ _ _ _ Hself_not_init). exact Hinop.
    + intros n child Hchild.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self in Hchild. cbn in Hchild. contradiction.
      * rewrite (upd_other _ _ _ _ Hne) in Hchild. exact (Hchn n child Hchild).
    + intros pkt' Hin'.
      apply in_app_iff in Hin' as [Hold | Hnew].
      * apply (Hvpkt pkt'). exact (remove_pkt_in _ _ _ Hold).
      * destruct Hnew as [<- | []]. simpl. exact Hadj_self_s.
    + rewrite (upd_other _ _ _ _ Hself_not_init).
      intro Hph. apply Hidle in Hph. rewrite Hph in Hin. contradiction.
  - (* internal: forwards Token, new_p has parent = Some sender *)
    set (new_p := mkProc Active (Some sender) pending []).
    set (out   := send_to_all self forwards Token).
    unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
           initiator_no_parent, children_are_neighbors, valid_packets,
           init_idle_empty, proc_of; cbn -[update_proc]; repeat split.
    + intros n par Hpar.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self in Hpar. cbn in Hpar.
        injection Hpar as <-. exact Hadj_self_s.
      * rewrite (upd_other _ _ _ _ Hne) in Hpar. exact (Hpin n par Hpar).
    + intros n Hcontra.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self in Hcontra. cbn in Hcontra.
        injection Hcontra as Heq. exact (Hsne Heq).
      * rewrite (upd_other _ _ _ _ Hne) in Hcontra. exact (Hself n Hcontra).
    + rewrite (upd_other _ _ _ _ Hself_not_init). exact Hinop.
    + intros n child Hchild.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self in Hchild. cbn in Hchild. contradiction.
      * rewrite (upd_other _ _ _ _ Hne) in Hchild. exact (Hchn n child Hchild).
    + intros pkt' Hin'.
      apply in_app_iff in Hin' as [Hold | Hnew].
      * apply (Hvpkt pkt'). exact (remove_pkt_in _ _ _ Hold).
      * apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
        rewrite Hsrc.
        apply nbrs_adj.
        exact (filter_subset _ _ _ Hdst).
    + intros Hph.
      rewrite (upd_other _ _ _ _ Hself_not_init) in Hph.
      unfold init_idle_empty, proc_of in Hidle.
      apply Hidle in Hph. rewrite Hph in Hin. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(** 5b. Token received by Active node (duplicate — already has parent) *)

(** Token received by an Active node (duplicate delivery).
    The handler sends a single Echo back but does NOT change any process state,
    so all parts of INV that concern proc states are immediate from the IH.
    Only valid_packets needs work: the new Echo travels along adj self sender
    which equals adj sender self (by adj_sym) = true from the incoming Token. *)
Lemma deliver_token_active gs self sender pkt :
    ep_src pkt = sender -> ep_dst pkt = self -> ep_body pkt = Token ->
    (proc_of gs self).(ps_phase) = Active ->
    INV gs ->
    In pkt gs.(es_msgs) ->
    INV (handle_msg node_eq all_nodes adj self
          (mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs)))
          pkt).
Proof.
  intros Hsrc Hdst Hbody Hphase [Htree [Hchn [Hvpkt Hidle]]] Hin.
  destruct Htree as [Hpin [Hself Hinop]].
  assert (Hadj_s_self : adj sender self = true).
  { rewrite <- Hsrc, <- Hdst. exact (Hvpkt pkt Hin). }
  assert (Hadj_self_s : adj self sender = true) by (apply adj_sym; exact Hadj_s_self).
  unfold handle_msg, proc_of in *. rewrite Hbody. simpl. rewrite Hphase.
  (* gs' = mkEchoState gs.(es_procs) (old_bag ++ [mkPkt self sender Echo]) *)
  unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
         initiator_no_parent, children_are_neighbors, valid_packets,
         init_idle_empty, proc_of; simpl; repeat split.
  - exact Hpin.
  - exact Hself.
  - exact Hinop.
  - exact Hchn.
  - intros pkt' Hin'.
    apply in_app_iff in Hin' as [Hold | Hnew].
    + exact (Hvpkt _ (remove_pkt_in _ _ _ Hold)).
    + destruct Hnew as [<- | []]. simpl. rewrite Hsrc. exact Hadj_self_s.
  - unfold init_idle_empty, proc_of in Hidle.
    intros Hph. apply Hidle in Hph.
    rewrite Hph in Hin. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(** 5c. Echo received by Active node *)

(** Echo received by an Active node — the return wave.
    Three sub-subcases: pending > 1 (still waiting), pending = 1 with parent
    (forward Echo to parent, stay Active), and pending = 1 without parent
    (this is the initiator — decide).  The most delicate case is
    pending = 1 / parent = None: we must show initiator_no_parent is
    preserved, which requires ruling out self ≠ initiator by contradiction
    (if self ≠ initiator and parent = None then Hinop gives a contradiction). *)
Lemma deliver_echo_active gs self sender pkt :
    ep_src pkt = sender -> ep_dst pkt = self -> ep_body pkt = Echo ->
    (proc_of gs self).(ps_phase) = Active ->
    INV gs ->
    In pkt gs.(es_msgs) ->
    INV (handle_msg node_eq all_nodes adj self
          (mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs)))
          pkt).
Proof.
  intros Hsrc Hdst Hbody Hphase [Htree [Hchn [Hvpkt Hidle]]] Hin.
  destruct Htree as [Hpin [Hself Hinop]].
  assert (Hadj_s_self : adj sender self = true).
  { rewrite <- Hsrc, <- Hdst. exact (Hvpkt pkt Hin). }
  assert (Hadj_self_s : adj self sender = true) by (apply adj_sym; exact Hadj_s_self).
  (* Unfold handle_msg and normalize the goal *)
  unfold handle_msg, proc_of in *.
  rewrite Hbody. cbn -[update_proc] in *. rewrite Hphase.
  (* Now the goal has:
       INV (if ps_pending (es_procs gs self) =? 1 then
              match ps_parent (es_procs gs self) with
              | Some par => mkEchoState (update_proc ... self new_p) (msgs ++ echo)
              | None     => mkEchoState (update_proc ... self decided) msgs
              end
            else
              mkEchoState (update_proc ... self new_p) msgs)
     Destruct on the condition to expose the concrete state. *)
  destruct (Nat.eqb (ps_pending (es_procs gs self)) 1) eqn:Hone.
  - (* pending = 1: if-true simplifies *)
    simpl.
    destruct (ps_parent (es_procs gs self)) as [par |] eqn:Hpar.
    + (* non-initiator: sends Echo to parent par *)
      assert (Hpar_adj : adj self par = true).
      { apply (Hpin self par). exact Hpar. }
      set (new_p := mkProc Active (Some par)
                           (Nat.pred (ps_pending (es_procs gs self)))
                           (ep_src pkt :: ps_children (es_procs gs self))).
      unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
             initiator_no_parent, children_are_neighbors, valid_packets,
             init_idle_empty, proc_of; cbn -[update_proc]; repeat split.
      * intro n. intro par'.
        destruct (node_eq self n) as [Heq | Hne].
        -- subst n. rewrite upd_self. simpl. intro H. injection H as <-. exact Hpar_adj.
        -- rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hpin n par' H).
      * intro n.
        destruct (node_eq self n) as [Heq | Hne].
        -- subst n. rewrite upd_self. simpl. intro H. injection H as <-.
           rewrite adj_irrefl in Hpar_adj. discriminate.
        -- rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hself n H).
      * destruct (node_eq self initiator) as [Heq | Hne].
        -- (* self = initiator contradicts Hpar and Hinop *)
           rewrite Heq in Hpar.
           unfold initiator_no_parent, proc_of in Hinop.
           rewrite Hpar in Hinop. discriminate.
        -- rewrite (upd_other _ _ _ _ Hne). exact Hinop.
      * intro n. intro child.
        destruct (node_eq self n) as [Heq | Hne].
        -- subst n. rewrite upd_self. simpl. intro H.
           destruct H as [<- | Hold].
           ++ rewrite Hsrc. exact Hadj_self_s.
           ++ exact (Hchn self child Hold).
        -- rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hchn n child H).
      * intros pkt' Hin'.
        apply in_app_iff in Hin' as [Hold | Hnew].
        -- exact (Hvpkt _ (remove_pkt_in _ _ _ Hold)).
        -- destruct Hnew as [<- | []]. simpl. exact Hpar_adj.
      * intros Hph.
        destruct (node_eq self initiator) as [Heq | Hne].
        -- rewrite Heq in Hph. rewrite upd_self in Hph. simpl in Hph. discriminate.
        -- rewrite (upd_other _ _ _ _ Hne) in Hph.
           apply Hidle in Hph. rewrite Hph in Hin. contradiction.
    + (* initiator decides: parent = None *)
      set (decided := mkProc Decided None 0
                             (ep_src pkt :: ps_children (es_procs gs self))).
      unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
             initiator_no_parent, children_are_neighbors, valid_packets,
             init_idle_empty, proc_of; cbn -[update_proc]; repeat split.
      * intro n. intro par'.
        destruct (node_eq self n) as [Heq | Hne].
        -- subst n. rewrite upd_self. simpl. discriminate.
        -- rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hpin n par' H).
      * intro n.
        destruct (node_eq self n) as [Heq | Hne].
        -- subst n. rewrite upd_self. simpl. discriminate.
        -- rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hself n H).
      * destruct (node_eq self initiator) as [Heq | Hne].
        -- rewrite Heq. rewrite upd_self. simpl. reflexivity.
        -- rewrite (upd_other _ _ _ _ Hne). exact Hinop.
      * intro n. intro child.
        destruct (node_eq self n) as [Heq | Hne].
        -- subst n. rewrite upd_self. simpl. intro H.
           destruct H as [<- | Hold].
           ++ rewrite Hsrc. exact Hadj_self_s.
           ++ exact (Hchn self child Hold).
        -- rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hchn n child H).
      * intros pkt' Hold.
        exact (Hvpkt _ (remove_pkt_in _ _ _ Hold)).
      * intros Hph.
        destruct (node_eq self initiator) as [Heq | Hne].
        -- rewrite Heq in Hph. rewrite upd_self in Hph. simpl in Hph. discriminate.
        -- rewrite (upd_other _ _ _ _ Hne) in Hph.
           apply Hidle in Hph. rewrite Hph in Hin. contradiction.
  - (* pending ≠ 1: still waiting, no new msgs.
       After if-false simplification: *)
    simpl.
    set (new_p := mkProc Active (ps_parent (es_procs gs self))
                         (Nat.pred (ps_pending (es_procs gs self)))
                         (ep_src pkt :: ps_children (es_procs gs self))).
    unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
           initiator_no_parent, children_are_neighbors, valid_packets,
           init_idle_empty, proc_of; cbn -[update_proc]; repeat split.
    + intro n. intro par'.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self. simpl. intro H. exact (Hpin self par' H).
      * rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hpin n par' H).
    + intro n.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self. simpl. intro H. exact (Hself self H).
      * rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hself n H).
    + destruct (node_eq self initiator) as [Heq | Hne].
      * rewrite Heq. rewrite upd_self. simpl.
        unfold initiator_no_parent, proc_of in Hinop.
        rewrite <- Heq in Hinop. exact Hinop.
      * rewrite (upd_other _ _ _ _ Hne).
        unfold initiator_no_parent, proc_of in Hinop. exact Hinop.
    + intro n. intro child.
      destruct (node_eq self n) as [Heq | Hne].
      * subst n. rewrite upd_self. simpl. intro H.
        destruct H as [<- | Hold].
        -- rewrite Hsrc. exact Hadj_self_s.
        -- exact (Hchn self child Hold).
      * rewrite (upd_other _ _ _ _ Hne). intro H. exact (Hchn n child H).
    + intros pkt' Hold.
      exact (Hvpkt _ (remove_pkt_in _ _ _ Hold)).
    + intros Hph.
      destruct (node_eq self initiator) as [Heq | Hne].
      * rewrite Heq in Hph. rewrite upd_self in Hph. simpl in Hph. discriminate.
      * rewrite (upd_other _ _ _ _ Hne) in Hph.
        apply Hidle in Hph. rewrite Hph in Hin. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(** 5d. Ignored cases: Token/Decided, Echo/Idle, Echo/Decided *)

(** Ignored message cases: Token/Decided, Echo/Idle, Echo/Decided.
    In all three branches handle_msg returns a state with identical procs
    and a strictly smaller message bag.  We first prove the state equality,
    then INV follows directly from the IH since fewer packets in the bag
    only makes valid_packets easier and init_idle_empty uses Hin to derive
    a contradiction if the initiator were still Idle. *)
Lemma deliver_ignored gs self pkt :
    ep_dst pkt = self ->
    (  (ep_body pkt = Token /\ (proc_of gs self).(ps_phase) = Decided)
    \/ (ep_body pkt = Echo  /\ (proc_of gs self).(ps_phase) = Idle)
    \/ (ep_body pkt = Echo  /\ (proc_of gs self).(ps_phase) = Decided)) ->
    INV gs ->
    In pkt gs.(es_msgs) ->
    INV (handle_msg node_eq all_nodes adj self
          (mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs)))
          pkt).
Proof.
  intros Hdst Hcase [Htree [Hchn [Hvpkt Hidle]]] Hin.
  destruct Htree as [Hpin [Hself Hinop]].
  (* In all three ignored cases, handle_msg returns the state with only msgs changed.
     We show the result state = mkEchoState gs.(es_procs) (remove_pkt ...) and prove INV. *)
  (* First reduce handle_msg for each case. *)
  assert (Hgoal :
    handle_msg node_eq all_nodes adj self
      (mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs)))
      pkt =
    mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs))).
  { unfold handle_msg, proc_of in *.
    rewrite <- Hdst in *.
    destruct Hcase as [[Hb Hph] | [[Hb Hph] | [Hb Hph]]];
    rewrite Hb; simpl; rewrite Hph; reflexivity. }
  rewrite Hgoal.
  (* Now prove INV of the state with same procs but reduced msgs. *)
  unfold INV, tree_invariant, parent_is_neighbor, no_self_parent,
         initiator_no_parent, children_are_neighbors, valid_packets,
         init_idle_empty, proc_of; simpl; repeat split.
  - exact Hpin.
  - exact Hself.
  - exact Hinop.
  - exact Hchn.
  - intros pkt' H. apply Hvpkt. exact (remove_pkt_in _ _ _ H).
  - intros Hph'. apply Hidle in Hph'. rewrite Hph' in Hin. contradiction.
Qed.

(* ================================================================== *)
(** ** 6. Main step lemma and invariant theorem *)

(** Combines all four per-handler sub-lemmas into a single step lemma.
    Destructs on (ep_body pkt, ps_phase (proc_of gs (ep_dst pkt))) to
    dispatch to the appropriate sub-lemma.  The six cases are:
    Token/{Idle,Active,Decided} and Echo/{Idle,Active,Decided}. *)
Lemma INV_step_deliver gs pkt gs' :
    INV gs ->
    In pkt gs.(es_msgs) ->
    gs' = handle_msg node_eq all_nodes adj (ep_dst pkt)
                     (mkEchoState gs.(es_procs) (remove_pkt node_eq pkt gs.(es_msgs)))
                     pkt ->
    INV gs'.
Proof.
  intros Hinv Hin ->.
  set (self   := ep_dst pkt).
  set (sender := ep_src pkt).
  set (p      := gs.(es_procs) self).
  destruct (ep_body pkt) eqn:Hbody; destruct (p.(ps_phase)) eqn:Hphase.
  - (* Token / Idle *)
    eapply deliver_token_idle with (sender := sender) (body := ep_body pkt);
    [destruct pkt; reflexivity | exact Hbody | exact Hphase | exact Hinv | exact Hin].
  - (* Token / Active *)
    eapply deliver_token_active;
    [reflexivity | reflexivity | exact Hbody | exact Hphase | exact Hinv | exact Hin].
  - (* Token / Decided *)
    eapply deliver_ignored; [reflexivity | left; split; [exact Hbody | exact Hphase]
                             | exact Hinv | exact Hin].
  - (* Echo / Idle *)
    eapply deliver_ignored; [reflexivity | right; left; split; [exact Hbody | exact Hphase]
                             | exact Hinv | exact Hin].
  - (* Echo / Active *)
    eapply deliver_echo_active;
    [reflexivity | reflexivity | exact Hbody | exact Hphase | exact Hinv | exact Hin].
  - (* Echo / Decided *)
    eapply deliver_ignored; [reflexivity | right; right; split; [exact Hbody | exact Hphase]
                             | exact Hinv | exact Hin].
Qed.

(** Main safety theorem: INV is an invariant of the Echo LTS.
    Uses [invariant_by_induction]: INV_init covers initial states,
    INV_step_start / INV_step_deliver cover the two transition kinds. *)
Theorem INV_holds : is_invariant ELts INV.
Proof.
  apply invariant_by_induction.
  - apply INV_init.
  - intros gs lbl gs' Hinv Hstep.
    destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hin Heq].
    + exact (INV_step_start gs0 Hinv Hph).
    + exact (INV_step_deliver gs0 pkt gs0' Hinv Hin Heq).
Qed.

(* ================================================================== *)
(** ** 7. Corollaries *)

(** Corollaries: project INV onto each individual property.
    These are the externally useful results — clients don't need to know
    about the full INV conjunction. *)
Theorem tree_invariant_holds : is_invariant ELts tree_invariant.
Proof.
  intros gs Hr. exact (proj1 (INV_holds gs Hr)).
Qed.

Theorem children_are_neighbors_holds : is_invariant ELts children_are_neighbors.
Proof.
  intros gs Hr. exact (proj1 (proj2 (INV_holds gs Hr))).
Qed.

Theorem valid_packets_holds : is_invariant ELts valid_packets.
Proof.
  intros gs Hr. exact (proj1 (proj2 (proj2 (INV_holds gs Hr)))).
Qed.

(* ================================================================== *)
(** ** 8. Spanning tree (path to initiator) *)

(** Follow the ps_parent chain for at most k hops.
    Returns Some m if the chain reaches m in ≤ k steps, None if it runs
    into a node with no parent before k steps are used.  The bound k is
    existentially quantified in [reaches_initiator], so the caller need
    only exhibit a concrete k — typically the depth of n in the token-wave
    spanning tree. *)
Fixpoint parent_path (gs : EState) (n : node) (k : nat) : option node :=
  match k with
  | 0   => Some n
  | S k' =>
      match (proc_of gs n).(ps_parent) with
      | None     => None
      | Some par => parent_path gs par k'
      end
  end.

Definition reaches_initiator (gs : EState) (n : node) : Prop :=
  exists k, parent_path gs n k = Some initiator.

(** If gs' agrees with gs on all nodes except [self], and [self] had no parent
    in gs, then any parent-chain that succeeded in gs still succeeds in gs'. *)
Lemma parent_path_upd_nil (gs gs' : EState) (self : node) :
    (forall q, q <> self -> proc_of gs' q = proc_of gs q) ->
    (proc_of gs self).(ps_parent) = None ->
    forall n k m, parent_path gs n k = Some m -> parent_path gs' n k = Some m.
Proof.
  intros Hother Hnil n k.
  revert n.
  induction k as [| k' IH]; intros n0 m Hpath.
  - exact Hpath.
  - simpl in Hpath.
    destruct ((proc_of gs n0).(ps_parent)) as [par |] eqn:Hpar; [| discriminate].
    simpl.
    destruct (node_eq n0 self) as [Heq | Hne].
    + subst. rewrite Hnil in Hpar. discriminate.
    + assert (Hpar' : (proc_of gs' n0).(ps_parent) = Some par).
      { rewrite (Hother n0 Hne). exact Hpar. }
      rewrite Hpar'. exact (IH par m Hpath).
Qed.

(** If gs' and gs agree on ALL parent pointers, any chain is unchanged. *)
Lemma parent_path_upd_agree (gs gs' : EState) :
    (forall n, (proc_of gs' n).(ps_parent) = (proc_of gs n).(ps_parent)) ->
    forall n k m, parent_path gs n k = Some m -> parent_path gs' n k = Some m.
Proof.
  intros Hagree n k.
  revert n.
  induction k as [| k' IH]; intros n0 m Hpath.
  - exact Hpath.
  - simpl in Hpath.
    destruct ((proc_of gs n0).(ps_parent)) as [par |] eqn:Hpar; [| discriminate].
    simpl. rewrite (Hagree n0), Hpar. exact (IH par m Hpath).
Qed.

(** Idle nodes have no parent pointer set. *)
Definition idle_no_parent (gs : EState) : Prop :=
  forall n, (proc_of gs n).(ps_phase) = Idle -> (proc_of gs n).(ps_parent) = None.

(** Every Token in the bag has a source node with a parent-chain to the initiator. *)
Definition token_src_has_chain (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Token ->
    reaches_initiator gs (ep_src pkt).

(** Every Active non-initiator node has a parent-chain to the initiator. *)
Definition active_non_init_has_chain_inv (gs : EState) : Prop :=
  forall n, In n all_nodes ->
    (proc_of gs n).(ps_phase) = Active ->
    n <> initiator ->
    reaches_initiator gs n.

(** Combined TSC invariant. *)
Definition TSC (gs : EState) : Prop :=
  idle_no_parent gs /\ token_src_has_chain gs /\ active_non_init_has_chain_inv gs.

(* ------------------------------------------------------------------ *)
(** Base case for TSC *)

Lemma TSC_init : forall gs, lts_init ELts gs -> TSC gs.
Proof.
  intros gs [Hproc Hmsgs].
  split; [| split].
  - (* idle_no_parent: all start Idle with parent=None *)
    intros n _.
    unfold proc_of. rewrite Hproc. simpl. reflexivity.
  - (* token_src_has_chain: no messages in initial state *)
    intros pkt Hin _. rewrite Hmsgs in Hin. contradiction.
  - (* active_non_init_has_chain_inv: no Active nodes initially *)
    intros n _ Hph _.
    unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(** Step preservation for TSC *)

Lemma TSC_step gs lbl gs' :
    TSC gs ->
    lts_trans ELts gs lbl gs' ->
    TSC gs'.
Proof.
  intros [Hinp [Htsc Hanic]] Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - (* gs' = initiator_start ... gs0 *)
    set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    (* Useful facts about proc_of gs' *)
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_active : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    split; [| split].

    + (* idle_no_parent *)
      intros n Hph.
      destruct (node_eq n initiator) as [-> | Hne].
      * rewrite Hinit_active in Hph. discriminate.
      * rewrite (Hother n Hne) in Hph. rewrite (Hother n Hne).
        exact (Hinp n Hph).

    + (* token_src_has_chain *)
      (* gs' has msgs = gs0.(es_msgs) ++ send_to_all initiator my_nbrs Token *)
      intros p Hpin Hbp.
      unfold initiator_start in Hpin. simpl in Hpin.
      apply in_app_iff in Hpin as [Hold | Hnew].
      * (* old token: src has chain in gs0; lift to gs' *)
        assert (Hreach_gs0 : reaches_initiator gs0 (ep_src p)).
        { exact (Htsc p Hold Hbp). }
        destruct Hreach_gs0 as [k Hk].
        exists k.
        apply (parent_path_upd_agree gs0 gs').
        { intros n.
          destruct (node_eq n initiator) as [-> | Hne].
          - rewrite Hinit_par.
            assert (Hinit_idle : (proc_of gs0 initiator).(ps_phase) = Idle) by exact Hph0.
            symmetry. exact (Hinp initiator Hinit_idle).
          - rewrite (Hother n Hne). reflexivity. }
        exact Hk.
      * (* new token from initiator: src = initiator *)
        apply send_to_all_inv in Hnew as [Hsrc _].
        rewrite Hsrc.
        exists 0. simpl. reflexivity.

    + (* active_non_init_has_chain_inv *)
      intros n Hn Hph Hne.
      (* Only initiator becomes Active in step_start *)
      destruct (node_eq n initiator) as [-> | Hne'].
      * exact (False_ind _ (Hne eq_refl)).
      * (* n ≠ initiator: proc_of gs' n = proc_of gs0 n, so n was Active in gs0 *)
        rewrite (Hother n Hne') in Hph.
        assert (Hreach_gs0 : reaches_initiator gs0 n) by exact (Hanic n Hn Hph Hne).
        destruct Hreach_gs0 as [k Hk].
        exists k.
        apply (parent_path_upd_agree gs0 gs').
        { intros m.
          destruct (node_eq m initiator) as [-> | Hmne].
          - rewrite Hinit_par.
            symmetry. exact (Hinp initiator Hph0).
          - rewrite (Hother m Hmne). reflexivity. }
        exact Hk.

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* ===== Token / Idle ===== *)
    + (* Key facts about gs' in Token/Idle case *)
      assert (Hgs'_procs_self : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hgs'_phase_self : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall n, n <> self -> proc_of gs' n = proc_of gs0 n).
      { intros n Hne.
        unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      (* self was Idle in gs0, so ps_parent = None *)
      assert (Hself_nil : (proc_of gs0 self).(ps_parent) = None).
      { exact (Hinp self Hphase). }
      (* sender has a chain in gs0 (it sent us a Token) *)
      assert (Hreach_sender_gs0 : reaches_initiator gs0 sender).
      { exact (Htsc pkt Hin Hbody). }
      assert (Hreach_sender_gs' : reaches_initiator gs' sender).
      { destruct Hreach_sender_gs0 as [k Hk].
        exists k.
        apply (parent_path_upd_nil gs0 gs' self).
        - intros n Hne. exact (Hother n Hne).
        - exact Hself_nil.
        - exact Hk. }
      (* self has a chain to initiator via sender *)
      assert (Hreach_self_gs' : reaches_initiator gs' self).
      { destruct Hreach_sender_gs' as [k Hk].
        exists (S k). simpl.
        rewrite Hgs'_procs_self. exact Hk. }
      split; [| split].

      * (* idle_no_parent *)
        intros n Hph.
        destruct (node_eq n self) as [-> | Hne].
        { rewrite Hgs'_phase_self in Hph. discriminate. }
        { rewrite (Hother n Hne) in Hph. rewrite (Hother n Hne).
          exact (Hinp n Hph). }

      * (* token_src_has_chain *)
        intros q Hqin Hqbody.
        unfold gs', handle_msg in Hqin.
        change (es_procs gs_mid self) with p in Hqin.
        rewrite Hbody, Hphase in Hqin.
        destruct (Nat.eqb (length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                          (nbrs all_nodes adj self))) 0) eqn:Hleaf in Hqin.
        { (* leaf sub-case: msgs = remove_pkt bag ++ [mkPkt self sender Echo] *)
          simpl in Hqin.
          apply in_app_iff in Hqin as [Hold | Hnew].
          { apply remove_pkt_in in Hold.
            assert (Hreach : reaches_initiator gs0 (ep_src q)).
            { exact (Htsc q Hold Hqbody). }
            destruct Hreach as [k Hk].
            exists k.
            apply (parent_path_upd_nil gs0 gs' self).
            { intros m Hme. exact (Hother m Hme). }
            { exact Hself_nil. }
            exact Hk. }
          { destruct Hnew as [<- | []]. simpl in Hqbody. discriminate. } }
        { (* internal sub-case: msgs = remove_pkt bag ++ send_to_all self forwards Token *)
          simpl in Hqin.
          apply in_app_iff in Hqin as [Hold | Hnew].
          { apply remove_pkt_in in Hold.
            assert (Hreach : reaches_initiator gs0 (ep_src q)).
            { exact (Htsc q Hold Hqbody). }
            destruct Hreach as [k Hk].
            exists k.
            apply (parent_path_upd_nil gs0 gs' self).
            { intros m Hme. exact (Hother m Hme). }
            { exact Hself_nil. }
            exact Hk. }
          { apply send_to_all_inv in Hnew as [Hsrc _].
            rewrite Hsrc. exact Hreach_self_gs'. } }

      * (* active_non_init_has_chain_inv *)
        intros n Hn Hph Hne.
        destruct (node_eq n self) as [-> | Hnself].
        { exact Hreach_self_gs'. }
        { rewrite (Hother n Hnself) in Hph.
          assert (Hreach_gs0 : reaches_initiator gs0 n) by exact (Hanic n Hn Hph Hne).
          destruct Hreach_gs0 as [k Hk].
          exists k.
          apply (parent_path_upd_nil gs0 gs' self).
          { intros m Hme. exact (Hother m Hme). }
          { exact Hself_nil. }
          exact Hk. }

    (* ===== Token / Active ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
      { intros n. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      split; [| split].
      * intros n Hph. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinp n Hph).
      * intros q Hqin Hqbody.
        (* gs' msgs = remove_pkt bag ++ [mkPkt self sender Echo] *)
        unfold gs', handle_msg in Hqin.
        change (es_procs gs_mid self) with p in Hqin.
        rewrite Hbody, Hphase in Hqin. simpl in Hqin.
        apply in_app_iff in Hqin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hold Hqbody).
           destruct Hreach as [k Hk]. exists k.
           exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
        -- destruct Hnew as [<- | []]. simpl in Hqbody. discriminate.
      * intros n Hn Hph Hne.
        unfold proc_of in Hph. rewrite Hgs'_procs in Hph.
        assert (Hreach : reaches_initiator gs0 n) by exact (Hanic n Hn Hph Hne).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).

    (* ===== Token / Decided ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
      { intros n. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      split; [| split].
      * intros n Hph. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinp n Hph).
      * intros q Hqin Hqbody.
        unfold gs', handle_msg in Hqin.
        change (es_procs gs_mid self) with p in Hqin.
        rewrite Hbody, Hphase in Hqin. simpl in Hqin.
        apply remove_pkt_in in Hqin.
        assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hqin Hqbody).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
      * intros n Hn Hph Hne.
        unfold proc_of in Hph. rewrite Hgs'_procs in Hph.
        assert (Hreach : reaches_initiator gs0 n) by exact (Hanic n Hn Hph Hne).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).

    (* ===== Echo / Idle ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
      { intros n. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      split; [| split].
      * intros n Hph. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinp n Hph).
      * intros q Hqin Hqbody.
        unfold gs', handle_msg in Hqin.
        change (es_procs gs_mid self) with p in Hqin.
        rewrite Hbody, Hphase in Hqin. simpl in Hqin.
        apply remove_pkt_in in Hqin.
        assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hqin Hqbody).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
      * intros n Hn Hph Hne.
        unfold proc_of in Hph. rewrite Hgs'_procs in Hph.
        assert (Hreach : reaches_initiator gs0 n) by exact (Hanic n Hn Hph Hne).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).

    (* ===== Echo / Active ===== *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar.
        -- (* pending=1, parent=Some par: self stays Active, parent unchanged *)
           set (new_p := mkProc Active (Some par) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold new_p. rewrite Hpeq. reflexivity. }
           assert (Hagree : forall nn, (proc_of gs' nn).(ps_parent) = (proc_of gs0 nn).(ps_parent)).
           { intros nn. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self nn) as [Heq | Hne].
             - subst nn. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar).
             - unfold proc_of. reflexivity. }
           split; [| split].
           ++ intros nn Hph.
              assert (Hnn_par : (proc_of gs' nn).(ps_parent) = (proc_of gs0 nn).(ps_parent))
                by exact (Hagree nn).
              rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self nn) as [Heq | Hne].
              ** subst nn. simpl in Hph. discriminate.
              ** unfold proc_of in *. rewrite Hnn_par. exact (Hinp nn Hph).
           ++ intros q Hqin Hqbody.
              rewrite Hgs'eq in Hqin. simpl in Hqin.
              apply in_app_iff in Hqin as [Hold | Hnew].
              ** apply remove_pkt_in in Hold.
                 assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hold Hqbody).
                 destruct Hreach as [k Hk]. exists k.
                 exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
              ** destruct Hnew as [<- | []]. simpl in Hqbody. discriminate.
           ++ intros nn Hnn Hph Hnne.
              rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self nn) as [Heq | Hnnself].
              ** subst nn. (* self was already Active in gs0 *)
                 simpl in Hph.
                 assert (Hself_act : (proc_of gs0 self).(ps_phase) = Active).
                 { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
                 assert (Hreach : reaches_initiator gs0 self) by exact (Hanic self Hnn Hself_act Hnne).
                 destruct Hreach as [k Hk]. exists k.
                 exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
              ** assert (Hreach : reaches_initiator gs0 nn).
                 { exact (Hanic nn Hnn Hph Hnne). }
                 destruct Hreach as [k Hk]. exists k.
                 exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).

        -- (* pending=1, parent=None: initiator decides, n ≠ initiator is vacuously false *)
           set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold decided. rewrite Hpeq. reflexivity. }
           assert (Hagree : forall nn, (proc_of gs' nn).(ps_parent) = (proc_of gs0 nn).(ps_parent)).
           { intros nn. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self nn) as [Heq | Hne].
             - subst nn. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar).
             - unfold proc_of. reflexivity. }
           split; [| split].
           ++ intros nn Hph.
              rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self nn) as [Heq | Hne].
              ** subst nn. simpl in Hph. discriminate.
              ** unfold proc_of in *. rewrite (Hagree nn). exact (Hinp nn Hph).
           ++ intros q Hqin Hqbody.
              rewrite Hgs'eq in Hqin. simpl in Hqin.
              apply remove_pkt_in in Hqin.
              assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hqin Hqbody).
              destruct Hreach as [k Hk]. exists k.
              exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
           ++ intros nn Hnn Hph Hnne.
              rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self nn) as [Heq | Hnnself].
              ** subst nn. simpl in Hph. discriminate.
              ** assert (Hreach : reaches_initiator gs0 nn).
                 { exact (Hanic nn Hnn Hph Hnne). }
                 destruct Hreach as [k Hk]. exists k.
                 exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).

      * (* pending ≠ 1: self stays Active, parent unchanged *)
        set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        assert (Hagree : forall nn, (proc_of gs' nn).(ps_parent) = (proc_of gs0 nn).(ps_parent)).
        { intros nn. rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self nn) as [Heq | Hne].
          - subst nn. simpl. unfold proc_of. reflexivity.
          - unfold proc_of. reflexivity. }
        split; [| split].
        -- intros nn Hph.
           rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
           destruct (node_eq self nn) as [Heq | Hne].
           ++ subst nn. simpl in Hph. discriminate.
           ++ unfold proc_of in *. rewrite (Hagree nn). exact (Hinp nn Hph).
        -- intros q Hqin Hqbody.
           rewrite Hgs'eq in Hqin. simpl in Hqin.
           apply remove_pkt_in in Hqin.
           assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hqin Hqbody).
           destruct Hreach as [k Hk]. exists k.
           exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
        -- intros nn Hnn Hph Hnne.
           rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
           destruct (node_eq self nn) as [Heq | Hnnself].
           ++ subst nn. (* nn = self: was Active in gs0 *)
              assert (Hself_act : (proc_of gs0 self).(ps_phase) = Active).
              { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
              assert (Hreach : reaches_initiator gs0 self) by exact (Hanic self Hnn Hself_act Hnne).
              destruct Hreach as [k Hk]. exists k.
              exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
           ++ assert (Hreach : reaches_initiator gs0 nn).
              { exact (Hanic nn Hnn Hph Hnne). }
              destruct Hreach as [k Hk]. exists k.
              exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).

    (* ===== Echo / Decided ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
      { intros n. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      split; [| split].
      * intros n Hph. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinp n Hph).
      * intros q Hqin Hqbody.
        unfold gs', handle_msg in Hqin.
        change (es_procs gs_mid self) with p in Hqin.
        rewrite Hbody, Hphase in Hqin. simpl in Hqin.
        apply remove_pkt_in in Hqin.
        assert (Hreach : reaches_initiator gs0 (ep_src q)) by exact (Htsc q Hqin Hqbody).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
      * intros n Hn Hph Hne.
        unfold proc_of in Hph. rewrite Hgs'_procs in Hph.
        assert (Hreach : reaches_initiator gs0 n) by exact (Hanic n Hn Hph Hne).
        destruct Hreach as [k Hk]. exists k.
        exact (parent_path_upd_agree gs0 gs' Hagree _ _ _ Hk).
Qed.

Theorem TSC_holds : is_invariant ELts TSC.
Proof.
  apply invariant_by_induction.
  - apply TSC_init.
  - intros gs lbl gs' Htsc Hstep.
    exact (TSC_step gs lbl gs' Htsc Hstep).
Qed.

Theorem active_non_init_has_chain :
  forall gs, reachable ELts gs ->
    forall n, In n all_nodes ->
      (proc_of gs n).(ps_phase) = Active ->
      n <> initiator ->
      reaches_initiator gs n.
Proof.
  intros gs Hr n Hn Hact Hne.
  exact (proj2 (proj2 (TSC_holds gs Hr)) n Hn Hact Hne).
Qed.

Definition initiator_decided (gs : EState) : Prop :=
  (proc_of gs initiator).(ps_phase) = Decided.

(* ================================================================== *)
(** ** Helper lemmas for one_hop_active *)

Lemma in_send_to_all (src : node) (dsts : list node) (msg : echo_msg) (n : node) :
    In n dsts -> In (mkPkt src n msg) (send_to_all src dsts msg).
Proof.
  intro Hin.
  unfold send_to_all.
  apply in_map_iff.
  exists n. split; [reflexivity | exact Hin].
Qed.

Lemma in_nbrs_of (m n : node) :
    adj m n = true -> In n all_nodes -> In n (nbrs all_nodes adj m).
Proof.
  intros Hadj Hin.
  unfold nbrs.
  apply filter_In. split; [exact Hin | exact Hadj].
Qed.

Lemma remove_pkt_ne_in (pkt pkt' : @echo_packet node) bag :
    In pkt' bag ->
    (ep_src pkt' <> ep_src pkt \/ ep_dst pkt' <> ep_dst pkt) ->
    In pkt' (remove_pkt node_eq pkt bag).
Proof.
  intros Hin Hne.
  induction bag as [| hd tl IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [<- | Htl].
    + (* pkt' = hd *)
      simpl remove_pkt.
      destruct (node_eq (ep_src hd) (ep_src pkt)) as [Esrc | Nsrc].
      * destruct (node_eq (ep_dst hd) (ep_dst pkt)) as [Edst | Ndst].
        -- (* src and dst match: check body *)
           destruct Hne as [Hs | Hd].
           ++ exact (False_ind _ (Hs Esrc)).
           ++ exact (False_ind _ (Hd Edst)).
        -- simpl. left. reflexivity.
      * simpl. left. reflexivity.
    + simpl remove_pkt.
      destruct (node_eq (ep_src hd) (ep_src pkt)) as [Esrc | Nsrc].
      * destruct (node_eq (ep_dst hd) (ep_dst pkt)) as [Edst | Ndst].
        -- (* src and dst match: check body *)
           destruct (ep_body hd) eqn:Hbh; destruct (ep_body pkt) eqn:Hbp.
           ++ (* Token/Token: hd removed, result = tl *)
              exact Htl.
           ++ (* Token/Echo: hd kept *)
              right. exact (IH Htl).
           ++ (* Echo/Token: hd kept *)
              right. exact (IH Htl).
           ++ (* Echo/Echo: hd removed, result = tl *)
              exact Htl.
        -- simpl. right. exact (IH Htl).
      * simpl. right. exact (IH Htl).
Qed.

Lemma remove_pkt_body_ne_in (pkt pkt' : @echo_packet node) bag :
    In pkt' bag ->
    ep_body pkt' <> ep_body pkt ->
    In pkt' (remove_pkt node_eq pkt bag).
Proof.
  intros Hin Hbne.
  induction bag as [| hd tl IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [<- | Htl].
    + simpl remove_pkt.
      destruct (node_eq (ep_src hd) (ep_src pkt)) as [Esrc | Nsrc].
      * destruct (node_eq (ep_dst hd) (ep_dst pkt)) as [Edst | Ndst].
        -- (* src and dst match: check body *)
           destruct (ep_body hd) eqn:Hbh; destruct (ep_body pkt) eqn:Hbp.
           ++ exact (False_ind _ (Hbne (eq_refl Token))).
           ++ simpl. left. reflexivity.
           ++ simpl. left. reflexivity.
           ++ exact (False_ind _ (Hbne (eq_refl Echo))).
        -- simpl. left. reflexivity.
      * simpl. left. reflexivity.
    + simpl remove_pkt.
      destruct (node_eq (ep_src hd) (ep_src pkt)) as [Esrc | Nsrc].
      * destruct (node_eq (ep_dst hd) (ep_dst pkt)) as [Edst | Ndst].
        -- destruct (ep_body hd) eqn:Hbh; destruct (ep_body pkt) eqn:Hbp.
           ++ exact Htl.
           ++ right. exact (IH Htl).
           ++ right. exact (IH Htl).
           ++ exact Htl.
        -- simpl. right. exact (IH Htl).
      * simpl. right. exact (IH Htl).
Qed.

(* ================================================================== *)
(** ** Invariant A: token_src_not_idle *)

(** Every Token in the message bag was sent by a non-Idle node. *)
Definition token_src_not_idle (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Token ->
    (proc_of gs (ep_src pkt)).(ps_phase) <> Idle.

Lemma token_src_not_idle_base : forall gs, lts_init ELts gs -> token_src_not_idle gs.
Proof.
  intros gs [_ Hmsgs] pkt Hin _.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma token_src_not_idle_step gs lbl gs' :
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    token_src_not_idle gs'.
Proof.
  intros Htoken_src_not_idle Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_active : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros pkt' Hpin Hbp.
    unfold gs', initiator_start in Hpin. simpl in Hpin.
    apply in_app_iff in Hpin as [Hold | Hnew].
    + (* old packet: source was non-Idle in gs0 *)
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Htoken_src_not_idle pkt' Hold Hbp).
      destruct (node_eq (ep_src pkt') initiator) as [Heq | Hne].
      * (* source = initiator: but Hph0 says initiator was Idle, contradiction *)
        rewrite Heq in Hne_idle. exact (False_ind _ (Hne_idle Hph0)).
      * (* source ≠ initiator: proc unchanged *)
        rewrite (Hother _ Hne). exact Hne_idle.
    + (* new packet from initiator: source = initiator, now Active *)
      apply send_to_all_inv in Hnew as [Hsrc _].
      rewrite Hsrc. rewrite Hinit_active. discriminate.

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros pkt' Hpin Hbp.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* ===== Token / Idle ===== *)
    + (* In Token/Idle case, gs' has:
         - self phase = Active
         - procs of others unchanged
         - msgs = remove_pkt bag ++ [Echo(self,sender)] (leaf) or ++ send_to_all (internal) *)
      assert (Hself_active : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall n, n <> self -> proc_of gs' n = proc_of gs0 n).
      { intros n Hne.
        unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      (* self was Idle: no Token in gs0.msgs with source = self *)
      assert (Hself_no_token : forall q, In q (es_msgs gs0) -> ep_body q = Token ->
                                         ep_src q <> self).
      { intros q Hqin Hqb.
        assert (H := Htoken_src_not_idle q Hqin Hqb).
        intro Heq. rewrite Heq in H.
        unfold proc_of in H. rewrite <- Hpeq in H. exact (H Hphase). }
      (* Determine what msgs are in gs' *)
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin.
      set (fwds := filter (fun x => if node_eq x (ep_src pkt) then false else true)
                          (nbrs all_nodes adj self)) in *.
      destruct (Nat.eqb (length fwds) 0) eqn:Hleaf.
      * (* leaf: msgs = remove_pkt bag ++ [Echo(self,sender)] *)
        simpl in Hpin.
        apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Htoken_src_not_idle pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq | Hne].
           ++ (* source = self: was Idle, contradicts non-Idle *)
              rewrite Heq in Hne_idle. unfold proc_of in Hne_idle. rewrite <- Hpeq in Hne_idle.
              exact (False_ind _ (Hne_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact Hne_idle.
        -- (* new Echo packet: body = Echo ≠ Token *)
           destruct Hnew as [<- | []]. simpl in Hbp. discriminate.
      * (* internal: msgs = remove_pkt bag ++ send_to_all self fwds Token *)
        simpl in Hpin.
        apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Htoken_src_not_idle pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq | Hne].
           ++ rewrite Heq in Hne_idle. unfold proc_of in Hne_idle. rewrite <- Hpeq in Hne_idle.
              exact (False_ind _ (Hne_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact Hne_idle.
        -- (* new Token packet: source = self, now Active *)
           apply send_to_all_inv in Hnew as [Hsrc _].
           rewrite Hsrc. rewrite Hself_active. discriminate.

    (* ===== Token / Active: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      (* msgs = remove_pkt bag ++ [Echo(self,sender)] *)
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply in_app_iff in Hpin as [Hold | Hnew].
      * apply remove_pkt_in in Hold.
        assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
          by exact (Htoken_src_not_idle pkt' Hold Hbp).
        unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.
      * destruct Hnew as [<- | []]. simpl in Hbp. discriminate.

    (* ===== Token / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Htoken_src_not_idle pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.

    (* ===== Echo / Idle: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Htoken_src_not_idle pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.

    (* ===== Echo / Active ===== *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar.
        -- set (new_p := mkProc Active (Some par) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold new_p. rewrite Hpeq. reflexivity. }
           rewrite Hgs'eq in Hpin. simpl in Hpin.
           apply in_app_iff in Hpin as [Hold | Hnew].
           ++ apply remove_pkt_in in Hold.
              assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
                by exact (Htoken_src_not_idle pkt' Hold Hbp).
              rewrite Hgs'eq. rewrite proc_of_upd.
              destruct (node_eq self (ep_src pkt')) as [Heq | Hne].
              ** simpl. discriminate.
              ** unfold proc_of in Hne_idle. exact Hne_idle.
           ++ destruct Hnew as [<- | []]. simpl in Hbp. discriminate.
        -- set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold decided. rewrite Hpeq. reflexivity. }
           rewrite Hgs'eq in Hpin. simpl in Hpin.
           apply remove_pkt_in in Hpin.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Htoken_src_not_idle pkt' Hpin Hbp).
           rewrite Hgs'eq. rewrite proc_of_upd.
           destruct (node_eq self (ep_src pkt')) as [Heq | Hne].
           ++ simpl. discriminate.
           ++ unfold proc_of in Hne_idle. exact Hne_idle.
      * set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        rewrite Hgs'eq in Hpin. simpl in Hpin.
        apply remove_pkt_in in Hpin.
        assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
          by exact (Htoken_src_not_idle pkt' Hpin Hbp).
        rewrite Hgs'eq. rewrite proc_of_upd.
        destruct (node_eq self (ep_src pkt')) as [Heq | Hne].
        ++ simpl. discriminate.
        ++ unfold proc_of in Hne_idle. exact Hne_idle.

    (* ===== Echo / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Htoken_src_not_idle pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.
Qed.

Theorem token_src_not_idle_holds : is_invariant ELts token_src_not_idle.
Proof.
  apply invariant_by_induction.
  - apply token_src_not_idle_base.
  - intros gs lbl gs' Hinv Hstep.
    exact (token_src_not_idle_step gs lbl gs' Hinv Hstep).
Qed.

(* ================================================================== *)
(** ** Invariant B: token_sent_or_notidle *)

(** If m is non-Idle, adj m n, and n is not m's parent, then n is non-Idle
    OR there is a Token(m->n) in the message bag. *)
Definition token_sent_or_notidle (gs : EState) : Prop :=
  forall m n,
    In m all_nodes -> In n all_nodes ->
    adj m n = true ->
    (proc_of gs m).(ps_phase) <> Idle ->
    (proc_of gs m).(ps_parent) <> Some n ->
    (proc_of gs n).(ps_phase) <> Idle \/
    (exists pkt, In pkt (es_msgs gs) /\
                 ep_src pkt = m /\ ep_dst pkt = n /\ ep_body pkt = Token).

Lemma token_sent_or_notidle_base : forall gs, lts_init ELts gs -> token_sent_or_notidle gs.
Proof.
  intros gs [Hproc _] m n Hm Hn Hadj Hph Hpar.
  exfalso. apply Hph.
  unfold proc_of. rewrite Hproc. simpl. reflexivity.
Qed.

Lemma token_sent_or_notidle_step gs lbl gs' :
    token_sent_or_notidle gs ->
    lts_trans ELts gs lbl gs' ->
    token_sent_or_notidle gs'.
Proof.
  intros Htsno Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_phase : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m n Hm Hn Hadj Hph Hpar.
    destruct (node_eq m initiator) as [Heqm | Hnem].
    + (* m = initiator: initiator is now Active, parent = None *)
      subst m.
      (* For each neighbor n of initiator, initiator sent Token to n *)
      (* initiator's parent is None, so Hpar : None <> Some n, which is fine *)
      right.
      (* Token(initiator, n) is in msgs of gs' *)
      assert (Hn_in_nbrs : In n (nbrs all_nodes adj initiator)).
      { apply in_nbrs_of; [exact Hadj | exact Hn]. }
      unfold gs', initiator_start. simpl.
      exists (mkPkt initiator n Token).
      split.
      * apply in_app_iff. right.
        apply in_send_to_all. exact Hn_in_nbrs.
      * simpl. auto.
    + (* m ≠ initiator: proc_of gs' m = proc_of gs0 m *)
      rewrite (Hother m Hnem) in Hph.
      rewrite (Hother m Hnem) in Hpar.
      destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
      * (* n non-Idle in gs0 *)
        destruct (node_eq n initiator) as [Heqn | Hnen].
        -- subst. left. rewrite Hinit_phase. discriminate.
        -- left. rewrite (Hother n Hnen). exact Hnph.
      * (* Token(m,n) in gs0.msgs *)
        right.
        unfold gs', initiator_start. simpl.
        exists p'. split.
        -- apply in_app_iff. left. exact Hpin.
        -- exact (conj Hps (conj Hpd Hpb)).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros m n Hm Hn Hadj Hph Hpar.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* ===== Token / Idle ===== *)
    + (* self goes Idle → Active, parent := Some sender *)
      assert (Hself_phase : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall n0, n0 <> self -> proc_of gs' n0 = proc_of gs0 n0).
      { intros n0 Hne.
        unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      (* Case split: m = self vs m ≠ self *)
      destruct (node_eq m self) as [Heqm | Hnem].
      * (* m = self: self just became Active, parent = Some sender *)
        subst m.
        rewrite Hself_par in Hpar.
        (* Hpar : Some sender <> Some n, so n ≠ sender *)
        assert (Hnsender : n <> sender).
        { intro Heq. apply Hpar. f_equal. exact (eq_sym Heq). }
        (* n is in the forwards list *)
        set (fwds := filter (fun x => if node_eq x (ep_src pkt) then false else true)
                            (nbrs all_nodes adj self)).
        assert (Hn_fwds : In n fwds).
        { unfold fwds. apply filter_In. split.
          - apply in_nbrs_of; [exact Hadj | exact Hn].
          - destruct (node_eq n (ep_src pkt)) as [Heq | Hne].
            + exact (False_ind _ (Hnsender Heq)).
            + reflexivity. }
        (* Token(self,n) is in gs'.msgs: use the internal case *)
        right.
        assert (Hpend_false : Nat.eqb (length fwds) 0 = false).
        { apply Nat.eqb_neq.
          intro Hlen. apply length_zero_iff_nil in Hlen.
          rewrite Hlen in Hn_fwds. contradiction. }
        unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        fold fwds. rewrite Hpend_false. simpl.
        exists (mkPkt self n Token).
        split.
        -- apply in_app_iff. right.
           apply in_send_to_all. exact Hn_fwds.
        -- simpl. auto.
      * (* m ≠ self: proc_of gs' m = proc_of gs0 m *)
        rewrite (Hother m Hnem) in Hph.
        rewrite (Hother m Hnem) in Hpar.
        destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
        -- (* n non-Idle in gs0 *)
           destruct (node_eq n self) as [Heqn | Hnen].
           ++ (* n = self: now Active *)
              subst n. left. rewrite Hself_phase. discriminate.
           ++ left. rewrite (Hother n Hnen). exact Hnph.
        -- (* Token(m,n) in gs0.msgs *)
           destruct (node_eq (ep_dst p') self) as [Edst | Ndst].
           ++ (* ep_dst p' = self → n = self (via Hpd): n is Active *)
              assert (Hn_self : n = self) by (rewrite <- Hpd; exact Edst).
              left. rewrite Hn_self. rewrite Hself_phase. discriminate.
           ++ (* dst≠self: p' survives in gs'.msgs *)
              right.
              assert (Hp'_in_rm : In p' (remove_pkt node_eq pkt (es_msgs gs0))).
              { apply remove_pkt_ne_in; [exact Hpin | right; exact Ndst]. }
              unfold gs', handle_msg. change (es_procs gs_mid self) with p.
              rewrite Hbody, Hphase.
              set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                          (nbrs all_nodes adj self))).
              destruct (Nat.eqb len0 0) eqn:Hpend; simpl es_msgs;
              exists p'; split;
              [ apply in_app_iff; left; simpl; exact Hp'_in_rm
              | exact (conj Hps (conj Hpd Hpb))
              | apply in_app_iff; left; simpl; exact Hp'_in_rm
              | exact (conj Hps (conj Hpd Hpb)) ].

    (* ===== Token / Active: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hph. rewrite (Hother m) in Hpar.
      destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
      * left. rewrite (Hother n). exact Hnph.
      * (* Token(m,n) in gs0.msgs *)
        (* gs'.(es_msgs) = remove_pkt bag ++ [Echo(self,sender)] *)
        (* n = self → left (self is Active); n ≠ self → p' survives remove_pkt *)
        destruct (node_eq n self) as [Heqn | Hnen].
        -- (* n = self: self is Active, not Idle *)
           left. rewrite (Hother n). unfold proc_of. rewrite Heqn. rewrite <- Hpeq.
           rewrite Hphase. discriminate.
        -- right.
           assert (Hgs'_msgs : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase. reflexivity. }
           assert (Hp'_survives : In p' (es_msgs gs_mid)).
           { simpl. apply remove_pkt_ne_in; [exact Hpin | right; rewrite Hpd; exact Hnen]. }
           exists p'. split.
           ++ rewrite Hgs'_msgs. apply in_app_iff. left. exact Hp'_survives.
           ++ exact (conj Hps (conj Hpd Hpb)).

    (* ===== Token / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hph. rewrite (Hother m) in Hpar.
      destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
      * left. rewrite (Hother n). exact Hnph.
      * destruct (node_eq n self) as [Heqn | Hnen].
        -- (* n = self → self is Decided, not Idle *)
           left. rewrite (Hother n). rewrite Heqn. unfold proc_of. rewrite <- Hpeq.
           rewrite Hphase. discriminate.
        -- (* n ≠ self: p' survives remove_pkt *)
           right.
           assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase. reflexivity. }
           assert (Hp'_survives : In p' (remove_pkt node_eq pkt (es_msgs gs0))).
           { apply remove_pkt_ne_in; [exact Hpin | right; rewrite Hpd; exact Hnen]. }
           exists p'. split.
           ++ rewrite Hgs'_msgs. exact Hp'_survives.
           ++ exact (conj Hps (conj Hpd Hpb)).

    (* ===== Echo / Idle: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hph. rewrite (Hother m) in Hpar.
      destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
      * left. rewrite (Hother n). exact Hnph.
      * (* Token(m,n) in gs0.msgs: pkt.body = Echo, p'.body = Token → bodies differ *)
        right.
        assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase. reflexivity. }
        assert (Hp'_survives : In p' (remove_pkt node_eq pkt (es_msgs gs0))).
        { apply remove_pkt_body_ne_in; [exact Hpin |].
          rewrite Hpb, Hbody. discriminate. }
        exists p'. split.
        ++ rewrite Hgs'_msgs. exact Hp'_survives.
        ++ exact (conj Hps (conj Hpd Hpb)).

    (* ===== Echo / Active ===== *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar'.
        -- set (new_p := mkProc Active (Some par) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar'. unfold new_p. rewrite Hpeq. reflexivity. }
           assert (Hother : forall n0, n0 <> self ->
                     proc_of gs' n0 = proc_of gs0 n0).
           { intros n0 Hne. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n0) as [Heq | _].
             - exact (False_ind _ (Hne (eq_sym Heq))).
             - unfold proc_of. reflexivity. }
           assert (Hself_par_gs' : (proc_of gs' self).(ps_parent) = Some par).
           { rewrite Hgs'eq. rewrite proc_of_upd. destruct (node_eq self self) as [_ | Hc].
             - simpl. reflexivity.
             - exact (False_ind _ (Hc eq_refl)). }
           assert (Hself_phase_gs' : (proc_of gs' self).(ps_phase) = Active).
           { rewrite Hgs'eq. rewrite proc_of_upd. destruct (node_eq self self) as [_ | Hc].
             - simpl. reflexivity.
             - exact (False_ind _ (Hc eq_refl)). }
           destruct (node_eq m self) as [Heqm | Hnem].
           ++ (* m = self: phase/parent unchanged (still Active/Some par) *)
              subst m.
              rewrite Hself_par_gs' in Hpar.
              rewrite Hself_phase_gs' in Hph.
              (* Hpar : Some par ≠ Some n *)
              assert (Hn_ne_par : n <> par).
              { intro Heq. apply Hpar. f_equal. exact (eq_sym Heq). }
              (* In gs0, self was Active with parent=Some par and ps_parent p = Some par *)
              assert (Hself_phase_gs0 : (proc_of gs0 self).(ps_phase) = Active).
              { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
              assert (Hself_par_gs0 : (proc_of gs0 self).(ps_parent) = Some par).
              { unfold proc_of. rewrite <- Hpeq. exact Hpar'. }
              (* Hpar in gs0: self's parent ≠ Some n *)
              assert (Hpar0 : (proc_of gs0 self).(ps_parent) <> Some n).
              { rewrite Hself_par_gs0. intro H. apply Hpar. exact H. }
              assert (Hself_not_idle_gs0 : (proc_of gs0 self).(ps_phase) <> Idle).
              { rewrite Hself_phase_gs0. discriminate. }
              destruct (Htsno self n Hm Hn Hadj Hself_not_idle_gs0 Hpar0)
                as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
              ** left.
                 destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. rewrite Hself_phase_gs'. discriminate.
                 --- rewrite (Hother n Hnen). exact Hnph.
              ** right.
                 rewrite Hgs'eq. simpl.
                 assert (Hp'_survives : In p' (es_msgs gs_mid)).
                 { simpl. apply remove_pkt_body_ne_in; [exact Hpin | rewrite Hpb, Hbody; discriminate]. }
                 exists p'. split.
                 --- apply in_app_iff. left. exact Hp'_survives.
                 --- exact (conj Hps (conj Hpd Hpb)).
           ++ (* m ≠ self *)
              rewrite (Hother m Hnem) in Hph. rewrite (Hother m Hnem) in Hpar.
              destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
              ** left.
                 destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. rewrite Hself_phase_gs'. discriminate.
                 --- rewrite (Hother n Hnen). exact Hnph.
              ** right.
                 rewrite Hgs'eq. simpl.
                 assert (Hp'_survives : In p' (es_msgs gs_mid)).
                 { simpl. apply remove_pkt_body_ne_in; [exact Hpin | rewrite Hpb, Hbody; discriminate]. }
                 exists p'. split.
                 --- apply in_app_iff. left. exact Hp'_survives.
                 --- exact (conj Hps (conj Hpd Hpb)).
        -- (* Echo/Active, pending=1, parent=None: initiator decides *)
           set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar'. unfold decided. rewrite Hpeq. reflexivity. }
           assert (Hother : forall n0, n0 <> self ->
                     proc_of gs' n0 = proc_of gs0 n0).
           { intros n0 Hne. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n0) as [Heq | _].
             - exact (False_ind _ (Hne (eq_sym Heq))).
             - unfold proc_of. reflexivity. }
           assert (Hself_phase_gs' : (proc_of gs' self).(ps_phase) = Decided).
           { rewrite Hgs'eq. rewrite proc_of_upd. destruct (node_eq self self) as [_ | Hc].
             - simpl. reflexivity.
             - exact (False_ind _ (Hc eq_refl)). }
           destruct (node_eq m self) as [Heqm | Hnem].
           ++ (* m = self: now Decided *)
              subst m.
              rewrite Hself_phase_gs' in Hph.
              (* self is Decided, not Idle *)
              (* In gs0, self was Active with parent=None *)
              assert (Hself_phase_gs0 : (proc_of gs0 self).(ps_phase) = Active).
              { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
              assert (Hself_par_gs0 : (proc_of gs0 self).(ps_parent) = None).
              { unfold proc_of. rewrite <- Hpeq. exact Hpar'. }
              assert (Hpar0 : (proc_of gs0 self).(ps_parent) <> Some n).
              { rewrite Hself_par_gs0. discriminate. }
              assert (Hself_not_idle_gs0 : (proc_of gs0 self).(ps_phase) <> Idle).
              { rewrite Hself_phase_gs0. discriminate. }
              destruct (Htsno self n Hm Hn Hadj Hself_not_idle_gs0 Hpar0)
                as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
              ** left.
                 destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. rewrite Hself_phase_gs'. discriminate.
                 --- rewrite (Hother n Hnen). exact Hnph.
              ** right.
                 rewrite Hgs'eq. simpl.
                 exists p'. split.
                 --- simpl. apply remove_pkt_body_ne_in; [exact Hpin |].
                     rewrite Hpb, Hbody. discriminate.
                 --- exact (conj Hps (conj Hpd Hpb)).
           ++ (* m ≠ self *)
              rewrite (Hother m Hnem) in Hph. rewrite (Hother m Hnem) in Hpar.
              destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
              ** left.
                 destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. rewrite Hself_phase_gs'. discriminate.
                 --- rewrite (Hother n Hnen). exact Hnph.
              ** right.
                 rewrite Hgs'eq. simpl.
                 exists p'. split.
                 --- simpl. apply remove_pkt_body_ne_in; [exact Hpin |].
                     rewrite Hpb, Hbody. discriminate.
                 --- exact (conj Hps (conj Hpd Hpb)).
      * (* Echo/Active, pending≠1: self stays Active *)
        set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        assert (Hother : forall n0, n0 <> self ->
                  proc_of gs' n0 = proc_of gs0 n0).
        { intros n0 Hne. rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self n0) as [Heq | _].
          - exact (False_ind _ (Hne (eq_sym Heq))).
          - unfold proc_of. reflexivity. }
        assert (Hself_par_gs' : (proc_of gs' self).(ps_parent) = (proc_of gs0 self).(ps_parent)).
        { rewrite Hgs'eq. rewrite proc_of_upd. destruct (node_eq self self) as [_ | Hc].
          - simpl. unfold proc_of. rewrite <- Hpeq. reflexivity.
          - exact (False_ind _ (Hc eq_refl)). }
        assert (Hself_phase_gs' : (proc_of gs' self).(ps_phase) = Active).
        { rewrite Hgs'eq. rewrite proc_of_upd. destruct (node_eq self self) as [_ | Hc].
          - simpl. reflexivity.
          - exact (False_ind _ (Hc eq_refl)). }
        destruct (node_eq m self) as [Heqm | Hnem].
        ++ subst m.
           assert (Hself_phase_gs0 : (proc_of gs0 self).(ps_phase) = Active).
           { unfold proc_of. rewrite Hpeq in Hphase. exact Hphase. }
           assert (Hself_par_gs0 : (proc_of gs0 self).(ps_parent) = ps_parent p).
           { unfold proc_of. rewrite <- Hpeq. reflexivity. }
           rewrite Hself_par_gs' in Hpar.
           assert (Hpar0 : (proc_of gs0 self).(ps_parent) <> Some n).
           { exact Hpar. }
           assert (Hself_not_idle_gs0 : (proc_of gs0 self).(ps_phase) <> Idle).
           { rewrite Hself_phase_gs0. discriminate. }
           destruct (Htsno self n Hm Hn Hadj Hself_not_idle_gs0 Hpar0)
             as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
           ** left.
              destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. rewrite Hself_phase_gs'. discriminate.
              --- rewrite (Hother n Hnen). exact Hnph.
           ** right.
              rewrite Hgs'eq. simpl.
              exists p'. split.
              --- simpl. apply remove_pkt_body_ne_in; [exact Hpin |].
                  rewrite Hpb, Hbody. discriminate.
              --- exact (conj Hps (conj Hpd Hpb)).
        ++ rewrite (Hother m Hnem) in Hph. rewrite (Hother m Hnem) in Hpar.
           destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
           ** left.
              destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. rewrite Hself_phase_gs'. discriminate.
              --- rewrite (Hother n Hnen). exact Hnph.
           ** right.
              rewrite Hgs'eq. simpl.
              exists p'. split.
              --- simpl. apply remove_pkt_body_ne_in; [exact Hpin |].
                  rewrite Hpb, Hbody. discriminate.
              --- exact (conj Hps (conj Hpd Hpb)).

    (* ===== Echo / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hph. rewrite (Hother m) in Hpar.
      destruct (Htsno m n Hm Hn Hadj Hph Hpar) as [Hnph | [p' [Hpin [Hps [Hpd Hpb]]]]].
      * left. rewrite (Hother n). exact Hnph.
      * right.
        unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. simpl.
        exists p'. split.
        -- apply remove_pkt_body_ne_in; [exact Hpin |].
           rewrite Hpb, Hbody. discriminate.
        -- exact (conj Hps (conj Hpd Hpb)).
Qed.

Theorem token_sent_or_notidle_holds : is_invariant ELts token_sent_or_notidle.
Proof.
  apply invariant_by_induction.
  - apply token_sent_or_notidle_base.
  - intros gs lbl gs' Hinv Hstep.
    exact (token_sent_or_notidle_step gs lbl gs' Hinv Hstep).
Qed.

(* ================================================================== *)
(** ** Invariant C: parent_is_active *)

(** If n is m's parent, then n is Active or Decided. *)
Definition parent_is_active (gs : EState) : Prop :=
  forall m, In m all_nodes ->
    forall n, (proc_of gs m).(ps_parent) = Some n ->
    (proc_of gs n).(ps_phase) = Active \/ (proc_of gs n).(ps_phase) = Decided.

Lemma parent_is_active_base : forall gs, lts_init ELts gs -> parent_is_active gs.
Proof.
  intros gs [Hproc _] m _ n Hpar.
  unfold proc_of in Hpar. rewrite Hproc in Hpar. simpl in Hpar. discriminate.
Qed.

Lemma parent_is_active_step gs lbl gs' :
    parent_is_active gs ->
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    parent_is_active gs'.
Proof.
  intros Hparent_active Htoken_src_not_idle Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_phase : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m Hm n Hpar.
    destruct (node_eq m initiator) as [Heqm | Hnem].
    + (* m = initiator: parent = None after step_start *)
      subst m.
      assert (Hpar' : (proc_of gs' initiator).(ps_parent) = None).
      { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
      rewrite Hpar' in Hpar. discriminate.
    + (* m ≠ initiator: proc unchanged *)
      rewrite (Hother m Hnem) in Hpar.
      destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
      * (* n was Active in gs0 *)
        destruct (node_eq n initiator) as [Heqn | Hnen].
        -- subst n. left. exact Hinit_phase.
        -- left. rewrite (Hother n Hnen). exact Hact.
      * (* n was Decided in gs0 *)
        destruct (node_eq n initiator) as [Heqn | Hnen].
        -- (* initiator just became Active, so n is Active *)
           subst n. left. exact Hinit_phase.
        -- right. rewrite (Hother n Hnen). exact Hdec.

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros m Hm n Hpar.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* ===== Token / Idle ===== *)
    + assert (Hself_phase : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall n0, n0 <> self -> proc_of gs' n0 = proc_of gs0 n0).
      { intros n0 Hne.
        unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      destruct (node_eq m self) as [Heqm | Hnem].
      * (* m = self: parent just became Some sender *)
        subst m.
        rewrite Hself_par in Hpar.
        injection Hpar as <-.
        (* Need: sender is Active or Decided *)
        (* sender sent Token(sender, self), so by token_src_not_idle, sender was non-Idle in gs0 *)
        assert (Hsender_not_idle : (proc_of gs0 sender).(ps_phase) <> Idle).
        { exact (Htoken_src_not_idle pkt Hin Hbody). }
        (* sender ≠ self: if sender = self, token_src_not_idle says self was non-Idle, contradicting Hphase *)
        assert (Hsender_ne_self : sender <> self).
        { intro Heq.
          apply Hsender_not_idle. rewrite Heq. unfold proc_of.
          change (es_procs gs0 self) with p. exact Hphase. }
        (* sender's proc unchanged in gs' *)
        rewrite (Hother sender Hsender_ne_self).
        (* sender non-Idle in gs0: either Active or Decided *)
        destruct (ps_phase (proc_of gs0 sender)) eqn:Hph_sender.
        -- exact (False_ind _ (Hsender_not_idle eq_refl)).
        -- left. reflexivity.
        -- right. reflexivity.
      * (* m ≠ self: parent unchanged *)
        rewrite (Hother m Hnem) in Hpar.
        destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
        -- destruct (node_eq n self) as [Heqn | Hnen].
           ++ subst n. left. exact Hself_phase.
           ++ left. rewrite (Hother n Hnen). exact Hact.
        -- destruct (node_eq n self) as [Heqn | Hnen].
           ++ subst n. left. exact Hself_phase.
           ++ right. rewrite (Hother n Hnen). exact Hdec.

    (* ===== Token / Active: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hpar.
      destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.

    (* ===== Token / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hpar.
      destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.

    (* ===== Echo / Idle: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hpar.
      destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.

    (* ===== Echo / Active ===== *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar'.
        -- set (new_p := mkProc Active (Some par) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar'. unfold new_p. rewrite Hpeq. reflexivity. }
           assert (Hother : forall n0, n0 <> self -> proc_of gs' n0 = proc_of gs0 n0).
           { intros n0 Hne. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n0) as [Heq | _].
             - exact (False_ind _ (Hne (eq_sym Heq))).
             - unfold proc_of. reflexivity. }
           assert (Hself_par_gs' : (proc_of gs' self).(ps_parent) = Some par).
           { rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self self) as [_ | Hc]; [simpl; reflexivity | exact (False_ind _ (Hc eq_refl))]. }
           assert (Hself_phase_gs' : (proc_of gs' self).(ps_phase) = Active).
           { rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self self) as [_ | Hc]; [simpl; reflexivity | exact (False_ind _ (Hc eq_refl))]. }
           destruct (node_eq m self) as [Heqm | Hnem].
           ++ subst m.
              rewrite Hself_par_gs' in Hpar.
              injection Hpar as <-.
              (* Now n has been replaced by par in the goal *)
              assert (Hpar_gs0 : (proc_of gs0 self).(ps_parent) = Some par).
              { unfold proc_of. rewrite <- Hpeq. exact Hpar'. }
              destruct (Hparent_active self Hm par Hpar_gs0) as [Hact | Hdec].
              ** (* par is Active in gs0 *)
                 left.
                 destruct (node_eq par self) as [Heqn | Hnen].
                 --- subst par. exact Hself_phase_gs'.
                 --- rewrite (Hother par Hnen). exact Hact.
              ** (* par is Decided in gs0 *)
                 destruct (node_eq par self) as [Heqn | Hnen].
                 --- subst par. left. exact Hself_phase_gs'.
                 --- right. rewrite (Hother par Hnen). exact Hdec.
           ++ rewrite (Hother m Hnem) in Hpar.
              destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
              ** left.
                 destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. exact Hself_phase_gs'.
                 --- rewrite (Hother n Hnen). exact Hact.
              ** destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. left. exact Hself_phase_gs'.
                 --- right. rewrite (Hother n Hnen). exact Hdec.
        -- set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar'. unfold decided. rewrite Hpeq. reflexivity. }
           assert (Hother : forall n0, n0 <> self -> proc_of gs' n0 = proc_of gs0 n0).
           { intros n0 Hne. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n0) as [Heq | _].
             - exact (False_ind _ (Hne (eq_sym Heq))).
             - unfold proc_of. reflexivity. }
           assert (Hself_phase_gs' : (proc_of gs' self).(ps_phase) = Decided).
           { rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self self) as [_ | Hc]; [simpl; reflexivity | exact (False_ind _ (Hc eq_refl))]. }
           assert (Hself_par_gs' : (proc_of gs' self).(ps_parent) = None).
           { rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self self) as [_ | Hc]; [simpl; reflexivity | exact (False_ind _ (Hc eq_refl))]. }
           destruct (node_eq m self) as [Heqm | Hnem].
           ++ subst m. rewrite Hself_par_gs' in Hpar. discriminate.
           ++ rewrite (Hother m Hnem) in Hpar.
              destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
              ** destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. right. exact Hself_phase_gs'.
                 --- left. rewrite (Hother n Hnen). exact Hact.
              ** destruct (node_eq n self) as [Heqn | Hnen].
                 --- subst n. right. exact Hself_phase_gs'.
                 --- right. rewrite (Hother n Hnen). exact Hdec.

      * set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        assert (Hother : forall n0, n0 <> self -> proc_of gs' n0 = proc_of gs0 n0).
        { intros n0 Hne. rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self n0) as [Heq | _].
          - exact (False_ind _ (Hne (eq_sym Heq))).
          - unfold proc_of. reflexivity. }
        assert (Hself_par_gs' : (proc_of gs' self).(ps_parent) = (proc_of gs0 self).(ps_parent)).
        { rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self self) as [_ | Hc].
          - simpl. unfold proc_of. rewrite <- Hpeq. reflexivity.
          - exact (False_ind _ (Hc eq_refl)). }
        assert (Hself_phase_gs' : (proc_of gs' self).(ps_phase) = Active).
        { rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self self) as [_ | Hc]; [simpl; reflexivity | exact (False_ind _ (Hc eq_refl))]. }
        destruct (node_eq m self) as [Heqm | Hnem].
        ++ subst m.
           rewrite Hself_par_gs' in Hpar.
           destruct (Hparent_active self Hm n Hpar) as [Hact | Hdec].
           ** left.
              destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. exact Hself_phase_gs'.
              --- rewrite (Hother n Hnen). exact Hact.
           ** destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. left. exact Hself_phase_gs'.
              --- right. rewrite (Hother n Hnen). exact Hdec.
        ++ rewrite (Hother m Hnem) in Hpar.
           destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
           ** left.
              destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. exact Hself_phase_gs'.
              --- rewrite (Hother n Hnen). exact Hact.
           ** destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. left. exact Hself_phase_gs'.
              --- right. rewrite (Hother n Hnen). exact Hdec.

    (* ===== Echo / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hpar.
      destruct (Hparent_active m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.
Qed.

Theorem parent_is_active_holds : is_invariant ELts parent_is_active.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => parent_is_active gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. split; [apply parent_is_active_base | apply token_src_not_idle_base]; exact Hi.
    - intros gs lbl gs' [Hparent_active Htoken_src_not_idle] Hstep. split.
      + exact (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(* ================================================================== *)
(** ** pkt_nodes_in_all_nodes and parent_in_all_nodes *)

(** Every packet in the bag has src and dst in all_nodes. *)
Definition pkt_nodes_in_all_nodes (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) ->
    In (ep_src pkt) all_nodes /\ In (ep_dst pkt) all_nodes.

(** Every parent pointer points into all_nodes. *)
Definition parent_in_all_nodes (gs : EState) : Prop :=
  forall n par, (proc_of gs n).(ps_parent) = Some par -> In par all_nodes.

Lemma pkt_nodes_in_all_nodes_base : forall gs, lts_init ELts gs ->
    pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs.
Proof.
  intros gs [Hproc Hmsgs]. split.
  - intros pkt Hin. rewrite Hmsgs in Hin. contradiction.
  - intros n par Hpar. unfold proc_of in Hpar. rewrite Hproc in Hpar. simpl in Hpar. discriminate.
Qed.

(** Combined step: prove pkt_nodes_in_all_nodes and parent_in_all_nodes together
    so each can use the other. *)
Lemma pkt_nodes_in_all_nodes_step gs lbl gs' :
    pkt_nodes_in_all_nodes gs ->
    parent_in_all_nodes gs ->
    lts_trans ELts gs lbl gs' ->
    pkt_nodes_in_all_nodes gs' /\ parent_in_all_nodes gs'.
Proof.
  intros Hpkt_in_all_nodes Hparent_in_all_nodes Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    split.
    + (* pkt_nodes_in_all_nodes gs' *)
      intros pkt' Hpin'.
      unfold gs', initiator_start in Hpin'. simpl in Hpin'.
      apply in_app_iff in Hpin' as [Hold | Hnew].
      * exact (Hpkt_in_all_nodes pkt' Hold).
      * apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
        rewrite Hsrc. split.
        -- exact initiator_in_nodes.
        -- exact (filter_subset _ all_nodes _ Hdst).
    + (* parent_in_all_nodes gs' *)
      intros n par Hpar.
      destruct (node_eq n initiator) as [-> | Hne].
      * rewrite Hinit_par in Hpar. discriminate.
      * rewrite (Hother n Hne) in Hpar. exact (Hparent_in_all_nodes n par Hpar).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    assert (Hsender_in : In sender all_nodes) by exact (proj1 (Hpkt_in_all_nodes pkt Hin)).
    assert (Hself_in   : In self   all_nodes) by exact (proj2 (Hpkt_in_all_nodes pkt Hin)).
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* ===== Token / Idle ===== *)
    + (* self gets parent = Some sender; new msgs = old ++ [Echo or Tokens] *)
      assert (Hother : forall n, n <> self -> proc_of gs' n = proc_of gs0 n).
      { intros n Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      split.
      * (* pkt_nodes_in_all_nodes gs' *)
        intros pkt' Hpin'.
        unfold gs', handle_msg in Hpin'. change (es_procs gs_mid self) with p in Hpin'.
        rewrite Hbody, Hphase in Hpin'.
        set (fwds := filter (fun x => if node_eq x (ep_src pkt) then false else true)
                            (nbrs all_nodes adj self)) in *.
        destruct (Nat.eqb (length fwds) 0) eqn:Hleaf; simpl in Hpin'.
        -- apply in_app_iff in Hpin' as [Hold | Hnew].
           ++ exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hold)).
           ++ destruct Hnew as [<- | []]. simpl. exact (conj Hself_in Hsender_in).
        -- apply in_app_iff in Hpin' as [Hold | Hnew].
           ++ exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hold)).
           ++ apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
              rewrite Hsrc. split.
              ** exact Hself_in.
              ** exact (filter_subset _ all_nodes _ (filter_subset _ _ _ Hdst)).
      * (* parent_in_all_nodes gs' *)
        intros n par Hpar.
        destruct (node_eq n self) as [-> | Hne].
        -- rewrite Hself_par in Hpar. injection Hpar as <-. exact Hsender_in.
        -- rewrite (Hother n Hne) in Hpar. exact (Hparent_in_all_nodes n par Hpar).

    (* ===== Token / Active: msgs = old ++ [Echo(self,sender)]; procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        apply in_app_iff in Hpin' as [Hold | Hnew].
        -- exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hold)).
        -- destruct Hnew as [<- | []]. simpl. exact (conj Hself_in Hsender_in).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hparent_in_all_nodes n par Hpar).

    (* ===== Token/Decided: procs unchanged, msgs shrink ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hpin')).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hparent_in_all_nodes n par Hpar).

    (* ===== Echo/Idle: procs unchanged, msgs shrink ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hpin')).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hparent_in_all_nodes n par Hpar).

    (* ===== Echo / Active ===== *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
        -- (* pending=1, parent=Some par0: Echo(self→par0) added *)
           set (new_p := mkProc Active (Some par0) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. unfold new_p. rewrite Hpeq. reflexivity. }
           (* par0 ∈ all_nodes: from parent_in_all_nodes (Hparent_in_all_nodes) applied to (self, par0) *)
           assert (Hpar0_in : In par0 all_nodes).
           { apply (Hparent_in_all_nodes self par0). unfold proc_of. rewrite Hpeq in Hpar0. exact Hpar0. }
           assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
           { intros n. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             - subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             - unfold proc_of. reflexivity. }
           split.
           ++ (* pkt_nodes_in_all_nodes gs' *)
              intros pkt' Hpin'. rewrite Hgs'eq in Hpin'. simpl in Hpin'.
              apply in_app_iff in Hpin' as [Hold | Hnew].
              ** exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hold)).
              ** destruct Hnew as [<- | []]. simpl. exact (conj Hself_in Hpar0_in).
           ++ (* parent_in_all_nodes gs' *)
              intros n par Hpar.
              rewrite (Hagree n) in Hpar. exact (Hparent_in_all_nodes n par Hpar).
        -- (* pending=1, parent=None: initiator decides *)
           set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. unfold decided. rewrite Hpeq. reflexivity. }
           assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
           { intros n. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             - subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             - unfold proc_of. reflexivity. }
           split.
           ++ intros pkt' Hpin'. rewrite Hgs'eq in Hpin'. simpl in Hpin'.
              exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hpin')).
           ++ intros n par Hpar. rewrite (Hagree n) in Hpar. exact (Hparent_in_all_nodes n par Hpar).
      * (* pending ≠ 1: no new msgs *)
        set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
        { intros n. rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self n) as [Heq | Hne].
          - subst n. simpl. unfold proc_of. reflexivity.
          - unfold proc_of. reflexivity. }
        split.
        -- intros pkt' Hpin'. rewrite Hgs'eq in Hpin'. simpl in Hpin'.
           exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hpin')).
        -- intros n par Hpar. rewrite (Hagree n) in Hpar. exact (Hparent_in_all_nodes n par Hpar).

    (* ===== Echo/Decided: procs unchanged, msgs shrink ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        exact (Hpkt_in_all_nodes pkt' (remove_pkt_in _ _ _ Hpin')).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hparent_in_all_nodes n par Hpar).
Qed.

Theorem pkt_nodes_in_all_nodes_holds : is_invariant ELts pkt_nodes_in_all_nodes.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs)).
  { apply invariant_by_induction.
    - intro gs. exact (pkt_nodes_in_all_nodes_base gs).
    - intros gs lbl gs' [Hpkt_in_all_nodes Hparent_in_all_nodes] Hstep.
      exact (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

Theorem parent_in_all_nodes_holds : is_invariant ELts parent_in_all_nodes.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs)).
  { apply invariant_by_induction.
    - intro gs. exact (pkt_nodes_in_all_nodes_base gs).
    - intros gs lbl gs' [Hpkt_in_all_nodes Hparent_in_all_nodes] Hstep.
      exact (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep). }
  intros gs Hr. exact (proj2 (Hcomb gs Hr)).
Qed.

(* ================================================================== *)
(** ** no_mutual_parent: no two nodes are mutual parents *)

Definition no_mutual_parent_prop (gs : EState) : Prop :=
  forall m par,
    (proc_of gs m).(ps_parent) = Some par ->
    (proc_of gs par).(ps_parent) <> Some m.

Lemma no_mutual_parent_base : forall gs, lts_init ELts gs -> no_mutual_parent_prop gs.
Proof.
  intros gs [Hproc _] m par Hpar.
  unfold proc_of in Hpar. rewrite Hproc in Hpar. simpl in Hpar. discriminate.
Qed.

Lemma no_mutual_parent_step gs lbl gs' :
    no_mutual_parent_prop gs ->
    parent_is_active gs ->
    pkt_nodes_in_all_nodes gs ->
    valid_packets gs ->
    lts_trans ELts gs lbl gs' ->
    no_mutual_parent_prop gs'.
Proof.
  intros Hno_mutual_parent Hparent_active Hpkt_in_all_nodes Hvpkt Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m par Hpar Hcontra.
    destruct (node_eq m initiator) as [Heqm | Hnem].
    + subst m. rewrite Hinit_par in Hpar. discriminate.
    + rewrite (Hother m Hnem) in Hpar.
      destruct (node_eq par initiator) as [Heqp | Hnep].
      * subst par. rewrite Hinit_par in Hcontra. discriminate.
      * rewrite (Hother par Hnep) in Hcontra.
        exact (Hno_mutual_parent m par Hpar Hcontra).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    assert (Hsender_in : In sender all_nodes) by exact (proj1 (Hpkt_in_all_nodes pkt Hin)).
    intros m par Hpar Hcontra.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* Token / Idle: self gets parent = Some sender *)
    + assert (Hother : forall n, n <> self -> proc_of gs' n = proc_of gs0 n).
      { intros n Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      destruct (node_eq m self) as [Heqm | Hnem].
      * subst m. rewrite Hself_par in Hpar. injection Hpar as <-.
        destruct (node_eq sender self) as [Hseq | Hsne].
        { (* sender = self: adj self self = true (from valid_packets) but adj_irrefl says false *)
          subst sender.
          (* ep_src pkt = self, ep_dst pkt = self, so valid_packets gives adj self self = true *)
          assert (Hadj_ss : adj self self = true).
          { assert (Hv := Hvpkt pkt Hin).
            unfold self in *. rewrite Hseq in Hv. exact Hv. }
          rewrite adj_irrefl in Hadj_ss. discriminate. }
        rewrite (Hother sender Hsne) in Hcontra.
        destruct (Hparent_active sender Hsender_in self Hcontra) as [Hact | Hdec].
        { unfold proc_of in Hact. rewrite <- Hpeq in Hact. rewrite Hphase in Hact. discriminate. }
        { unfold proc_of in Hdec. rewrite <- Hpeq in Hdec. rewrite Hphase in Hdec. discriminate. }
      * rewrite (Hother m Hnem) in Hpar.
        destruct (node_eq par self) as [Heqp | Hnep].
        { (* par = self: Hpar says parent(gs0 m) = Some self;
             Hcontra says parent(gs' self) = Some m;
             Hself_par says parent(gs' self) = Some sender;
             so sender = m; then Hparent_active m gives phase(gs0 self) Active/Decided,
             contradicting Hphase : phase(gs0 self) = Idle *)
          subst par. rewrite Hself_par in Hcontra. injection Hcontra as Hmend.
          (* Hmend : sender = m; rewrite in Hpar *)
          rewrite <- Hmend in Hpar.
          destruct (Hparent_active sender Hsender_in self Hpar) as [Hact | Hdec].
          - unfold proc_of in Hact. rewrite <- Hpeq in Hact. rewrite Hphase in Hact. discriminate.
          - unfold proc_of in Hdec. rewrite <- Hpeq in Hdec. rewrite Hphase in Hdec. discriminate. }
        { rewrite (Hother par Hnep) in Hcontra.
          exact (Hno_mutual_parent m par Hpar Hcontra). }

    (* Token/Active, Token/Decided, Echo/Idle, Echo/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hno_mutual_parent m par Hpar Hcontra).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hno_mutual_parent m par Hpar Hcontra).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hno_mutual_parent m par Hpar Hcontra).

    (* Echo / Active: parent pointers agree with pre-state *)
    + assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
      { intros n.
        destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
        * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
          -- assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                                 (mkProc Active (Some par0) (Nat.pred (ps_pending p))
                                         (ep_src pkt :: ps_children p)))
                                                 (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
             { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
               rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
             rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             + subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             + unfold proc_of. reflexivity.
          -- assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                                 (mkProc Decided None 0 (ep_src pkt :: ps_children p)))
                                                 (es_msgs gs_mid)).
             { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
               rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
             rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             + subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             + unfold proc_of. reflexivity.
        * assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                               (mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                                       (ep_src pkt :: ps_children p)))
                                               (es_msgs gs_mid)).
          { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
            rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
          rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self n) as [Heq | Hne].
          + subst n. simpl. unfold proc_of. reflexivity.
          + unfold proc_of. reflexivity. }
      rewrite (Hagree m) in Hpar. rewrite (Hagree par) in Hcontra.
      exact (Hno_mutual_parent m par Hpar Hcontra).

    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hno_mutual_parent m par Hpar Hcontra).
Qed.

Theorem no_mutual_parent_holds : is_invariant ELts no_mutual_parent_prop.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => no_mutual_parent_prop gs /\ parent_is_active gs /\
               pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs /\
               token_src_not_idle gs /\ INV gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      refine (conj (no_mutual_parent_base gs Hi) (conj (parent_is_active_base gs Hi) (conj _ (conj _ (conj (token_src_not_idle_base gs Hi) (INV_init gs Hi)))))).
      + exact (proj1 (pkt_nodes_in_all_nodes_base gs Hi)).
      + exact (proj2 (pkt_nodes_in_all_nodes_base gs Hi)).
    - intros gs lbl gs' [Hno_mutual_parent [Hparent_active [Hpkt_in_all_nodes [Hparent_in_all_nodes [Htoken_src_not_idle Hinv]]]]] Hstep.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      + exact (no_mutual_parent_step gs lbl gs' Hno_mutual_parent Hparent_active Hpkt_in_all_nodes (proj1 (proj2 (proj2 Hinv))) Hstep).
      + exact (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep).
      + exact (proj1 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (proj2 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep).
      + destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hin Heq].
        * exact (INV_step_start gs0 Hinv Hph).
        * exact (INV_step_deliver gs0 pkt gs0' Hinv Hin Heq). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(* ================================================================== *)
(** ** §8. Pending-chain argument: no Token reaches an Idle node when decided

    Strategy: maintain a battery of state invariants about Tokens, Echoes, children
    lists, and pending counts.  Together they let us prove that Token(m→n) in the
    bag ∧ n Idle ⟹ pending(m) >= 1 ⟹ (up the parent chain) ⟹ pending(initiator) >= 1
    ⟹ initiator cannot yet be Decided — contradiction. *)

(* ------------------------------------------------------------------ *)
(** *** echo_src_not_idle: Echo senders are never Idle. *)

Definition echo_src_not_idle (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Echo ->
    (proc_of gs (ep_src pkt)).(ps_phase) <> Idle.

Lemma echo_src_not_idle_base : forall gs, lts_init ELts gs -> echo_src_not_idle gs.
Proof.
  intros gs [_ Hmsgs] pkt Hin _.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma echo_src_not_idle_step gs lbl gs' :
    echo_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    echo_src_not_idle gs'.
Proof.
  intros Hecho_src_not_idle Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_active : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros pkt' Hpin Hbp.
    unfold gs', initiator_start in Hpin. simpl in Hpin.
    apply in_app_iff in Hpin as [Hold | Hnew].
    + (* old packet *)
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Hecho_src_not_idle pkt' Hold Hbp).
      destruct (node_eq (ep_src pkt') initiator) as [Heq | Hne].
      * rewrite Heq in Hne_idle. exact (False_ind _ (Hne_idle Hph0)).
      * rewrite (Hother _ Hne). exact Hne_idle.
    + (* new Token packet from step_start has body Token, not Echo *)
      apply send_to_all_inv in Hnew as [_ [_ Hbody]].
      rewrite Hbody in Hbp. discriminate.

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros pkt' Hpin Hbp.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* Token/Idle *)
    + assert (Hself_active : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall n, n <> self -> proc_of gs' n = proc_of gs0 n).
      { intros n Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin.
      set (fwds := filter (fun x => if node_eq x (ep_src pkt) then false else true)
                          (nbrs all_nodes adj self)) in *.
      destruct (Nat.eqb (length fwds) 0) eqn:Hleaf; simpl in Hpin.
      * apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Hecho_src_not_idle pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq | Hne].
           ++ rewrite Heq in Hne_idle. unfold proc_of in Hne_idle.
              rewrite <- Hpeq in Hne_idle. exact (False_ind _ (Hne_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact Hne_idle.
        -- (* new Echo(self→sender): src=self, now Active *)
           destruct Hnew as [<- | []]. simpl ep_src. rewrite Hself_active. discriminate.
      * apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Hecho_src_not_idle pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq | Hne].
           ++ rewrite Heq in Hne_idle. unfold proc_of in Hne_idle.
              rewrite <- Hpeq in Hne_idle. exact (False_ind _ (Hne_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact Hne_idle.
        -- (* new Token packets: body = Token ≠ Echo *)
           apply send_to_all_inv in Hnew as [_ [_ Hbody2]].
           rewrite Hbody2 in Hbp. discriminate.

    (* Token/Active: procs unchanged; new Echo(self→sender) has body=Echo, src=self=Active *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hself_active : (proc_of gs0 self).(ps_phase) = Active).
      { unfold proc_of. rewrite <- Hpeq. exact Hphase. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply in_app_iff in Hpin as [Hold | Hnew].
      * apply remove_pkt_in in Hold.
        assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
          by exact (Hecho_src_not_idle pkt' Hold Hbp).
        unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.
      * destruct Hnew as [<- | []]. simpl ep_src.
        unfold proc_of. rewrite Hgs'_procs. rewrite <- Hpeq. rewrite Hphase. discriminate.

    (* Token/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Hecho_src_not_idle pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.

    (* Echo/Idle: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Hecho_src_not_idle pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.

    (* Echo/Active *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par |] eqn:Hpar.
        -- set (new_p := mkProc Active (Some par) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold new_p. rewrite Hpeq. reflexivity. }
           rewrite Hgs'eq in Hpin. simpl in Hpin.
           apply in_app_iff in Hpin as [Hold | Hnew].
           ++ apply remove_pkt_in in Hold.
              assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
                by exact (Hecho_src_not_idle pkt' Hold Hbp).
              rewrite Hgs'eq. rewrite proc_of_upd.
              destruct (node_eq self (ep_src pkt')) as [Heq | Hne].
              ** simpl. discriminate.
              ** unfold proc_of in Hne_idle. exact Hne_idle.
           ++ destruct Hnew as [<- | []]. simpl ep_src. rewrite Hgs'eq.
              rewrite proc_of_upd.
              destruct (node_eq self self) as [_ | Hc]; [simpl; discriminate |
                exact (False_ind _ (Hc eq_refl))].
        -- set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar. unfold decided. rewrite Hpeq. reflexivity. }
           rewrite Hgs'eq in Hpin. simpl in Hpin.
           apply remove_pkt_in in Hpin.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Hecho_src_not_idle pkt' Hpin Hbp).
           rewrite Hgs'eq. rewrite proc_of_upd.
           destruct (node_eq self (ep_src pkt')) as [Heq | Hne].
           ++ simpl. discriminate.
           ++ unfold proc_of in Hne_idle. exact Hne_idle.
      * set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        rewrite Hgs'eq in Hpin. simpl in Hpin.
        apply remove_pkt_in in Hpin.
        assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
          by exact (Hecho_src_not_idle pkt' Hpin Hbp).
        rewrite Hgs'eq. rewrite proc_of_upd.
        destruct (node_eq self (ep_src pkt')) as [Heq | Hne].
        ++ simpl. discriminate.
        ++ unfold proc_of in Hne_idle. exact Hne_idle.

    (* Echo/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Hecho_src_not_idle pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.
Qed.

Theorem echo_src_not_idle_holds : is_invariant ELts echo_src_not_idle.
Proof.
  apply invariant_by_induction.
  - apply echo_src_not_idle_base.
  - intros gs lbl gs' Hinv Hstep.
    exact (echo_src_not_idle_step gs lbl gs' Hinv Hstep).
Qed.

(* ------------------------------------------------------------------ *)
(** *** idle_not_in_children: Idle nodes never appear in any children list. *)

Definition idle_not_in_children (gs : EState) : Prop :=
  forall m n,
    (proc_of gs n).(ps_phase) = Idle ->
    ~ In n (proc_of gs m).(ps_children).

Lemma idle_not_in_children_base : forall gs, lts_init ELts gs -> idle_not_in_children gs.
Proof.
  intros gs [Hproc _] m n _ Hin.
  unfold proc_of in Hin. rewrite Hproc in Hin. simpl in Hin. contradiction.
Qed.

Lemma idle_not_in_children_step gs lbl gs' :
    idle_not_in_children gs ->
    token_src_not_idle gs ->
    echo_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    idle_not_in_children gs'.
Proof.
  intros Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_active : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_children : (proc_of gs' initiator).(ps_children) = []).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m n Hn_idle Hin_child.
    destruct (node_eq m initiator) as [-> | Hne].
    + rewrite Hinit_children in Hin_child. contradiction.
    + rewrite (Hother m Hne) in Hin_child.
      destruct (node_eq n initiator) as [-> | Hnen].
      * rewrite Hinit_active in Hn_idle. discriminate.
      * rewrite (Hother n Hnen) in Hn_idle.
        exact (Hidle_not_in_children m n Hn_idle Hin_child).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros m n Hn_idle Hin_child.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* Token/Idle: self gets Active, children = [] *)
    + assert (Hself_children : (proc_of gs' self).(ps_children) = []).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_active : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      destruct (node_eq m self) as [-> | Hne].
      * rewrite Hself_children in Hin_child. contradiction.
      * rewrite (Hother m Hne) in Hin_child.
        destruct (node_eq n self) as [-> | Hnen].
        -- rewrite Hself_active in Hn_idle. discriminate.
        -- rewrite (Hother n Hnen) in Hn_idle.
           exact (Hidle_not_in_children m n Hn_idle Hin_child).

    (* Token/Active: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hidle_not_in_children m n Hn_idle Hin_child).

    (* Token/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hidle_not_in_children m n Hn_idle Hin_child).

    (* Echo/Idle: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hidle_not_in_children m n Hn_idle Hin_child).

    (* Echo/Active: sender added to children(self) *)
    + (* The key case: sender is the echo sender; sender was Active (non-Idle) *)
      assert (Hsender_not_idle : (proc_of gs0 sender).(ps_phase) <> Idle).
      { exact (Hecho_src_not_idle pkt Hin Hbody). }
      destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
        -- (* pending=1, parent=Some par0 *)
           set (new_p := mkProc Active (Some par0) (Nat.pred (ps_pending p))
                                (sender :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. unfold new_p. rewrite Hpeq. reflexivity. }
           (* Determine n's idle status in gs0 *)
           assert (Hn_idle0 : (proc_of gs0 n).(ps_phase) = Idle).
           { destruct (node_eq n self) as [-> | Hnen].
             - (* n = self: after Echo/Active with par0, self is Active *)
               rewrite Hgs'eq in Hn_idle. rewrite proc_of_upd in Hn_idle.
               destruct (node_eq self self) as [_ | Hc]; [simpl in Hn_idle; discriminate |
                 exact (False_ind _ (Hc eq_refl))].
             - (* n ≠ self: proc_of gs' n = proc_of gs0 n *)
               rewrite Hgs'eq in Hn_idle. rewrite proc_of_upd in Hn_idle.
               destruct (node_eq self n) as [Heq | _]; [exact (False_ind _ (Hnen (eq_sym Heq))) |].
               unfold proc_of in Hn_idle. exact Hn_idle. }
           destruct (node_eq m self) as [-> | Hne].
           ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
              destruct (node_eq self self) as [_ | Hc]; [| exact (False_ind _ (Hc eq_refl))].
              simpl in Hin_child. unfold new_p in Hin_child. simpl in Hin_child.
              destruct Hin_child as [<- | Hrest].
              ** exact (Hsender_not_idle Hn_idle0).
              ** exact (Hidle_not_in_children self n Hn_idle0 Hrest).
           ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
              destruct (node_eq self m) as [Heq | _].
              ** exact (False_ind _ (Hne (eq_sym Heq))).
              ** unfold proc_of in *. simpl in Hin_child.
                 exact (Hidle_not_in_children m n Hn_idle0 Hin_child).
        -- (* pending=1, parent=None: initiator decides *)
           set (decided := mkProc Decided None 0 (sender :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. unfold decided. rewrite Hpeq. reflexivity. }
           (* Determine n's idle status in gs0 *)
           assert (Hn_idle0 : (proc_of gs0 n).(ps_phase) = Idle).
           { destruct (node_eq n self) as [-> | Hnen].
             - rewrite Hgs'eq in Hn_idle. rewrite proc_of_upd in Hn_idle.
               destruct (node_eq self self) as [_ | Hc]; [simpl in Hn_idle; discriminate |
                 exact (False_ind _ (Hc eq_refl))].
             - rewrite Hgs'eq in Hn_idle. rewrite proc_of_upd in Hn_idle.
               destruct (node_eq self n) as [Heq | _]; [exact (False_ind _ (Hnen (eq_sym Heq))) |].
               unfold proc_of in Hn_idle. exact Hn_idle. }
           destruct (node_eq m self) as [-> | Hne].
           ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
              destruct (node_eq self self) as [_ | Hc]; [| exact (False_ind _ (Hc eq_refl))].
              simpl in Hin_child. unfold decided in Hin_child. simpl in Hin_child.
              destruct Hin_child as [<- | Hrest].
              ** exact (Hsender_not_idle Hn_idle0).
              ** exact (Hidle_not_in_children self n Hn_idle0 Hrest).
           ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
              destruct (node_eq self m) as [Heq | _].
              ** exact (False_ind _ (Hne (eq_sym Heq))).
              ** unfold proc_of in *. simpl in Hin_child.
                 exact (Hidle_not_in_children m n Hn_idle0 Hin_child).
      * (* pending ≠ 1 *)
        set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (sender :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        (* Determine n's idle status in gs0 *)
        assert (Hn_idle0 : (proc_of gs0 n).(ps_phase) = Idle).
        { destruct (node_eq n self) as [-> | Hnen].
          - rewrite Hgs'eq in Hn_idle. rewrite proc_of_upd in Hn_idle.
            destruct (node_eq self self) as [_ | Hc]; [simpl in Hn_idle; discriminate |
              exact (False_ind _ (Hc eq_refl))].
          - rewrite Hgs'eq in Hn_idle. rewrite proc_of_upd in Hn_idle.
            destruct (node_eq self n) as [Heq | _]; [exact (False_ind _ (Hnen (eq_sym Heq))) |].
            unfold proc_of in Hn_idle. exact Hn_idle. }
        destruct (node_eq m self) as [-> | Hne].
        ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
           destruct (node_eq self self) as [_ | Hc]; [| exact (False_ind _ (Hc eq_refl))].
           simpl in Hin_child. unfold new_p in Hin_child. simpl in Hin_child.
           destruct Hin_child as [<- | Hrest].
           ** exact (Hsender_not_idle Hn_idle0).
           ** exact (Hidle_not_in_children self n Hn_idle0 Hrest).
        ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
           destruct (node_eq self m) as [Heq | _].
           ** exact (False_ind _ (Hne (eq_sym Heq))).
           ** unfold proc_of in *. simpl in Hin_child.
              exact (Hidle_not_in_children m n Hn_idle0 Hin_child).

    (* Echo/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hidle_not_in_children m n Hn_idle Hin_child).
Qed.

Theorem idle_not_in_children_holds : is_invariant ELts idle_not_in_children.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => idle_not_in_children gs /\ token_src_not_idle gs /\ echo_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. refine (conj (idle_not_in_children_base gs Hi) (conj _ _)).
      + apply token_src_not_idle_base. exact Hi.
      + apply echo_src_not_idle_base. exact Hi.
    - intros gs lbl gs' [Hidle_not_in_children [Htoken_src_not_idle Hecho_src_not_idle]] Hstep.
      refine (conj _ (conj _ _)).
      + exact (idle_not_in_children_step gs lbl gs' Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hstep).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep).
      + exact (echo_src_not_idle_step gs lbl gs' Hecho_src_not_idle Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Invariant: token_dst_not_parent
    The destination of a Token packet is not the source's parent. *)

Definition token_dst_not_parent (gs : EState) : Prop :=
  forall pkt,
    In pkt (es_msgs gs) -> ep_body pkt = Token ->
    (proc_of gs (ep_src pkt)).(ps_parent) <> Some (ep_dst pkt).

Lemma token_dst_not_parent_base : forall gs, lts_init ELts gs -> token_dst_not_parent gs.
Proof.
  intros gs [_ Hmsgs] pkt Hin _.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma token_dst_not_parent_step gs lbl gs' :
    token_dst_not_parent gs ->
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    token_dst_not_parent gs'.
Proof.
  intros Htoken_dst_not_parent Htoken_src_not_idle Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros pkt' Hpin Hbp.
    unfold gs', initiator_start in Hpin. simpl in Hpin.
    apply in_app_iff in Hpin as [Hold | Hnew].
    + (* old packet *)
      assert (Hne_par := Htoken_dst_not_parent pkt' Hold Hbp).
      destruct (node_eq (ep_src pkt') initiator) as [-> | Hne].
      * rewrite Hinit_par. discriminate.
      * rewrite (Hother _ Hne). exact Hne_par.
    + (* new Token(initiator, n) *)
      apply send_to_all_inv in Hnew as [Hsrc _].
      rewrite Hsrc. rewrite Hinit_par. discriminate.

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros pkt' Hpin Hbp.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* Token/Idle: self gets parent = Some sender; new Tokens go to fwds *)
    + assert (Hother : forall n, n <> self -> proc_of gs' n = proc_of gs0 n).
      { intros n Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin.
      set (fwds := filter (fun x => if node_eq x (ep_src pkt) then false else true)
                          (nbrs all_nodes adj self)) in *.
      destruct (Nat.eqb (length fwds) 0) eqn:Hleaf; simpl in Hpin.
      * (* leaf: msgs = remove_pkt bag ++ [Echo(self,sender)] - no Tokens added *)
        apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           (* pkt' is a Token in old bag *)
           assert (Hsrc_not_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Htoken_src_not_idle pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq_src | Hne].
           ++ (* ep_src pkt' = self which was Idle → contradiction *)
              rewrite Heq_src in Hsrc_not_idle.
              unfold proc_of in Hsrc_not_idle. rewrite <- Hpeq in Hsrc_not_idle.
              exact (False_ind _ (Hsrc_not_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact (Htoken_dst_not_parent pkt' Hold Hbp).
        -- destruct Hnew as [<- | []]. simpl in Hbp. discriminate.
      * (* internal: msgs = remove_pkt bag ++ send_to_all self fwds Token *)
        apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hsrc_not_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Htoken_src_not_idle pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq_src | Hne].
           ++ (* ep_src pkt' = self which was Idle → contradiction *)
              rewrite Heq_src in Hsrc_not_idle.
              unfold proc_of in Hsrc_not_idle. rewrite <- Hpeq in Hsrc_not_idle.
              exact (False_ind _ (Hsrc_not_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact (Htoken_dst_not_parent pkt' Hold Hbp).
        -- apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
           (* pkt' = Token(self, dst) where dst ∈ fwds *)
           (* Need: parent(gs' self) ≠ Some dst *)
           rewrite Hsrc. rewrite Hself_par.
           intro H. injection H as Heq.
           (* Heq : sender = ep_dst pkt' = dst ∈ fwds *)
           (* fwds = filter (fun x => if node_eq x sender then false else true) nbrs *)
           apply filter_In in Hdst as [_ Hflt].
           (* Heq : sender = ep_dst pkt', Hflt : filter(ep_dst pkt') says true *)
           (* fwds filters out sender; ep_dst pkt' = sender by Heq contradicts filter *)
           (* Heq : sender = ep_dst pkt' *)
           (* Hflt : (if node_eq (ep_dst pkt') sender then false else true) = true *)
           (* Substituting ep_dst pkt' = sender in Hflt gives: node_eq sender sender *)
           rewrite <- Heq in Hflt.
           unfold sender in Hflt.
           (* Now Hflt : (if node_eq (ep_src pkt) (ep_src pkt) then false else true) = true *)
           destruct (node_eq (ep_src pkt) (ep_src pkt)) as [_ | Hc];
           [ exact (Bool.diff_false_true Hflt) | exact (Hc (eq_refl (ep_src pkt))) ].

    (* Token/Active: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs in Hpin. apply in_app_iff in Hpin as [Hold | Hnew].
      * unfold proc_of in *. rewrite Hgs'_procs.
        exact (Htoken_dst_not_parent pkt' (remove_pkt_in _ _ _ Hold) Hbp).
      * destruct Hnew as [<- | []]. simpl in Hbp. discriminate.

    (* Token/Decided: procs unchanged, msgs shrink (= remove_pkt) *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs in Hpin.
      assert (Hold : In pkt' (es_msgs gs0)) by exact (remove_pkt_in _ _ _ Hpin).
      unfold proc_of in *. rewrite Hgs'_procs.
      exact (Htoken_dst_not_parent pkt' Hold Hbp).

    (* Echo/Idle: procs unchanged, msgs shrink (= remove_pkt) *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs in Hpin.
      assert (Hold : In pkt' (es_msgs gs0)) by exact (remove_pkt_in _ _ _ Hpin).
      unfold proc_of in *. rewrite Hgs'_procs.
      exact (Htoken_dst_not_parent pkt' Hold Hbp).

    (* Echo/Active: parent pointers agree; msgs may add Echo or shrink *)
    + assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
      { intros n.
        destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
        * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
          -- assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                               (mkProc Active (Some par0) (Nat.pred (ps_pending p))
                                       (ep_src pkt :: ps_children p)))
                                                 (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
             { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
               rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
             rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             + subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             + unfold proc_of. reflexivity.
          -- assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                               (mkProc Decided None 0 (ep_src pkt :: ps_children p)))
                                                 (es_msgs gs_mid)).
             { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
               rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
             rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             + subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             + unfold proc_of. reflexivity.
        * assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                             (mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                                     (ep_src pkt :: ps_children p)))
                                               (es_msgs gs_mid)).
          { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
            rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
          rewrite Hgs'eq. rewrite proc_of_upd.
          destruct (node_eq self n) as [Heq | Hne].
          + subst n. simpl. unfold proc_of. reflexivity.
          + unfold proc_of. reflexivity. }
      (* For Token packets in gs', they're all from gs_mid (new pkts are Echo) *)
      assert (Htoken_in_mid : In pkt' (es_msgs gs_mid)).
      { destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
        * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
          -- assert (Hgs'eq_msgs : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self par0 Echo]).
             { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
               rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. simpl. reflexivity. }
             rewrite Hgs'eq_msgs in Hpin. apply in_app_iff in Hpin as [H | H].
             + exact H.
             + destruct H as [Hq | []]. rewrite <- Hq in Hbp. simpl in Hbp. discriminate.
          -- assert (Hgs'eq_msgs : es_msgs gs' = es_msgs gs_mid).
             { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
               rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. simpl. reflexivity. }
             rewrite Hgs'eq_msgs in Hpin. exact Hpin.
        * assert (Hgs'eq_msgs : es_msgs gs' = es_msgs gs_mid).
          { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
            rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
          rewrite Hgs'eq_msgs in Hpin. exact Hpin. }
      rewrite (Hagree (ep_src pkt')).
      exact (Htoken_dst_not_parent pkt' (remove_pkt_in _ _ _ Htoken_in_mid) Hbp).

    (* Echo/Decided: procs unchanged, msgs = remove_pkt *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs in Hpin.
      assert (Hold : In pkt' (es_msgs gs0)) by exact (remove_pkt_in _ _ _ Hpin).
      unfold proc_of in *. rewrite Hgs'_procs.
      exact (Htoken_dst_not_parent pkt' Hold Hbp).
Qed.

Theorem token_dst_not_parent_holds : is_invariant ELts token_dst_not_parent.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => token_dst_not_parent gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. split; [apply token_dst_not_parent_base | apply token_src_not_idle_base]; exact Hi.
    - intros gs lbl gs' [Htoken_dst_not_parent Htoken_src_not_idle] Hstep. split.
      + exact (token_dst_not_parent_step gs lbl gs' Htoken_dst_not_parent Htoken_src_not_idle Hstep).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Definition: act_fwds
    The set of nodes that node m forwards Tokens to (all adj neighbors
    except parent(m)). This equals the set m would use in the Token/Idle
    case if m had just received a Token. *)

Definition act_fwds (gs : EState) (m : node) : list node :=
  filter (fun n =>
    match (proc_of gs m).(ps_parent) with
    | Some p => if node_eq n p then false else adj m n
    | None   => adj m n
    end) all_nodes.

(** act_fwds has no duplicates (follows from NoDup all_nodes + filter). *)
Lemma nodup_act_fwds gs m : NoDup (act_fwds gs m).
Proof.
  apply NoDup_filter. exact nodup_nodes.
Qed.

(** n ∈ act_fwds(m) ↔ n ∈ all_nodes ∧ adj m n ∧ parent(m) ≠ Some n. *)
Lemma act_fwds_spec gs m n :
    In n (act_fwds gs m) <->
    In n all_nodes /\ adj m n = true /\ (proc_of gs m).(ps_parent) <> Some n.
Proof.
  unfold act_fwds.
  rewrite filter_In.
  split.
  - intros [Hn_in Hflt].
    refine (conj Hn_in (conj _ _)).
    + destruct ((proc_of gs m).(ps_parent)) as [p |].
      * destruct (node_eq n p) as [Heq | Hne].
        -- discriminate.
        -- exact Hflt.
      * exact Hflt.
    + destruct ((proc_of gs m).(ps_parent)) as [p |] eqn:Hpar.
      * destruct (node_eq n p) as [Heq | Hne].
        -- discriminate.
        -- intro H. injection H as <-. exact (Hne eq_refl).
      * discriminate.
  - intros [Hn_in [Hadj Hne_par]].
    split; [exact Hn_in |].
    destruct ((proc_of gs m).(ps_parent)) as [p |] eqn:Hpar.
    + destruct (node_eq n p) as [Heq | Hne].
      * exfalso. apply Hne_par. rewrite Heq. reflexivity.
      * exact Hadj.
    + exact Hadj.
Qed.

(** If gs and gs' agree on parent(m) and on adj, then act_fwds is the same. *)
Lemma act_fwds_parent_agree gs gs' m :
    (proc_of gs m).(ps_parent) = (proc_of gs' m).(ps_parent) ->
    act_fwds gs m = act_fwds gs' m.
Proof.
  intro Hagree.
  unfold act_fwds. rewrite Hagree. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Invariant: decided_pending_zero
    A Decided node has pending = 0. Only the initiator can be Decided,
    and it becomes Decided with pending explicitly set to 0. *)

Definition decided_pending_zero (gs : EState) : Prop :=
  forall n, (proc_of gs n).(ps_phase) = Decided ->
            (proc_of gs n).(ps_pending) = 0.

Lemma decided_pending_zero_base : forall gs, lts_init ELts gs -> decided_pending_zero gs.
Proof.
  intros gs [Hproc _] n Hph.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma decided_pending_zero_step gs lbl gs' :
    decided_pending_zero gs ->
    lts_trans ELts gs lbl gs' ->
    decided_pending_zero gs'.
Proof.
  intros Hdpz Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_phase : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros n Hph.
    destruct (node_eq n initiator) as [-> | Hne].
    + rewrite Hinit_phase in Hph. discriminate.
    + rewrite (Hother n Hne) in Hph.
      rewrite (Hother n Hne). exact (Hdpz n Hph).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros n Hph.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    (* Token/Idle: self becomes Active, not Decided *)
    + assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      destruct (node_eq n self) as [-> | Hne].
      * assert (Hself_active : (proc_of gs' self).(ps_phase) = Active).
        { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase.
          set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                      (nbrs all_nodes adj self))).
          destruct (Nat.eqb len0 0);
          simpl es_procs; rewrite upd_self; simpl; reflexivity. }
        rewrite Hself_active in Hph. discriminate.
      * rewrite (Hother n Hne) in Hph. rewrite (Hother n Hne). exact (Hdpz n Hph).
    (* Token/Active, Token/Decided, Echo/Idle, Echo/Decided: procs unchanged or only phase unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hdpz n Hph).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hdpz n Hph).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hdpz n Hph).
    (* Echo/Active: self gets new pending = pred(pending), possibly Decides *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
        -- (* pending=1, parent=Some par0: self stays Active *)
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                             (mkProc Active (Some par0) (Nat.pred (ps_pending p))
                                     (ep_src pkt :: ps_children p)))
                                               (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
           destruct (node_eq n self) as [-> | Hne].
           ++ rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self self) as [_ | Hc]; [simpl in Hph; discriminate |
                exact (False_ind _ (Hc eq_refl))].
           ++ rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self n) as [Heq | _]; [exact (False_ind _ (Hne (eq_sym Heq))) |].
              simpl in Hph.
              rewrite Hgs'eq. rewrite proc_of_upd.
              destruct (node_eq self n) as [Heq' | _]; [exact (False_ind _ (Hne (eq_sym Heq'))) |].
              simpl. exact (Hdpz n Hph).
        -- (* pending=1, parent=None: self becomes Decided with pending=0 *)
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                             (mkProc Decided None 0 (ep_src pkt :: ps_children p)))
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
           destruct (node_eq n self) as [-> | Hne].
           ++ rewrite Hgs'eq. rewrite proc_of_upd.
              destruct (node_eq self self) as [_ | Hc]; [simpl; reflexivity |
                exact (False_ind _ (Hc eq_refl))].
           ++ rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
              destruct (node_eq self n) as [Heq | _]; [exact (False_ind _ (Hne (eq_sym Heq))) |].
              simpl in Hph.
              rewrite Hgs'eq. rewrite proc_of_upd.
              destruct (node_eq self n) as [Heq' | _]; [exact (False_ind _ (Hne (eq_sym Heq'))) |].
              simpl. exact (Hdpz n Hph).
      * (* pending ≠ 1: self stays Active *)
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self
                           (mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                                   (ep_src pkt :: ps_children p)))
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
        destruct (node_eq n self) as [-> | Hne].
        ++ rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
           destruct (node_eq self self) as [_ | Hc]; [simpl in Hph; discriminate |
             exact (False_ind _ (Hc eq_refl))].
        ++ rewrite Hgs'eq in Hph. rewrite proc_of_upd in Hph.
           destruct (node_eq self n) as [Heq | _]; [exact (False_ind _ (Hne (eq_sym Heq))) |].
           simpl in Hph.
           rewrite Hgs'eq. rewrite proc_of_upd.
           destruct (node_eq self n) as [Heq' | _]; [exact (False_ind _ (Hne (eq_sym Heq'))) |].
           simpl. exact (Hdpz n Hph).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hdpz n Hph).
Qed.

Theorem decided_pending_zero_holds : is_invariant ELts decided_pending_zero.
Proof.
  apply invariant_by_induction.
  - apply decided_pending_zero_base.
  - intros gs lbl gs' Hdpz Hstep.
    exact (decided_pending_zero_step gs lbl gs' Hdpz Hstep).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Helper invariants for the pending-count argument *)

(** Count nodes in act_fwds(m) not yet in children(m). *)
Definition remaining_fwds (gs : EState) (m : node) : nat :=
  length (filter (fun n =>
    negb (existsb (fun c => if node_eq c n then true else false)
                  (proc_of gs m).(ps_children)))
    (act_fwds gs m)).

Definition weak_pending_ge_count (gs : EState) : Prop :=
  forall m,
    ((proc_of gs m).(ps_phase) = Active \/ (proc_of gs m).(ps_phase) = Decided) ->
    (proc_of gs m).(ps_pending) >= remaining_fwds gs m.

(** Helper: if n ∈ children then existsb returns true. *)
Lemma existsb_children_true (gs : EState) (m n : node) :
    In n (proc_of gs m).(ps_children) ->
    existsb (fun c => if node_eq c n then true else false) (proc_of gs m).(ps_children) = true.
Proof.
  intro Hin.
  apply existsb_exists. exists n. split; [exact Hin |].
  destruct (node_eq n n) as [_ | Hc]; [reflexivity | exact (False_ind _ (Hc eq_refl))].
Qed.

(** Helper: n ∉ children means negb(existsb ...) = true. *)
Lemma not_in_children_negb (gs : EState) (m n : node) :
    ~ In n (proc_of gs m).(ps_children) ->
    negb (existsb (fun c => if node_eq c n then true else false)
                  (proc_of gs m).(ps_children)) = true.
Proof.
  intro Hnin.
  apply negb_true_iff.
  apply not_true_is_false.
  intro H.
  apply existsb_exists in H as [c [Hc Heq]].
  destruct (node_eq c n) as [-> | _]; [| discriminate].
  exact (Hnin Hc).
Qed.

(** Helper: n ∈ children means negb(existsb ...) = false. *)
Lemma in_children_negb (gs : EState) (m n : node) :
    In n (proc_of gs m).(ps_children) ->
    negb (existsb (fun c => if node_eq c n then true else false)
                  (proc_of gs m).(ps_children)) = false.
Proof.
  intro Hin.
  apply negb_false_iff.
  apply existsb_children_true. exact Hin.
Qed.

(** Helper lemma: filter is non-empty iff there's an element satisfying f. *)
Lemma length_filter_pos {A} (l : list A) (f : A -> bool) :
    (exists x, In x l /\ f x = true) -> length (filter f l) >= 1.
Proof.
  intros [x [Hin Hfx]].
  induction l as [| hd tl IH].
  - contradiction.
  - simpl in Hin. simpl filter. destruct Hin as [<- | Htl].
    + rewrite Hfx. simpl. apply le_n_S, Nat.le_0_l.
    + destruct (f hd); simpl; [apply le_n_S, Nat.le_0_l | exact (IH Htl)].
Qed.

(** If n ∈ act_fwds(m) and n ∉ children(m), then remaining_fwds ≥ 1. *)
Lemma remaining_fwds_pos gs m n :
    In n (act_fwds gs m) ->
    ~ In n (proc_of gs m).(ps_children) ->
    remaining_fwds gs m >= 1.
Proof.
  intros Hin Hnin.
  unfold remaining_fwds.
  apply length_filter_pos.
  exists n. split; [exact Hin |].
  exact (not_in_children_negb gs m n Hnin).
Qed.

(* ================================================================== *)
(** *** Invariant: weak_pending_ge_count (WPEMC)

    For this we need three helper invariants proved in order.

    (A) token_from_parent_consumed (tfpc):
        parent(n) = Some p → Token(p→n) ∉ bag.
    (B) echo_src_not_par_of_dst (enspd):
        Echo(A→B) ∈ bag → parent(B) ≠ Some A.
    (C) echo_not_in_children (enic):
        Echo(A→B) ∈ bag → A ∉ children(B). *)

(** (A) token_at_most_once (tamo): each Token(src→dst) packet appears
    at most once by position in the message bag.

    We use a structural matching predicate and length-of-filter count. *)

Definition pkt_matches (p q : @echo_packet node) : bool :=
  match node_eq (ep_src p) (ep_src q) with
  | left _ =>
      match node_eq (ep_dst p) (ep_dst q) with
      | left _ =>
          match ep_body p, ep_body q with
          | Token, Token | Echo, Echo => true
          | _, _ => false
          end
      | right _ => false
      end
  | right _ => false
  end.

(** count_pkt pkt l = number of elements in l matching pkt. *)
Definition count_pkt (pkt : @echo_packet node) (l : list (@echo_packet node)) : nat :=
  length (filter (pkt_matches pkt) l).

Lemma pkt_matches_self (pkt : @echo_packet node) : pkt_matches pkt pkt = true.
Proof.
  unfold pkt_matches.
  destruct (node_eq (ep_src pkt) (ep_src pkt)) as [_ | Hc]; [| exact (False_ind _ (Hc eq_refl))].
  destruct (node_eq (ep_dst pkt) (ep_dst pkt)) as [_ | Hc]; [| exact (False_ind _ (Hc eq_refl))].
  destruct (ep_body pkt); reflexivity.
Qed.

Lemma pkt_matches_sym p q : pkt_matches p q = pkt_matches q p.
Proof.
  unfold pkt_matches.
  destruct (node_eq (ep_src p) (ep_src q)) as [Eps | Nps];
  destruct (node_eq (ep_src q) (ep_src p)) as [Eqs | Nqs].
  - destruct (node_eq (ep_dst p) (ep_dst q)) as [Epd | Npd];
    destruct (node_eq (ep_dst q) (ep_dst p)) as [Eqd | Nqd].
    + destruct (ep_body p), (ep_body q); reflexivity.
    + exact (False_ind _ (Nqd (eq_sym Epd))).
    + exact (False_ind _ (Npd (eq_sym Eqd))).
    + reflexivity.
  - exact (False_ind _ (Nqs (eq_sym Eps))).
  - exact (False_ind _ (Nps (eq_sym Eqs))).
  - reflexivity.
Qed.

Lemma count_pkt_ge_one_in pkt l :
    In pkt l -> count_pkt pkt l >= 1.
Proof.
  intro Hin.
  unfold count_pkt.
  induction l as [| hd tl IH].
  - contradiction.
  - simpl in Hin. simpl filter. destruct Hin as [<- | Htl].
    + rewrite pkt_matches_self. simpl. apply le_n_S, Nat.le_0_l.
    + destruct (pkt_matches pkt hd); simpl; [apply le_n_S, Nat.le_0_l | exact (IH Htl)].
Qed.

Lemma count_pkt_zero_notin pkt l :
    count_pkt pkt l = 0 -> ~ In pkt l.
Proof.
  intros Hz Hin.
  assert (H := count_pkt_ge_one_in pkt l Hin).
  rewrite Hz in H. inversion H.
Qed.

Lemma count_pkt_app pkt l1 l2 :
    count_pkt pkt (l1 ++ l2) = count_pkt pkt l1 + count_pkt pkt l2.
Proof.
  unfold count_pkt. rewrite filter_app. rewrite length_app. reflexivity.
Qed.

(** remove_pkt pkt removes exactly the first element matching pkt. *)
Lemma count_pkt_remove_le pkt q l :
    count_pkt pkt (remove_pkt node_eq q l) <= count_pkt pkt l.
Proof.
  induction l as [| hd tl IH].
  - simpl. reflexivity.
  - unfold count_pkt in *. simpl remove_pkt.
    destruct (node_eq (ep_src hd) (ep_src q)) as [Esrc | Nesrc].
    + destruct (node_eq (ep_dst hd) (ep_dst q)) as [Edst | Nedst].
      * destruct (ep_body hd) eqn:Hbh; destruct (ep_body q) eqn:Hbq.
        -- (* Token/Token: hd removed. Result = tl. Count(pkt,hd::tl) = Count(pkt,tl) + (if match 1 else 0). *)
           simpl filter. destruct (pkt_matches pkt hd) eqn:Hm; simpl length.
           ++ exact (Nat.le_succ_diag_r _).
           ++ exact (Nat.le_refl _).
        -- simpl filter. destruct (pkt_matches pkt hd) eqn:Hm; simpl length;
           [exact (le_n_S _ _ IH) | exact IH].
        -- simpl filter. destruct (pkt_matches pkt hd) eqn:Hm; simpl length;
           [exact (le_n_S _ _ IH) | exact IH].
        -- (* Echo/Echo: hd removed. *)
           simpl filter. destruct (pkt_matches pkt hd) eqn:Hm; simpl length.
           ++ exact (Nat.le_succ_diag_r _).
           ++ exact (Nat.le_refl _).
      * simpl filter. destruct (pkt_matches pkt hd) eqn:Hm; simpl length;
        [exact (le_n_S _ _ IH) | exact IH].
    + simpl filter. destruct (pkt_matches pkt hd) eqn:Hm; simpl length;
      [exact (le_n_S _ _ IH) | exact IH].
Qed.

(** Count of Tokens not matching given src in send_to_all is 0 if src mismatch. *)
Lemma count_pkt_src_mismatch pkt src dsts msg :
    ep_src pkt <> src ->
    count_pkt pkt (send_to_all src dsts msg) = 0.
Proof.
  intro Hne.
  induction dsts as [| d ds IH].
  - unfold count_pkt, send_to_all. simpl. reflexivity.
  - unfold count_pkt, send_to_all in *.
    simpl map.
    change (filter (pkt_matches pkt)
              ((mkPkt src d msg) :: (map (fun dst => mkPkt src dst msg) ds)))
      with
      (if pkt_matches pkt (mkPkt src d msg)
       then (mkPkt src d msg) :: filter (pkt_matches pkt) (map (fun dst => mkPkt src dst msg) ds)
       else filter (pkt_matches pkt) (map (fun dst => mkPkt src dst msg) ds)).
    assert (Hpm : pkt_matches pkt (mkPkt src d msg) = false).
    { unfold pkt_matches. simpl.
      destruct (node_eq (ep_src pkt) src) as [Heq | _].
      - exact (False_ind _ (Hne Heq)).
      - reflexivity. }
    rewrite Hpm. exact IH.
Qed.

(** Helper: no element of send_to_all src ds msg matches pkt when pkt.dst ∉ ds. *)
Lemma count_pkt_send_to_all_notin pkt src ds msg :
    ep_src pkt = src -> ep_body pkt = msg ->
    ~ In (ep_dst pkt) ds ->
    count_pkt pkt (send_to_all src ds msg) = 0.
Proof.
  intros Hsrc Hbody Hnotin.
  unfold count_pkt, send_to_all.
  induction ds as [| d ds' IH].
  - simpl. reflexivity.
  - simpl map. simpl filter.
    assert (Hpm : pkt_matches pkt (mkPkt src d msg) = false).
    { unfold pkt_matches. simpl. rewrite Hsrc.
      destruct (node_eq src src) as [_ | Hc]; [| exact (False_ind _ (Hc eq_refl))].
      destruct (node_eq (ep_dst pkt) d) as [Hed | _].
      - exfalso. apply Hnotin. left. exact (eq_sym Hed).
      - destruct (ep_body pkt), msg; reflexivity. }
    rewrite Hpm. simpl length.
    apply IH. intro H. apply Hnotin. right. exact H.
Qed.

(** For send_to_all src dsts, count of pkt is ≤ 1 if dsts is NoDup. *)
Lemma count_pkt_send_to_all_le_one pkt src dsts msg :
    ep_src pkt = src -> ep_body pkt = msg ->
    NoDup dsts ->
    count_pkt pkt (send_to_all src dsts msg) <= 1.
Proof.
  intros Hsrc Hbody Hnd.
  unfold count_pkt, send_to_all.
  induction Hnd as [| d ds Hnotin Hnd IH].
  - simpl. exact (Nat.le_0_l _).
  - simpl map. simpl filter.
    assert (Hpm_eq : pkt_matches pkt (mkPkt src d msg) =
      match node_eq (ep_dst pkt) d with
      | left _ => match ep_body pkt, msg with
                  | Token, Token | Echo, Echo => true | _, _ => false end
      | right _ => false end).
    { unfold pkt_matches. simpl. rewrite Hsrc.
      destruct (node_eq src src); [| contradiction]. reflexivity. }
    rewrite Hpm_eq.
    destruct (node_eq (ep_dst pkt) d) as [Hed | Hned].
    + destruct (ep_body pkt) eqn:Hbp; destruct msg eqn:Hm; try discriminate.
      * (* Token/Token: dst = d, remaining ds has pkt.dst ∉ ds (by NoDup) *)
        assert (Hzero : count_pkt pkt (send_to_all src ds Token) = 0).
        { apply count_pkt_send_to_all_notin; [exact Hsrc | exact Hbp |].
          intro H. apply Hnotin. rewrite <- Hed. exact H. }
        unfold count_pkt, send_to_all in Hzero. simpl.
        rewrite Hzero. apply Nat.le_refl.
      * (* Echo/Echo: dst = d, remaining ds has pkt.dst ∉ ds *)
        assert (Hzero : count_pkt pkt (send_to_all src ds Echo) = 0).
        { apply count_pkt_send_to_all_notin; [exact Hsrc | exact Hbp |].
          intro H. apply Hnotin. rewrite <- Hed. exact H. }
        unfold count_pkt, send_to_all in Hzero. simpl.
        rewrite Hzero. apply Nat.le_refl.
    + destruct (ep_body pkt), msg; simpl length; exact IH.
Qed.

(** No Token appears at the same (src,dst) twice. *)
Definition token_at_most_once (gs : EState) : Prop :=
  forall pkt, ep_body pkt = Token -> count_pkt pkt (es_msgs gs) <= 1.

(** Helper: removing the first occurrence of pkt strictly decreases count_pkt. *)
Lemma count_pkt_remove_pkt_self pkt l :
    In pkt l ->
    count_pkt pkt (remove_pkt node_eq pkt l) + 1 <= count_pkt pkt l.
Proof.
  induction l as [| hd tl IH].
  - intro; contradiction.
  - intro Hin.
    simpl in Hin.
    unfold count_pkt. simpl remove_pkt.
    destruct (node_eq (ep_src hd) (ep_src pkt)) as [Es | Ns].
    + destruct (node_eq (ep_dst hd) (ep_dst pkt)) as [Ed | Nd].
      * destruct (ep_body hd) eqn:Hbh; destruct (ep_body pkt) eqn:Hbp.
        -- (* Token/Token: remove hd, return tl. Goal: count(tl)+1 <= count(hd::tl)=S count(tl) *)
           assert (Hpm_hd : pkt_matches pkt hd = true).
           { unfold pkt_matches.
             destruct (node_eq (ep_src pkt) (ep_src hd)) as [_ | Hc]; [| exact (False_ind _ (Hc (eq_sym Es)))].
             destruct (node_eq (ep_dst pkt) (ep_dst hd)) as [_ | Hc]; [| exact (False_ind _ (Hc (eq_sym Ed)))].
             rewrite Hbp, Hbh. reflexivity. }
           simpl filter. rewrite Hpm_hd. simpl length.
           fold (count_pkt pkt tl).
           rewrite Nat.add_1_r. exact (Nat.le_refl _).
        -- (* Token/Echo: body mismatch, keep hd, recurse into tl *)
           assert (Hne_match : pkt_matches pkt hd = false).
           { unfold pkt_matches.
             destruct (node_eq (ep_src pkt) (ep_src hd)) as [_ | Hc]; [| reflexivity].
             destruct (node_eq (ep_dst pkt) (ep_dst hd)) as [_ | Hc]; [| reflexivity].
             rewrite Hbp, Hbh. reflexivity. }
           simpl filter. rewrite Hne_match. simpl length.
           fold (count_pkt pkt tl).
           destruct Hin as [<- | Htl].
           ++ rewrite pkt_matches_self in Hne_match. discriminate.
           ++ exact (IH Htl).
        -- (* Echo/Token: body mismatch, keep hd, recurse into tl *)
           assert (Hne_match : pkt_matches pkt hd = false).
           { unfold pkt_matches.
             destruct (node_eq (ep_src pkt) (ep_src hd)) as [_ | Hc]; [| reflexivity].
             destruct (node_eq (ep_dst pkt) (ep_dst hd)) as [_ | Hc]; [| reflexivity].
             rewrite Hbp, Hbh. reflexivity. }
           simpl filter. rewrite Hne_match. simpl length.
           fold (count_pkt pkt tl).
           destruct Hin as [<- | Htl].
           ++ rewrite pkt_matches_self in Hne_match. discriminate.
           ++ exact (IH Htl).
        -- (* Echo/Echo: remove hd, return tl. Goal: count(tl)+1 <= count(hd::tl)=S count(tl) *)
           assert (Hpm_hd : pkt_matches pkt hd = true).
           { unfold pkt_matches.
             destruct (node_eq (ep_src pkt) (ep_src hd)) as [_ | Hc]; [| exact (False_ind _ (Hc (eq_sym Es)))].
             destruct (node_eq (ep_dst pkt) (ep_dst hd)) as [_ | Hc]; [| exact (False_ind _ (Hc (eq_sym Ed)))].
             rewrite Hbp, Hbh. reflexivity. }
           simpl filter. rewrite Hpm_hd. simpl length.
           fold (count_pkt pkt tl).
           rewrite Nat.add_1_r. exact (Nat.le_refl _).
      * (* dst mismatch: keep hd, recurse. *)
        assert (Hne_match : pkt_matches pkt hd = false).
        { unfold pkt_matches.
          destruct (node_eq (ep_src pkt) (ep_src hd)) as [_ | Hc]; [| reflexivity].
          destruct (node_eq (ep_dst pkt) (ep_dst hd)) as [He | _]; [| reflexivity].
          exact (False_ind _ (Nd (eq_sym He))). }
        simpl filter. rewrite Hne_match.
        destruct Hin as [<- | Htl].
        -- rewrite pkt_matches_self in Hne_match. discriminate.
        -- exact (IH Htl).
    + (* src mismatch: keep hd, recurse. *)
      assert (Hne_match : pkt_matches pkt hd = false).
      { unfold pkt_matches.
        destruct (node_eq (ep_src pkt) (ep_src hd)) as [He | _]; [| reflexivity].
        exact (False_ind _ (Ns (eq_sym He))). }
      simpl filter. rewrite Hne_match.
      destruct Hin as [<- | Htl].
      -- rewrite pkt_matches_self in Hne_match. discriminate.
      -- exact (IH Htl).
Qed.

(** Key consequence: if Token pkt is in bag and tamo holds, then removing pkt leaves pkt out. *)
Lemma token_at_most_once_remove_not_in (gs : EState) (pkt : @echo_packet node) :
    token_at_most_once gs ->
    ep_body pkt = Token ->
    In pkt (es_msgs gs) ->
    ~ In pkt (remove_pkt node_eq pkt (es_msgs gs)).
Proof.
  intros Htoken_at_most_once Hbody Hin Hin'.
  assert (H1 : count_pkt pkt (es_msgs gs) <= 1) by exact (Htoken_at_most_once pkt Hbody).
  assert (H2 : count_pkt pkt (es_msgs gs) >= 1) by exact (count_pkt_ge_one_in pkt _ Hin).
  assert (Heq1 : count_pkt pkt (es_msgs gs) = 1).
  { apply Nat.le_antisymm; [exact H1 | exact H2]. }
  assert (H3 : count_pkt pkt (remove_pkt node_eq pkt (es_msgs gs)) >= 1)
    by exact (count_pkt_ge_one_in pkt _ Hin').
  assert (H4 : count_pkt pkt (remove_pkt node_eq pkt (es_msgs gs)) + 1 <=
               count_pkt pkt (es_msgs gs))
    by exact (count_pkt_remove_pkt_self pkt (es_msgs gs) Hin).
  rewrite Heq1 in H4. rewrite Nat.add_comm in H4. simpl in H4.
  (* H3 : 1 <= count, H4 : S count <= 1. Combined: S count <= 1 <= count. *)
  set (count := count_pkt pkt (remove_pkt node_eq pkt (es_msgs gs))).
  assert (HScount_le_count : S count <= count).
  { apply Nat.le_trans with (m := 1); [exact H4 | exact H3]. }
  exact (Nat.lt_irrefl count (Nat.lt_le_trans count (S count) count
           (Nat.lt_succ_diag_r count) HScount_le_count)).
Qed.

Lemma token_at_most_once_base : forall gs, lts_init ELts gs -> token_at_most_once gs.
Proof.
  intros gs [_ Hmsgs] pkt _.
  unfold count_pkt. rewrite Hmsgs. simpl. exact (Nat.le_0_l _).
Qed.

(** Helper: if no packet in list has ep_src matching pkt_src with same body and matching src,
    then count_pkt pkt l = 0. *)
Lemma count_pkt_zero_if_no_match pkt l :
    (forall q, In q l -> pkt_matches pkt q = false) ->
    count_pkt pkt l = 0.
Proof.
  intro Hno.
  unfold count_pkt.
  induction l as [| hd tl IH].
  - simpl. reflexivity.
  - simpl filter. rewrite (Hno hd (or_introl eq_refl)).
    simpl length. apply IH.
    intros q Hq. exact (Hno q (or_intror Hq)).
Qed.

(** Count of pkt is 0 when pkt.src is Idle (no Token from idle in bag). *)
Lemma token_at_most_once_count_idle_src gs pkt :
    token_src_not_idle gs ->
    ep_body pkt = Token ->
    (proc_of gs (ep_src pkt)).(ps_phase) = Idle ->
    count_pkt pkt (es_msgs gs) = 0.
Proof.
  intros Htoken_src_not_idle Hbody Hidle.
  apply count_pkt_zero_if_no_match.
  intros q Hq.
  unfold pkt_matches.
  destruct (node_eq (ep_src pkt) (ep_src q)) as [Hsrc | _]; [| reflexivity].
  destruct (node_eq (ep_dst pkt) (ep_dst q)) as [_ | _]; [| reflexivity].
  destruct (ep_body pkt) eqn:Hbp; [| rewrite Hbody in Hbp; discriminate].
  destruct (ep_body q) eqn:Hbq; [| reflexivity].
  exfalso. apply (Htoken_src_not_idle q Hq Hbq).
  rewrite <- Hsrc. exact Hidle.
Qed.

Lemma token_at_most_once_step gs lbl gs' :
    token_at_most_once gs ->
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    token_at_most_once gs'.
Proof.
  intros Htoken_at_most_once Htoken_src_not_idle Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - (* new msgs = old ++ send_to_all init nbrs Token *)
    intros pkt2 Hbody2.
    unfold initiator_start. simpl es_msgs.
    rewrite count_pkt_app.
    set (my_nbrs := nbrs all_nodes adj initiator).
    destruct (node_eq (ep_src pkt2) initiator) as [Hsrc | Hnsrc].
    + (* pkt2.src = initiator: no old Token(init→x) (init was Idle) *)
      assert (Hidle_src : (proc_of gs0 (ep_src pkt2)).(ps_phase) = Idle).
      { unfold proc_of. simpl. rewrite Hsrc. exact Hph0. }
      rewrite (token_at_most_once_count_idle_src gs0 pkt2 Htoken_src_not_idle Hbody2 Hidle_src).
      simpl Nat.add.
      apply count_pkt_send_to_all_le_one.
      * exact Hsrc.
      * exact Hbody2.
      * apply NoDup_filter. exact nodup_nodes.
    + (* pkt2.src ≠ initiator: new tokens have src=init, old ≤ 1 *)
      rewrite (count_pkt_src_mismatch pkt2 initiator my_nbrs Token Hnsrc).
      rewrite Nat.add_0_r.
      exact (Htoken_at_most_once pkt2 Hbody2).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros pkt2 Hbody2.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* Token/Idle: adds Tokens(self→fwds) or Echo(self→sender). *)
    + set (fwds := filter (fun x => if node_eq x sender then false else true)
                          (nbrs all_nodes adj self)).
      assert (Hgs'_msgs :
        es_msgs gs' =
        remove_pkt node_eq pkt (es_msgs gs0) ++
          (if Nat.eqb (length fwds) 0
           then [mkPkt self sender Echo]
           else send_to_all self fwds Token)).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. unfold fwds.
        destruct (Nat.eqb _ 0); reflexivity. }
      rewrite Hgs'_msgs. rewrite count_pkt_app.
      (* Part 1: count in remove_pkt ≤ count in old ≤ 1 *)
      assert (H1 : count_pkt pkt2 (remove_pkt node_eq pkt (es_msgs gs0)) <=
                   count_pkt pkt2 (es_msgs gs0))
        by exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)).
      assert (H2 : count_pkt pkt2 (es_msgs gs0) <= 1) by exact (Htoken_at_most_once pkt2 Hbody2).
      (* Part 2: count in new_extra *)
      destruct (Nat.eqb (length fwds) 0) eqn:Hleaf.
      * (* Leaf: new = [Echo]. Token count = 0. *)
        assert (Hecho_count : count_pkt pkt2 [mkPkt self sender Echo] = 0).
        { apply count_pkt_zero_if_no_match. intros q [<- | []].
          unfold pkt_matches. simpl.
          destruct (node_eq (ep_src pkt2) self) as [_ | _]; [| reflexivity].
          destruct (node_eq (ep_dst pkt2) sender) as [_ | _]; [| reflexivity].
          rewrite Hbody2. reflexivity. }
        rewrite Hecho_count. rewrite Nat.add_0_r.
        apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)); [exact H1 | exact H2].
      * (* Internal: new = send_to_all self fwds Token *)
        destruct (node_eq (ep_src pkt2) self) as [Hsrc2 | Hnsrc2].
        -- (* pkt2.src = self: old count = 0 (self was Idle) *)
           assert (Hc0 : count_pkt pkt2 (es_msgs gs0) = 0).
           { apply token_at_most_once_count_idle_src; [exact Htoken_src_not_idle | exact Hbody2 |].
             unfold proc_of. rewrite Hsrc2. rewrite <- Hpeq. simpl. exact Hphase. }
           rewrite Hc0 in H1. apply Nat.le_0_r in H1. rewrite H1.
           apply count_pkt_send_to_all_le_one.
           ++ exact Hsrc2.
           ++ exact Hbody2.
           ++ apply NoDup_filter, NoDup_filter. exact nodup_nodes.
        -- rewrite (count_pkt_src_mismatch pkt2 self fwds Token Hnsrc2).
           rewrite Nat.add_0_r.
           apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)); [exact H1 | exact H2].

    (* Token/Active: adds Echo(self→sender). No new Tokens. *)
    + assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0) ++ [mkPkt self sender Echo]).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs, count_pkt_app.
      assert (H1 : count_pkt pkt2 (remove_pkt node_eq pkt (es_msgs gs0)) <= 1).
      { apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)]. }
      assert (Hecho_count : count_pkt pkt2 [mkPkt self sender Echo] = 0).
      { apply count_pkt_zero_if_no_match. intros q [<- | []].
        unfold pkt_matches. simpl.
        destruct (node_eq (ep_src pkt2) self) as [_ | _]; [| reflexivity].
        destruct (node_eq (ep_dst pkt2) sender) as [_ | _]; [| reflexivity].
        rewrite Hbody2. reflexivity. }
      rewrite Hecho_count. rewrite Nat.add_0_r. exact H1.

    (* Token/Decided: no new msgs (drop token). *)
    + assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs.
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)].

    (* Echo/Idle: drop. *)
    + assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs.
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)].

    (* Echo/Active: possibly adds Echo(self→par). No new Tokens. *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
        -- assert (Hgs'_msgs : es_msgs gs' =
                    remove_pkt node_eq pkt (es_msgs gs0) ++ [mkPkt self par0 Echo]).
           { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
           rewrite Hgs'_msgs, count_pkt_app.
           assert (H1 : count_pkt pkt2 (remove_pkt node_eq pkt (es_msgs gs0)) <= 1).
           { apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
             [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)]. }
           assert (Hecho_count : count_pkt pkt2 [mkPkt self par0 Echo] = 0).
           { apply count_pkt_zero_if_no_match. intros q [<- | []].
             unfold pkt_matches. simpl.
             destruct (node_eq (ep_src pkt2) self) as [_ | _]; [| reflexivity].
             destruct (node_eq (ep_dst pkt2) par0) as [_ | _]; [| reflexivity].
             rewrite Hbody2. reflexivity. }
           rewrite Hecho_count. rewrite Nat.add_0_r. exact H1.
        -- assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
           { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. rewrite Hpeq. reflexivity. }
           rewrite Hgs'_msgs.
           apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)].
      * assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
        { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
        rewrite Hgs'_msgs.
        apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)].

    (* Echo/Decided: drop. *)
    + assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs.
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htoken_at_most_once pkt2 Hbody2)].
Qed.

Theorem token_at_most_once_holds : is_invariant ELts token_at_most_once.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => token_at_most_once gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. exact (conj (token_at_most_once_base gs Hi) (token_src_not_idle_base gs Hi)).
    - intros gs lbl gs' [Htoken_at_most_once Htoken_src_not_idle] Hstep.
      exact (conj (token_at_most_once_step gs lbl gs' Htoken_at_most_once Htoken_src_not_idle Hstep)
                  (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep)). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(** (A) token_from_parent_consumed (tfpc): parent(n) = Some p → Token(p→n) ∉ bag. *)
Definition token_from_parent_consumed (gs : EState) : Prop :=
  forall n p, (proc_of gs n).(ps_parent) = Some p ->
    ~ In (mkPkt p n Token) (es_msgs gs).

Lemma token_from_parent_consumed_base : forall gs, lts_init ELts gs -> token_from_parent_consumed gs.
Proof.
  intros gs [_ Hmsgs] n p _ Hin.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma token_from_parent_consumed_step gs lbl gs' :
    token_at_most_once gs ->
    token_from_parent_consumed gs ->
    parent_is_active gs ->
    lts_trans ELts gs lbl gs' ->
    token_from_parent_consumed gs'.
Proof.
  intros Htoken_at_most_once Htoken_from_parent Hparent_active Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ---- step_start ---- *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother_proc : forall m, m <> initiator -> proc_of gs' m = proc_of gs0 m).
    { intros m Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros n p Hpar Hpin.
    destruct (node_eq n initiator) as [-> | Hne].
    + rewrite Hinit_par in Hpar. discriminate.
    + rewrite (Hother_proc n Hne) in Hpar.
      unfold gs', initiator_start in Hpin. simpl in Hpin.
      apply in_app_iff in Hpin as [Hold | Hnew].
      * exact (Htoken_from_parent n p Hpar Hold).
      * apply send_to_all_inv in Hnew as [Hsrc [Hdst Hbody]].
        assert (Heq_src : p = initiator) by exact Hsrc.
        subst p.
        (* n ∈ all_nodes since it appears as dst in send_to_all, which uses nbrs ⊆ all_nodes *)
        assert (Hn_in : In n all_nodes).
        { simpl in Hdst. exact (filter_subset _ all_nodes n Hdst). }
        destruct (Hparent_active n Hn_in initiator Hpar) as [Hact | Hdec].
        -- unfold proc_of in Hact. simpl in Hact. rewrite Hph0 in Hact. discriminate.
        -- unfold proc_of in Hdec. simpl in Hdec. rewrite Hph0 in Hdec. discriminate.

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros n par Hpar Hpin.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* Token/Idle: self.parent ← Some sender. *)
    + assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne.
        unfold gs', proc_of, handle_msg.
        change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_par_new : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase.
        set (len0 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      set (fwds := filter (fun x => if node_eq x (ep_src pkt) then false else true)
                          (nbrs all_nodes adj self)).
      destruct (node_eq n self) as [-> | Hn_ne].
      * (* n = self: par = sender. Token(sender→self) was just delivered (= pkt). *)
        rewrite Hself_par_new in Hpar. injection Hpar as Hpar_eq. symmetry in Hpar_eq. subst par.
        (* pkt = Token(sender→self). By tamo, pkt appears at most once in old.
           Since pkt IS in old (step_deliver premise), removing it leaves no copy. *)
        assert (Htoken_not_in : ~ In pkt (remove_pkt node_eq pkt (es_msgs gs0)))
          by exact (token_at_most_once_remove_not_in gs0 pkt Htoken_at_most_once Hbody Hin).
        unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
        rewrite Hbody, Hphase in Hpin.
        set (len1 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))) in Hpin.
        destruct (Nat.eqb len1 0);
        simpl in Hpin; apply in_app_iff in Hpin as [Hold | Hnew].
        -- (* pkt ∈ remove_pkt old: contradicts token_not_in *)
           exfalso. apply Htoken_not_in.
           assert (Hpkt : {| ep_src := sender; ep_dst := self; ep_body := Token |} = pkt).
           { destruct pkt as [s d b]. simpl in *. subst. reflexivity. }
           rewrite Hpkt in Hold. exact Hold.
        -- destruct Hnew as [H0 | []]. simpl in *. discriminate.
        -- exfalso. apply Htoken_not_in.
           assert (Hpkt : {| ep_src := sender; ep_dst := self; ep_body := Token |} = pkt).
           { destruct pkt as [s d b]. simpl in *. subst. reflexivity. }
           rewrite Hpkt in Hold. exact Hold.
        -- apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
           simpl in Hsrc, Hdst.
           (* Hsrc : sender = self, Hdst : In self fwds (fwds excludes sender = ep_src pkt) *)
           unfold fwds in Hdst.
           apply filter_In in Hdst as [_ Hcond].
           rewrite <- Hsrc in Hcond.
           destruct (node_eq sender (ep_src pkt)) as [_ | Hne].
           { discriminate. }
           { exfalso. apply Hne. reflexivity. }
      * (* n ≠ self: par unchanged *)
        rewrite (Hother n Hn_ne) in Hpar.
        unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
        rewrite Hbody, Hphase in Hpin.
        set (len1 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))) in Hpin.
        destruct (Nat.eqb len1 0);
        simpl in Hpin; apply in_app_iff in Hpin as [Hold | Hnew].
        -- exact (Htoken_from_parent n par Hpar (remove_pkt_in _ _ _ Hold)).
        -- destruct Hnew as [Hpkt_eq | []]. injection Hpkt_eq as _ _ Hbody_eq. discriminate.
        -- exact (Htoken_from_parent n par Hpar (remove_pkt_in _ _ _ Hold)).
        -- apply send_to_all_inv in Hnew as [Hsrc [Hpd _]].
           simpl in Hsrc, Hpd.
           (* Hsrc : par = self; Hpar : proc_of gs0 n.parent = Some par. Rewrite to get Some self.
              n ∈ all_nodes since n ∈ fwds ⊆ nbrs adj self ⊆ all_nodes *)
           assert (Hn_in : In n all_nodes).
           { apply filter_subset in Hpd.
             unfold nbrs in Hpd. apply (filter_subset _ all_nodes n Hpd). }
           rewrite Hsrc in Hpar.
           destruct (Hparent_active n Hn_in self Hpar) as [Hact | Hdec].
           ++ unfold proc_of in Hact. rewrite <- Hpeq in Hact. simpl in Hact. rewrite Hphase in Hact. discriminate.
           ++ unfold proc_of in Hdec. rewrite <- Hpeq in Hdec. simpl in Hdec. rewrite Hphase in Hdec. discriminate.

    (* Token/Active: procs unchanged, Echo added *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply in_app_iff in Hpin as [Hold | Hnew].
      * apply remove_pkt_in in Hold.
        unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
        exact (Htoken_from_parent n par Hpar Hold).
      * destruct Hnew as [Hpkt_eq | []]. injection Hpkt_eq as _ _ Hbody_eq. discriminate.

    (* Token/Decided: procs unchanged, pkt dropped *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
      exact (Htoken_from_parent n par Hpar Hpin).

    (* Echo/Idle: procs unchanged, pkt dropped *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
      exact (Htoken_from_parent n par Hpar Hpin).

    (* Echo/Active: self.children updated; possibly self becomes Decided. *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0 |] eqn:Hpar0.
        -- set (new_p := mkProc Active (Some par0) (Nat.pred (ps_pending p))
                                (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                               (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. unfold new_p. rewrite Hpeq. reflexivity. }
           assert (Hpin_old : In (mkPkt par n Token) (es_msgs gs0)).
           { rewrite Hgs'eq in Hpin. simpl in Hpin.
             apply in_app_iff in Hpin as [Hold | Hnew].
             - exact (remove_pkt_in _ _ _ Hold).
             - destruct Hnew as [Hpkt_eq | []]. injection Hpkt_eq as _ _ Hbody_eq. discriminate. }
           rewrite Hgs'eq in Hpar. rewrite proc_of_upd in Hpar.
           destruct (node_eq self n) as [-> | Hne].
           ++ simpl in Hpar. injection Hpar as Hpar_eq. subst par.
              (* parent(n=self) = Some par0 in gs0, and Token(par0→n) is in gs0. Contradiction. *)
              assert (Hpar_old : (proc_of gs0 n).(ps_parent) = Some par0).
              { unfold proc_of. rewrite <- Hpeq. exact Hpar0. }
              exact (Htoken_from_parent n par0 Hpar_old Hpin_old).
           ++ unfold proc_of in Hpar. exact (Htoken_from_parent n par Hpar Hpin_old).
        -- set (decided := mkProc Decided None 0 (ep_src pkt :: ps_children p)).
           assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self decided)
                                               (es_msgs gs_mid)).
           { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
             rewrite Hbody, Hphase, Hone, Hpar0. unfold decided. rewrite Hpeq. reflexivity. }
           assert (Hpin_old : In (mkPkt par n Token) (es_msgs gs0)).
           { rewrite Hgs'eq in Hpin. simpl in Hpin. exact (remove_pkt_in _ _ _ Hpin). }
           rewrite Hgs'eq in Hpar. rewrite proc_of_upd in Hpar.
           destruct (node_eq self n) as [-> | Hne].
           ++ simpl in Hpar. discriminate.
           ++ unfold proc_of in Hpar. exact (Htoken_from_parent n par Hpar Hpin_old).
      * set (new_p := mkProc Active (ps_parent p) (Nat.pred (ps_pending p))
                              (ep_src pkt :: ps_children p)).
        assert (Hgs'eq : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self new_p)
                                             (es_msgs gs_mid)).
        { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. unfold new_p. rewrite Hpeq. reflexivity. }
        assert (Hpin_old : In (mkPkt par n Token) (es_msgs gs0)).
        { rewrite Hgs'eq in Hpin. simpl in Hpin. exact (remove_pkt_in _ _ _ Hpin). }
        rewrite Hgs'eq in Hpar. rewrite proc_of_upd in Hpar.
        destruct (node_eq self n) as [-> | Hne].
        ++ unfold new_p in Hpar. simpl in Hpar.
           (* Hpar : ps_parent p = Some par *)
           assert (Hpar_old : (proc_of gs0 n).(ps_parent) = Some par).
           { unfold proc_of. rewrite <- Hpeq. exact Hpar. }
           exact (Htoken_from_parent n par Hpar_old Hpin_old).
        ++ unfold proc_of in Hpar. exact (Htoken_from_parent n par Hpar Hpin_old).

    (* Echo/Decided: procs unchanged, pkt dropped *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
      exact (Htoken_from_parent n par Hpar Hpin).
Qed.

Theorem token_from_parent_consumed_holds : is_invariant ELts token_from_parent_consumed.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => token_at_most_once gs /\ token_from_parent_consumed gs /\
               parent_is_active gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      exact (conj (token_at_most_once_base gs Hi)
             (conj (token_from_parent_consumed_base gs Hi)
             (conj (parent_is_active_base gs Hi) (token_src_not_idle_base gs Hi)))).
    - intros gs lbl gs' [Htoken_at_most_once [Htoken_from_parent [Hparent_active Htoken_src_not_idle]]] Hstep.
      exact (conj (token_at_most_once_step gs lbl gs' Htoken_at_most_once Htoken_src_not_idle Hstep)
             (conj (token_from_parent_consumed_step gs lbl gs' Htoken_at_most_once Htoken_from_parent Hparent_active Hstep)
             (conj (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep)
                   (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep)))). }
  intros gs Hr. exact (proj1 (proj2 (Hcomb gs Hr))).
Qed.

(* ================================================================== *)
(** *** pending_pos_active: If m is Active, pending(m) >= 1, and parent(m) = par, then Echo(m→par) is not yet in the bag. *)

Definition pending_pos_active (gs : EState) : Prop :=
  forall m par,
    (proc_of gs m).(ps_phase) = Active ->
    (proc_of gs m).(ps_parent) = Some par ->
    (proc_of gs m).(ps_pending) >= 1 ->
    ~ In (mkPkt m par Echo) (es_msgs gs) /\
    ~ In m (proc_of gs par).(ps_children).

Lemma pending_pos_active_base : forall gs, lts_init ELts gs -> pending_pos_active gs.
Proof.
  intros gs [Hproc _] m par Hph _ _.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma pending_pos_active_step gs lbl gs' :
    pending_pos_active gs -> token_from_parent_consumed gs ->
    idle_not_in_children gs -> echo_src_not_idle gs ->
    valid_packets gs -> parent_is_neighbor gs ->
    lts_trans ELts gs lbl gs' -> pending_pos_active gs'.
Proof.
  intros Hpending_pos Htoken_from_parent Hidle_not_in_children Hecho_src_not_idle Hvp Hpin Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m par Hph Hpar Hpend.
    destruct (node_eq m initiator) as [-> | Hne]; [rewrite Hinit_par in Hpar; discriminate|].
    rewrite (Hother m Hne) in Hph, Hpar, Hpend.
    destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]. split.
    + unfold gs', initiator_start. simpl. intro H. apply in_app_iff in H as [Ho|Hn].
      * exact (Hecho Ho).
      * apply send_to_all_inv in Hn as [_ [_ Hb]]. simpl in Hb. discriminate.
    + destruct (node_eq par initiator) as [-> | Hnep].
      * unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. intro H; exact H.
      * rewrite (Hother par Hnep). exact Hchild.
  - subst gs0'.
    set (self := ep_dst pkt). set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros m par Hph Hpar Hpend.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    + (* Token/Idle *)
      set (fwds := filter (fun x => if node_eq x sender then false else true) (nbrs all_nodes adj self)).
      assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_ch : (proc_of gs' self).(ps_children) = []).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_idle : (proc_of gs0 self).(ps_phase) = Idle)
        by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
      assert (Hself_pend : (proc_of gs' self).(ps_pending) = length fwds).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        destruct (Nat.eqb (length (filter (fun x => if node_eq x sender then false else true)
                                          (nbrs all_nodes adj self))) 0) eqn:Hq;
        simpl es_procs; rewrite upd_self; simpl;
        [apply Nat.eqb_eq in Hq; exact (eq_sym Hq) | reflexivity]. }
      destruct (node_eq m self) as [-> | Hne].
      * rewrite Hself_par in Hpar; injection Hpar as <-. rewrite Hself_pend in Hpend.
        destruct (Nat.eqb (length fwds) 0) eqn:Hleaf.
        -- apply Nat.eqb_eq in Hleaf; rewrite Hleaf in Hpend; inversion Hpend.
        -- apply Nat.eqb_neq in Hleaf.
           assert (Hmsgs : es_msgs gs' = es_msgs gs_mid ++ send_to_all self fwds Token).
           { unfold gs', handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase.
             fold sender. fold fwds. rewrite (proj2 (Nat.eqb_neq _ 0) Hleaf); reflexivity. }
           split.
           ++ rewrite Hmsgs; intro H; apply in_app_iff in H as [Ho|Hn].
              ** apply remove_pkt_in in Ho; exact (Hecho_src_not_idle (mkPkt self sender Echo) Ho eq_refl Hself_idle).
              ** apply send_to_all_inv in Hn as [_ [_ Hb]]; simpl in Hb; discriminate.
           ++ destruct (node_eq sender self) as [Heq|Hne].
              ** exfalso.
                 assert (Hadj_ss : adj sender self = true).
                 { change sender with (ep_src pkt). change self with (ep_dst pkt). exact (Hvp pkt Hin). }
                 rewrite Heq in Hadj_ss. rewrite adj_irrefl in Hadj_ss. discriminate.
              ** rewrite (Hother sender Hne); exact (Hidle_not_in_children sender self Hself_idle).
      * rewrite (Hother m Hne) in Hph, Hpar, Hpend.
        destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild].
        assert (Hmi : forall q, In q (es_msgs gs') ->
            In q (es_msgs gs_mid) \/ q = mkPkt self sender Echo \/
            (ep_src q = self /\ ep_body q = Token)).
        { intro q. unfold gs', handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase.
          fold sender.
          destruct (Nat.eqb (length (filter (fun x => if node_eq x sender then false else true)
                                            (nbrs all_nodes adj self))) 0) eqn:Hq.
          - simpl; intro H; apply in_app_iff in H as [H|H]; [left; exact H|].
            destruct H as [<-|[]]; right; left; reflexivity.
          - simpl; intro H; apply in_app_iff in H as [H|H]; [left; exact H|].
            apply send_to_all_inv in H as [Hs [_ Hb]]; right; right; simpl in *; exact (conj Hs Hb). }
        split.
        -- intro H; apply Hmi in H as [Ho|[Heq|[Hs _]]].
           ++ exact (Hecho (remove_pkt_in _ _ _ Ho)).
           ++ injection Heq as Hms _; exact (Hne Hms).
           ++ simpl in Hs; exact (Hne Hs).
        -- destruct (node_eq par self) as [-> | Hnep].
           ++ rewrite Hself_ch; intro H; exact H.
           ++ rewrite (Hother par Hnep); exact Hchild.
    + (* Token/Active *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      assert (Hmg : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hph, Hpar, Hpend; rewrite Hpr in Hph, Hpar, Hpend.
      destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
      * rewrite Hmg; intro H; apply in_app_iff in H as [Ho|Hn].
        -- exact (Hecho (remove_pkt_in _ _ _ Ho)).
        -- destruct Hn as [Heq|[]]; injection Heq as Hms Hds; subst m par.
           assert (He : pkt = mkPkt sender self Token).
           { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
           rewrite He in Hin; exact (Htoken_from_parent self sender Hpar Hin).
      * unfold proc_of; rewrite Hpr; exact Hchild.
    + (* Token/Decided *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hph, Hpar, Hpend; rewrite Hpr in Hph, Hpar, Hpend.
      destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
      * intro H; unfold gs' in H; unfold handle_msg in H; change (es_procs gs_mid self) with p in H;
        rewrite Hbody, Hphase in H; simpl in H; exact (Hecho (remove_pkt_in _ _ _ H)).
      * unfold proc_of; rewrite Hpr; exact Hchild.
    + (* Echo/Idle *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hph, Hpar, Hpend; rewrite Hpr in Hph, Hpar, Hpend.
      destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
      * intro H; unfold gs' in H; unfold handle_msg in H; change (es_procs gs_mid self) with p in H;
        rewrite Hbody, Hphase in H; simpl in H; exact (Hecho (remove_pkt_in _ _ _ H)).
      * unfold proc_of; rewrite Hpr; exact Hchild.
    + (* Echo/Active *)
      destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0|] eqn:Hpar0.
        -- set (np := mkProc Active (Some par0) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np)
                                            (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold np; rewrite Hpeq; reflexivity. }
           assert (Hz : Nat.pred (ps_pending p) = 0) by
             (apply Nat.eqb_eq in Hone; rewrite Hone; simpl; reflexivity).
           destruct (node_eq m self) as [-> | Hne].
           ++ rewrite Hge, proc_of_upd in Hpend.
              destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
              simpl in Hpend; rewrite Hz in Hpend; inversion Hpend.
           ++ rewrite Hge, proc_of_upd in Hph, Hpar, Hpend.
              destruct (node_eq self m) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
              unfold proc_of in Hph, Hpar, Hpend.
              destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
              ** rewrite Hge; simpl es_msgs; intro H; apply in_app_iff in H as [Ho|Hn].
                 --- exact (Hecho (remove_pkt_in _ _ _ Ho)).
                 --- destruct Hn as [Heq|[]]; injection Heq as Hms _; exact (Hne (eq_sym Hms)).
              ** rewrite Hge, proc_of_upd.
                 destruct (node_eq self par) as [Heq|Hnep].
                 --- simpl; unfold np; simpl; intro H; destruct H as [<-|Hr].
                     +++ assert (Hp : (proc_of gs0 sender).(ps_parent) = Some self) by (rewrite Heq; exact Hpar).
                         assert (He : pkt = mkPkt sender self Echo).
                         { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
                         rewrite He in Hin; exact (proj1 (Hpending_pos sender self Hph Hp Hpend) Hin).
                     +++ rewrite <- Heq in Hchild; exact (Hchild Hr).
                 --- unfold proc_of; exact Hchild.
        -- set (dec := mkProc Decided None 0 (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self dec) (es_msgs gs_mid)).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold dec; rewrite Hpeq; reflexivity. }
           destruct (node_eq m self) as [-> | Hne].
           ++ rewrite Hge, proc_of_upd in Hph.
              destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
              simpl in Hph; discriminate.
           ++ rewrite Hge, proc_of_upd in Hph, Hpar, Hpend.
              destruct (node_eq self m) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
              unfold proc_of in Hph, Hpar, Hpend.
              destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
              ** rewrite Hge; simpl es_msgs; intro H; exact (Hecho (remove_pkt_in _ _ _ H)).
              ** rewrite Hge, proc_of_upd.
                 destruct (node_eq self par) as [Heq|Hnep].
                 --- simpl; unfold dec; simpl; intro H; destruct H as [<-|Hr].
                     +++ assert (Hp : (proc_of gs0 sender).(ps_parent) = Some self) by (rewrite Heq; exact Hpar).
                         assert (He : pkt = mkPkt sender self Echo).
                         { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
                         rewrite He in Hin; exact (proj1 (Hpending_pos sender self Hph Hp Hpend) Hin).
                     +++ rewrite <- Heq in Hchild; exact (Hchild Hr).
                 --- unfold proc_of; exact Hchild.
      * set (np := mkProc Active (ps_parent p) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
        assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np) (es_msgs gs_mid)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
          rewrite Hbody, Hphase, Hone; unfold np; rewrite Hpeq; reflexivity. }
        destruct (node_eq m self) as [-> | Hne].
        -- rewrite Hge, proc_of_upd in Hph, Hpar, Hpend.
           destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
           simpl in Hph, Hpar, Hpend; unfold np in Hpar, Hpend; simpl in Hpar, Hpend.
           assert (Hold2 : ps_pending p >= 2).
           { apply Nat.eqb_neq in Hone.
             destruct (ps_pending p) as [|[|k]].
             - simpl in Hpend. inversion Hpend.
             - exfalso. apply Hone. reflexivity.
             - simpl. lia. }
           assert (Hpho : (proc_of gs0 self).(ps_phase) = Active)
             by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
           assert (Hparo : (proc_of gs0 self).(ps_parent) = Some par)
             by (unfold proc_of; rewrite <- Hpeq; exact Hpar).
           assert (Hpo1 : (proc_of gs0 self).(ps_pending) >= 1) by
             (unfold proc_of; rewrite <- Hpeq;
              exact (Nat.le_trans 1 2 _ (Nat.le_succ_diag_r 1) Hold2)).
           destruct (Hpending_pos self par Hpho Hparo Hpo1) as [Heo Hco]; split.
           ++ rewrite Hge; simpl es_msgs; intro H; exact (Heo (remove_pkt_in _ _ _ H)).
           ++ rewrite Hge, proc_of_upd.
              destruct (node_eq self par) as [Heq|Hnep].
              ** exfalso.
                 assert (Hps : (proc_of gs0 self).(ps_parent) = Some self)
                   by (rewrite <- Heq in Hparo; exact Hparo).
                 assert (Hadj_ss := Hpin self self Hps). rewrite adj_irrefl in Hadj_ss. discriminate.
              ** destruct (node_eq self par) as [Habs|_]; [exact (False_ind _ (Hnep Habs))|]; exact Hco.
        -- rewrite Hge, proc_of_upd in Hph, Hpar, Hpend.
           destruct (node_eq self m) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
           unfold proc_of in Hph, Hpar, Hpend.
           destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
           ++ rewrite Hge; simpl es_msgs; intro H; exact (Hecho (remove_pkt_in _ _ _ H)).
           ++ rewrite Hge, proc_of_upd.
              destruct (node_eq self par) as [Heq|Hnep].
              ** simpl; unfold np; simpl; intro H; destruct H as [<-|Hr].
                 --- assert (Hp : (proc_of gs0 sender).(ps_parent) = Some self) by (rewrite Heq; exact Hpar).
                     assert (He : pkt = mkPkt sender self Echo).
                     { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
                     rewrite He in Hin; exact (proj1 (Hpending_pos sender self Hph Hp Hpend) Hin).
                 --- rewrite <- Heq in Hchild; exact (Hchild Hr).
              ** unfold proc_of; exact Hchild.
    + (* Echo/Decided *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hph, Hpar, Hpend; rewrite Hpr in Hph, Hpar, Hpend.
      destruct (Hpending_pos m par Hph Hpar Hpend) as [Hecho Hchild]; split.
      * intro H; unfold gs' in H; unfold handle_msg in H; change (es_procs gs_mid self) with p in H;
        rewrite Hbody, Hphase in H; simpl in H; exact (Hecho (remove_pkt_in _ _ _ H)).
      * unfold proc_of; rewrite Hpr; exact Hchild.
Qed.

Theorem pending_pos_active_holds : is_invariant ELts pending_pos_active.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => pending_pos_active gs /\ token_at_most_once gs /\
               token_from_parent_consumed gs /\ parent_is_active gs /\
               idle_not_in_children gs /\ echo_src_not_idle gs /\
               token_src_not_idle gs /\ INV gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      exact (conj (pending_pos_active_base gs Hi) (conj (token_at_most_once_base gs Hi) (conj (token_from_parent_consumed_base gs Hi)
             (conj (parent_is_active_base gs Hi) (conj (idle_not_in_children_base gs Hi) (conj (echo_src_not_idle_base gs Hi)
             (conj (token_src_not_idle_base gs Hi) (INV_init gs Hi)))))))).
    - intros gs lbl gs' [Hpending_pos [Htoken_at_most_once [Htoken_from_parent [Hparent_active [Hidle_not_in_children [Hecho_src_not_idle [Htoken_src_not_idle Hinv]]]]]]] Hstep.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
      + exact (pending_pos_active_step gs lbl gs' Hpending_pos Htoken_from_parent Hidle_not_in_children Hecho_src_not_idle
                        (proj1 (proj2 (proj2 Hinv))) (proj1 (proj1 Hinv)) Hstep).
      + exact (token_at_most_once_step gs lbl gs' Htoken_at_most_once Htoken_src_not_idle Hstep).
      + exact (token_from_parent_consumed_step gs lbl gs' Htoken_at_most_once Htoken_from_parent Hparent_active Hstep).
      + exact (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep).
      + exact (idle_not_in_children_step gs lbl gs' Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hstep).
      + exact (echo_src_not_idle_step gs lbl gs' Hecho_src_not_idle Hstep).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep).
      + destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hin Heq].
        * exact (INV_step_start gs0 Hinv Hph).
        * exact (INV_step_deliver gs0 pkt gs0' Hinv Hin Heq). }
  intros gs Hr; exact (proj1 (Hcomb gs Hr)).
Qed.

(* ================================================================== *)
(** *** Helper invariants for weak_pending_ge_count *)

(** echo_dst_not_idle: Every Echo in the bag targets a non-Idle node (the destination is Active or Decided). *)
Definition echo_dst_not_idle (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Echo ->
    (proc_of gs (ep_dst pkt)).(ps_phase) <> Idle.

(** echo_token_sender_not: If Echo(A→B) is in the bag, the reverse Token(B→A) is not. *)
Definition echo_token_sender_not (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Echo ->
    ~ In (mkPkt (ep_dst pkt) (ep_src pkt) Token) (es_msgs gs).

(** children_implies_no_parent_token: If c is in m's children list, Token(m→c) is no longer in the bag (it was already delivered). *)
Definition children_implies_no_parent_token (gs : EState) : Prop :=
  forall m c, In c (proc_of gs m).(ps_children) ->
    ~ In (mkPkt m c Token) (es_msgs gs).

(** echo_not_in_children: If Echo(n→m) is still in the bag (not yet delivered), n is not yet in m's children list. *)
Definition echo_not_in_children (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Echo ->
    ~ In (ep_src pkt) (proc_of gs (ep_dst pkt)).(ps_children).

(** echo_src_in_fwds: If Echo(n→m) is in the bag, n is in m's forward-set (parent(m) ≠ n). *)
Definition echo_src_in_fwds (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Echo ->
    (proc_of gs (ep_dst pkt)).(ps_parent) <> Some (ep_src pkt).

(** pending_exact_count_ge: For every Active/Decided node, pending + |children| >= |forwards|. (This is actually equality, but >= suffices.) *)
Definition pending_exact_count_ge (gs : EState) : Prop :=
  forall m,
    ((proc_of gs m).(ps_phase) = Active \/ (proc_of gs m).(ps_phase) = Decided) ->
    (proc_of gs m).(ps_pending) + length (proc_of gs m).(ps_children) >=
    length (act_fwds gs m).

(** echo_at_most_once: Each Echo packet appears at most once in the message bag. *)
Definition echo_at_most_once (gs : EState) : Prop :=
  forall pkt, ep_body pkt = Echo -> count_pkt pkt (es_msgs gs) <= 1.

Lemma echo_at_most_once_remove_not_in (gs : EState) (pkt : @echo_packet node) :
    echo_at_most_once gs ->
    ep_body pkt = Echo ->
    In pkt (es_msgs gs) ->
    ~ In pkt (remove_pkt node_eq pkt (es_msgs gs)).
Proof.
  intros Hecho_at_most_once Hbody Hin Hin'.
  assert (H1 : count_pkt pkt (es_msgs gs) <= 1) by exact (Hecho_at_most_once pkt Hbody).
  assert (H2 : count_pkt pkt (es_msgs gs) >= 1) by exact (count_pkt_ge_one_in pkt _ Hin).
  assert (Heq1 : count_pkt pkt (es_msgs gs) = 1)
    by (apply Nat.le_antisymm; [exact H1 | exact H2]).
  assert (H3 : count_pkt pkt (remove_pkt node_eq pkt (es_msgs gs)) >= 1)
    by exact (count_pkt_ge_one_in pkt _ Hin').
  assert (H4 : count_pkt pkt (remove_pkt node_eq pkt (es_msgs gs)) + 1 <=
               count_pkt pkt (es_msgs gs))
    by exact (count_pkt_remove_pkt_self pkt (es_msgs gs) Hin).
  rewrite Heq1 in H4. rewrite Nat.add_comm in H4. simpl in H4.
  set (count := count_pkt pkt (remove_pkt node_eq pkt (es_msgs gs))).
  assert (HScount_le_count : S count <= count).
  { apply Nat.le_trans with (m := 1); [exact H4 | exact H3]. }
  exact (Nat.lt_irrefl count (Nat.lt_le_trans count (S count) count
           (Nat.lt_succ_diag_r count) HScount_le_count)).
Qed.

Lemma echo_at_most_once_base : forall gs, lts_init ELts gs -> echo_at_most_once gs.
Proof.
  intros gs [_ Hmsgs] p _. unfold count_pkt. rewrite Hmsgs. simpl. exact (Nat.le_0_l _).
Qed.

Lemma echo_at_most_once_step gs lbl gs' :
    echo_at_most_once gs ->
    echo_src_not_idle gs ->
    echo_token_sender_not gs ->
    pending_pos_active gs ->
    lts_trans ELts gs lbl gs' ->
    echo_at_most_once gs'.
Proof.
  intros Hecho_at_most_once Hecho_src_not_idle Hecho_token_sender_not Hpending_pos Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - (* step_start: new pkts are Tokens. No new Echoes. *)
    set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hmsgs : es_msgs gs' = es_msgs gs0 ++
                    send_to_all initiator (nbrs all_nodes adj initiator) Token).
    { unfold gs', initiator_start. simpl. reflexivity. }
    intros pkt2 Hbody2. rewrite Hmsgs. rewrite count_pkt_app.
    assert (Hzero : count_pkt pkt2 (send_to_all initiator (nbrs all_nodes adj initiator) Token) = 0).
    { apply count_pkt_zero_if_no_match. intros q Hq.
      apply send_to_all_inv in Hq as [_ [_ Hb]].
      (* ep_body q = Token, ep_body pkt2 = Echo → pkt_matches = false *)
      unfold pkt_matches.
      destruct (node_eq (ep_src pkt2) (ep_src q)) as [_ | _]; [| reflexivity].
      destruct (node_eq (ep_dst pkt2) (ep_dst q)) as [_ | _]; [| reflexivity].
      rewrite Hbody2, Hb. reflexivity. }
    rewrite Hzero. rewrite Nat.add_0_r. exact (Hecho_at_most_once pkt2 Hbody2).
  - subst gs0'.
    set (self := ep_dst pkt). set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros pkt2 Hbody2.
    (* Helper: count in gs0 ≤ 1 *)
    assert (Hle1 : count_pkt pkt2 (es_msgs gs0) <= 1) by exact (Hecho_at_most_once pkt2 Hbody2).
    (* Helper: count in gs_mid ≤ 1 *)
    assert (Hle_mid : count_pkt pkt2 (es_msgs gs_mid) <= 1).
    { apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
      exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). exact Hle1. }
    (* Helper: new Echo count in [single_echo] ≤ 1 *)
    assert (Hle_single : forall a b, count_pkt pkt2 [mkPkt a b Echo] <= 1).
    { intros a b. unfold count_pkt. simpl.
      destruct (pkt_matches pkt2 (mkPkt a b Echo)) eqn:Hm; simpl.
      - exact (Nat.le_refl _).
      - exact (Nat.le_0_l _). }
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    + (* Token/Idle: new msg is Echo(self→sender) OR send_to_all (Tokens). *)
      assert (Hself_idle : (proc_of gs0 self).(ps_phase) = Idle)
        by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
      set (fwds := filter (fun x => if node_eq x sender then false else true) (nbrs all_nodes adj self)).
      (* Case split: leaf (Echo added) or internal (Tokens added) *)
      destruct (Nat.eqb (length fwds) 0) eqn:Hleaf.
      * (* Leaf: gs'.msgs = gs_mid ++ [Echo(self→sender)] *)
        assert (Hmsgs : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
        { unfold gs', handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase.
          fold sender; fold fwds. rewrite Hleaf. simpl. reflexivity. }
        rewrite Hmsgs. rewrite count_pkt_app.
        (* New Echo(self→sender): old count = 0 (self was Idle, esni) *)
        assert (H0 : count_pkt pkt2 (es_msgs gs0) = 0 \/ count_pkt pkt2 [mkPkt self sender Echo] = 0).
        { (* If pkt2.src ≠ self: count in [Echo(self→sender)] = 0 (src mismatch). *)
          destruct (node_eq (ep_src pkt2) self) as [Hs|Hns].
          2: { right. apply count_pkt_zero_if_no_match. intros q [<-|[]].
               unfold pkt_matches. simpl.
               destruct (node_eq (ep_src pkt2) self) as [Habs|_]; [exact (False_ind _ (Hns Habs))|].
               reflexivity. }
          left. apply count_pkt_zero_if_no_match. intros q Hq.
          unfold pkt_matches. destruct (node_eq (ep_src pkt2) (ep_src q)) as [Hsrc|_]; [| reflexivity].
          (* pkt2.src = ep_src q. And pkt2.src = self. So ep_src q = self. q ∈ gs0.msgs.
             q body = pkt2 body = Echo. By esni: phase(self in gs0) ≠ Idle. But self IS Idle. *)
          destruct (node_eq (ep_dst pkt2) (ep_dst q)) as [_|_]; [| reflexivity].
          rewrite Hbody2. destruct (ep_body q) eqn:Hbq.
          - (* q body = Token: pkt_matches = false. ✓ *)
            reflexivity.
          - (* q body = Echo: by esni: phase(ep_src q = self) ≠ Idle. But Idle. *)
            exfalso.
            assert (Hself_q : (proc_of gs0 (ep_src q)).(ps_phase) = Idle).
            { rewrite <- Hsrc. rewrite Hs. exact Hself_idle. }
            exact (Hecho_src_not_idle q Hq Hbq Hself_q). }
        destruct H0 as [H0|H0].
        -- (* count in gs0 = 0: count in gs_mid = 0, total = 0 + count[echo] ≤ 1 *)
           assert (Hle_mid0 : count_pkt pkt2 (es_msgs gs_mid) = 0).
           { apply Nat.le_antisymm; [| exact (Nat.le_0_l _)].
             apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
             exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). rewrite H0. exact (Nat.le_refl _). }
           rewrite Hle_mid0. simpl. exact (Hle_single self sender).
        -- (* count in [echo] = 0: total = count_mid + 0 ≤ 1 *)
           rewrite H0. rewrite Nat.add_0_r. exact Hle_mid.
      * (* Internal: gs'.msgs = gs_mid ++ send_to_all self fwds Token *)
        assert (Hmsgs : es_msgs gs' = es_msgs gs_mid ++ send_to_all self fwds Token).
        { unfold gs', handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase.
          fold sender; fold fwds. rewrite Hleaf. simpl. reflexivity. }
        rewrite Hmsgs. rewrite count_pkt_app.
        assert (Hzero_tokens : count_pkt pkt2 (send_to_all self fwds Token) = 0).
        { apply count_pkt_zero_if_no_match. intros q Hq.
          apply send_to_all_inv in Hq as [_ [_ Hbq]].
          unfold pkt_matches.
          destruct (node_eq (ep_src pkt2) (ep_src q)) as [_|_]; [| reflexivity].
          destruct (node_eq (ep_dst pkt2) (ep_dst q)) as [_|_]; [| reflexivity].
          rewrite Hbody2, Hbq. reflexivity. }
        rewrite Hzero_tokens. rewrite Nat.add_0_r. exact Hle_mid.
    + (* Token/Active: gs'.msgs = gs_mid ++ [Echo(self→sender)] *)
      assert (Hmg : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      rewrite Hmg. rewrite count_pkt_app.
      (* New Echo(self→sender): old count = 0 (etsn: Token(sender→self) ∈ bag → Echo(self→sender) ∉ bag) *)
      assert (H0 : count_pkt pkt2 (es_msgs gs0) = 0 \/ count_pkt pkt2 [mkPkt self sender Echo] = 0).
      { destruct (node_eq (ep_src pkt2) self) as [Hs|Hns].
        2: { right. apply count_pkt_zero_if_no_match. intros q [<-|[]].
             unfold pkt_matches. simpl.
             destruct (node_eq (ep_src pkt2) self) as [Habs|_]; [exact (False_ind _ (Hns Habs))|]. reflexivity. }
        destruct (node_eq (ep_dst pkt2) sender) as [Hd|Hnd].
        2: { right. apply count_pkt_zero_if_no_match. intros q [<-|[]].
             unfold pkt_matches. simpl.
             destruct (node_eq (ep_src pkt2) self) as [_|Habs]; [| exact (False_ind _ (Habs Hs))].
             destruct (node_eq (ep_dst pkt2) sender) as [Habs|_]; [exact (False_ind _ (Hnd Habs))| reflexivity]. }
        (* pkt2 = Echo(self→sender). Old count = 0 from etsn. *)
        left. apply count_pkt_zero_if_no_match. intros q Hq.
        unfold pkt_matches.
        destruct (node_eq (ep_src pkt2) (ep_src q)) as [Hsrc|_]; [| reflexivity].
        destruct (node_eq (ep_dst pkt2) (ep_dst q)) as [Hdst|_]; [| reflexivity].
        rewrite Hbody2. destruct (ep_body q) eqn:Hbq; [reflexivity |].
        (* q = Echo(self→sender) in gs0.msgs. pkt_matches=true. But we need false. *)
        (* By etsn: Echo(q=self→sender) ∈ gs0 → Token(sender→self) ∉ gs0. But pkt=Token(sender→self) ∈ gs0. *)
        exfalso.
        assert (Hne := Hecho_token_sender_not q Hq Hbq). simpl in Hne.
        (* Hne : ~ In (mkPkt (ep_dst q) (ep_src q) Token) (es_msgs gs0) *)
        (* ep_dst q = sender (from Hdst and Hd: ep_dst pkt2 = sender and ep_dst pkt2 = ep_dst q) *)
        (* ep_src q = self (from Hsrc and Hs: ep_src pkt2 = self and ep_src pkt2 = ep_src q) *)
        rewrite <- Hsrc, <- Hdst in Hne. rewrite Hs, Hd in Hne.
        (* Need: In (mkPkt sender self Token) (es_msgs gs0). pkt = Token(sender→self) = Hbody.
           Hin: In pkt gs0.msgs. pkt = mkPkt sender self Token by Hbody. *)
        assert (Hpkt' : pkt = mkPkt sender self Token).
        { destruct pkt as [a b c]. simpl in Hbody, sender, self |- *. rewrite Hbody. reflexivity. }
        rewrite Hpkt' in Hin. exact (Hne Hin). }
      destruct H0 as [H0|H0].
      * (* count in gs0 = 0 *)
        assert (Hle_mid0 : count_pkt pkt2 (es_msgs gs_mid) = 0).
        { apply Nat.le_antisymm; [| exact (Nat.le_0_l _)].
          apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
          exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). rewrite H0. exact (Nat.le_refl _). }
        rewrite Hle_mid0. simpl. exact (Hle_single self sender).
      * rewrite H0. rewrite Nat.add_0_r. exact Hle_mid.
    + (* Token/Decided, Echo/Idle: msgs = remove_pkt *)
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
      { assert (Hms : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
        rewrite Hms. exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). }
      exact Hle1.
    + apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
      { assert (Hms : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
        rewrite Hms. exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). }
      exact Hle1.
    + (* Echo/Active *)
      destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0|] eqn:Hpar0.
        -- (* pending=1, parent=par0: adds Echo(self→par0) *)
           assert (Hge : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self par0 Echo]).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; rewrite Hpeq; simpl. reflexivity. }
           rewrite Hge. rewrite count_pkt_app.
           assert (H0 : count_pkt pkt2 (es_msgs gs0) = 0 \/ count_pkt pkt2 [mkPkt self par0 Echo] = 0).
           { destruct (node_eq (ep_src pkt2) self) as [Hs|Hns].
             2: { right. apply count_pkt_zero_if_no_match. intros q [<-|[]]. unfold pkt_matches. simpl.
                  destruct (node_eq (ep_src pkt2) self) as [Habs|_]; [exact (False_ind _ (Hns Habs))|]. reflexivity. }
             destruct (node_eq (ep_dst pkt2) par0) as [Hd|Hnd].
             2: { right. apply count_pkt_zero_if_no_match. intros q [<-|[]]. unfold pkt_matches. simpl.
                  destruct (node_eq (ep_src pkt2) self) as [_|Habs]; [| exact (False_ind _ (Habs Hs))].
                  destruct (node_eq (ep_dst pkt2) par0) as [Habs|_]; [exact (False_ind _ (Hnd Habs))| reflexivity]. }
             (* pkt2 = Echo(self→par0). Old count = 0 from ppa. *)
             left. apply count_pkt_zero_if_no_match. intros q Hq.
             unfold pkt_matches.
             destruct (node_eq (ep_src pkt2) (ep_src q)) as [Hsrc|_]; [| reflexivity].
             destruct (node_eq (ep_dst pkt2) (ep_dst q)) as [Hdst|_]; [| reflexivity].
             rewrite Hbody2. destruct (ep_body q) eqn:Hbq; [reflexivity |].
             (* q = Echo(self→par0) in gs0.msgs. pkt_matches=true. Need false. By ppa: Echo ∉ gs0. *)
             exfalso.
             assert (Hself_ph : (proc_of gs0 self).(ps_phase) = Active)
               by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
             assert (Hself_par : (proc_of gs0 self).(ps_parent) = Some par0)
               by (unfold proc_of; rewrite <- Hpeq; exact Hpar0).
             assert (Hpend1 : (proc_of gs0 self).(ps_pending) >= 1).
             { unfold proc_of. rewrite <- Hpeq. apply Nat.eqb_eq in Hone. rewrite Hone. simpl. exact (Nat.le_refl _). }
             assert (Hq_eq : q = mkPkt self par0 Echo).
             { destruct q as [qs qd qb]. simpl in Hsrc, Hdst, Hbq |- *.
               rewrite <- Hsrc, <- Hdst, Hbq. rewrite Hs, Hd. reflexivity. }
             rewrite Hq_eq in Hq. exact (proj1 (Hpending_pos self par0 Hself_ph Hself_par Hpend1) Hq). }
           destruct H0 as [H0|H0].
           ++ assert (Hle_mid0 : count_pkt pkt2 (es_msgs gs_mid) = 0).
              { apply Nat.le_antisymm; [| exact (Nat.le_0_l _)].
                apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
                exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). rewrite H0. exact (Nat.le_refl _). }
              rewrite Hle_mid0. simpl. exact (Hle_single self par0).
           ++ rewrite H0. rewrite Nat.add_0_r. exact Hle_mid.
        -- (* pending=1, parent=None: no new Echo *)
           apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
           { assert (Hms : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
             { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
               rewrite Hbody, Hphase, Hone, Hpar0; rewrite Hpeq; simpl. reflexivity. }
             rewrite Hms. exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). }
           exact Hle1.
      * (* pending ≠ 1: no new Echo *)
        apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
        { assert (Hms : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
          { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
            rewrite Hbody, Hphase, Hone; rewrite Hpeq. simpl. reflexivity. }
          rewrite Hms. exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). }
        exact Hle1.
    + (* Echo/Decided: msgs = remove_pkt *)
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0)).
      { assert (Hms : es_msgs gs' = remove_pkt node_eq pkt gs0.(es_msgs)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
        rewrite Hms. exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)). }
      exact Hle1.
Qed.

(** Helper: act_fwds gs' self = filter (fun n => if n=sender then false else adj self n) all_nodes
    when parent(self in gs') = Some sender. *)
Lemma act_fwds_some_eq gs m sender :
    (proc_of gs m).(ps_parent) = Some sender ->
    act_fwds gs m =
    filter (fun n => if node_eq n sender then false else adj m n) all_nodes.
Proof.
  intro Hpar. unfold act_fwds. rewrite Hpar. reflexivity.
Qed.

(** Helper: filter with adj and ne equals filter ne applied to nbrs. *)
Lemma filter_adj_ne_parent_eq (m sender : node) :
    filter (fun n => if node_eq n sender then false else adj m n) all_nodes =
    filter (fun n => if node_eq n sender then false else true) (nbrs all_nodes adj m).
Proof.
  unfold nbrs.
  generalize all_nodes as l. intro l.
  induction l as [| hd tl IH].
  - simpl. reflexivity.
  - simpl. destruct (adj m hd) eqn:Hadj; destruct (node_eq hd sender) eqn:Hne; simpl.
    + rewrite Hne. exact IH.
    + rewrite Hne. simpl. rewrite IH. reflexivity.
    + exact IH.
    + exact IH.
Qed.

(** Combined step lemma: prove 6 new invariants simultaneously. *)
Lemma token_echo_accounting_step gs lbl gs' :
    echo_dst_not_idle gs -> echo_token_sender_not gs ->
    children_implies_no_parent_token gs -> echo_not_in_children gs ->
    echo_src_in_fwds gs -> pending_exact_count_ge gs ->
    echo_at_most_once gs ->
    pending_pos_active gs -> token_at_most_once gs ->
    token_from_parent_consumed gs -> parent_is_active gs ->
    idle_not_in_children gs -> token_src_not_idle gs -> echo_src_not_idle gs ->
    pkt_nodes_in_all_nodes gs -> parent_in_all_nodes gs ->
    token_dst_not_parent gs -> no_mutual_parent_prop gs ->
    INV gs ->
    lts_trans ELts gs lbl gs' ->
    echo_dst_not_idle gs' /\ echo_token_sender_not gs' /\
    children_implies_no_parent_token gs' /\ echo_not_in_children gs' /\
    echo_src_in_fwds gs' /\ pending_exact_count_ge gs'.
Proof.
  intros Hecho_dst_not_idle Hecho_token_sender_not Hchildren_no_parent_token Hecho_not_in_children Hecho_src_in_fwds Hpending_count Hecho_at_most_once
         Hpending_pos Htoken_at_most_once Htoken_from_parent Hparent_active Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hpkt_in_all_nodes Hparent_in_all_nodes Htoken_dst_not_parent Hno_mutual_parent Hinv Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].

  (* ------------------------------------------------------------------ step_start *)
  - set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_act : (proc_of gs' initiator).(ps_phase) = Active).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_ch : (proc_of gs' initiator).(ps_children) = []).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_pend : (proc_of gs' initiator).(ps_pending) =
                         length (nbrs all_nodes adj initiator)).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hmsgs : es_msgs gs' = es_msgs gs0 ++
                    send_to_all initiator (nbrs all_nodes adj initiator) Token).
    { unfold gs', initiator_start. simpl. reflexivity. }
    assert (Hinit_idle_gs0 : (proc_of gs0 initiator).(ps_phase) = Idle).
    { unfold proc_of. simpl. exact Hph0. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + (* edni *)
      intros pkt' Hpin Hbp. rewrite Hmsgs in Hpin.
      apply in_app_iff in Hpin as [Ho|Hn].
      * assert (H := Hecho_dst_not_idle pkt' Ho Hbp).
        destruct (node_eq (ep_dst pkt') initiator) as [-> | Hne].
        -- rewrite Hinit_act. discriminate.
        -- rewrite (Hother _ Hne). exact H.
      * apply send_to_all_inv in Hn as [_ [_ Hb]]. rewrite Hb in Hbp. discriminate.
    + (* etsn *)
      intros pkt' Hpin Hbp. rewrite Hmsgs in Hpin.
      apply in_app_iff in Hpin as [Ho|Hn].
      * assert (H := Hecho_token_sender_not pkt' Ho Hbp).
        intro Htin. rewrite Hmsgs in Htin. apply in_app_iff in Htin as [Hto|Hnew].
        -- exact (H Hto).
        -- apply send_to_all_inv in Hnew as [Hsrc [_ _]]. simpl in Hsrc.
           assert (Hcontra := Hecho_dst_not_idle pkt' Ho Hbp).
           rewrite Hsrc in Hcontra. exact (Hcontra Hinit_idle_gs0).
      * apply send_to_all_inv in Hn as [_ [_ Hb]]. rewrite Hb in Hbp. discriminate.
    + (* cipt *)
      intros m c Hch.
      destruct (node_eq m initiator) as [-> | Hne].
      * rewrite Hinit_ch in Hch. contradiction.
      * rewrite (Hother m Hne) in Hch.
        assert (H := Hchildren_no_parent_token m c Hch).
        intro Hpin. rewrite Hmsgs in Hpin. apply in_app_iff in Hpin as [Ho|Hn].
        -- exact (H Ho).
        -- apply send_to_all_inv in Hn as [Hsrc [_ _]]. simpl in Hsrc. exact (Hne Hsrc).
    + (* enic *)
      intros pkt' Hpin Hbp. rewrite Hmsgs in Hpin.
      apply in_app_iff in Hpin as [Ho|Hn].
      * assert (H := Hecho_not_in_children pkt' Ho Hbp).
        destruct (node_eq (ep_dst pkt') initiator) as [-> | Hne].
        -- rewrite Hinit_ch. intro Hc; exact Hc.
        -- rewrite (Hother _ Hne). exact H.
      * apply send_to_all_inv in Hn as [_ [_ Hb]]. rewrite Hb in Hbp. discriminate.
    + (* esif *)
      intros pkt' Hpin Hbp. rewrite Hmsgs in Hpin.
      apply in_app_iff in Hpin as [Ho|Hn].
      * assert (H := Hecho_src_in_fwds pkt' Ho Hbp).
        destruct (node_eq (ep_dst pkt') initiator) as [-> | Hne].
        -- rewrite Hinit_par. discriminate.
        -- rewrite (Hother _ Hne). exact H.
      * apply send_to_all_inv in Hn as [_ [_ Hb]]. rewrite Hb in Hbp. discriminate.
    + (* pec_ge *)
      intros m Hph.
      destruct (node_eq m initiator) as [-> | Hne].
      * rewrite Hinit_pend, Hinit_ch. simpl length. rewrite Nat.add_0_r.
        unfold act_fwds. rewrite Hinit_par. apply Nat.le_refl.
      * rewrite (Hother m Hne) in Hph.
        assert (H := Hpending_count m Hph).
        assert (Hag : act_fwds gs' m = act_fwds gs0 m).
        { apply act_fwds_parent_agree. rewrite (Hother m Hne). reflexivity. }
        rewrite Hag. rewrite (Hother m Hne). exact H.
  (* ------------------------------------------------------------------ step_deliver *)
  - subst gs0'.
    set (self := ep_dst pkt). set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.

    (* ======================================== Token / Idle *)
    + set (fwds := filter (fun x => if node_eq x sender then false else true) (nbrs all_nodes adj self)).
      assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      assert (Hself_act : (proc_of gs' self).(ps_phase) = Active).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_par : (proc_of gs' self).(ps_parent) = Some sender).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_ch : (proc_of gs' self).(ps_children) = []).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        set (len0 := length (filter (fun x => if node_eq x sender then false else true)
                                    (nbrs all_nodes adj self))).
        destruct (Nat.eqb len0 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hself_idle : (proc_of gs0 self).(ps_phase) = Idle)
        by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
      assert (Hself_pend : (proc_of gs' self).(ps_pending) = length fwds).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        fold sender.
        destruct (Nat.eqb (length (filter (fun x => if node_eq x sender then false else true)
                                          (nbrs all_nodes adj self))) 0) eqn:Hq;
        simpl es_procs; rewrite upd_self; simpl;
        [apply Nat.eqb_eq in Hq; exact (eq_sym Hq) | reflexivity]. }
      assert (Hmsgs_cla : forall q, In q (es_msgs gs') ->
          In q (es_msgs gs_mid) \/ q = mkPkt self sender Echo \/
          (ep_src q = self /\ ep_body q = Token)).
      { intro q. unfold gs', handle_msg; change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. fold sender.
        destruct (Nat.eqb (length (filter (fun x => if node_eq x sender then false else true)
                                          (nbrs all_nodes adj self))) 0) eqn:Hq.
        - simpl; intro H; apply in_app_iff in H as [H|H]; [left; exact H|].
          destruct H as [<-|[]]; right; left; reflexivity.
        - simpl; intro H; apply in_app_iff in H as [H|H]; [left; exact H|].
          apply send_to_all_inv in H as [Hs [_ Hb]]; right; right; simpl in *; exact (conj Hs Hb). }
      assert (Hsender_ne_idle : (proc_of gs0 sender).(ps_phase) <> Idle)
        by exact (Htoken_src_not_idle pkt Hin Hbody).
      assert (Hsender_ne_self : sender <> self).
      { intro Heq. apply Hsender_ne_idle. rewrite Heq. unfold proc_of. rewrite <- Hpeq. exact Hphase. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * (* edni: old Echoes + new Echo(self→sender). No old Echo dst=self (self was Idle). *)
        intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|[Heq|[Hs Hbt]]].
        -- apply remove_pkt_in in Ho. assert (H := Hecho_dst_not_idle pkt' Ho Hbp).
           destruct (node_eq (ep_dst pkt') self) as [-> | Hne].
           ++ rewrite Hself_act. discriminate.
           ++ rewrite (Hother _ Hne). exact H.
        -- subst pkt'. simpl. rewrite (Hother sender Hsender_ne_self). exact Hsender_ne_idle.
        -- rewrite Hbt in Hbp. discriminate.
      * (* etsn: Echo(A→B) ∈ gs'.msgs → Token(B→A) ∉ gs'.msgs *)
        intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|[Heq|[Hs Hbt]]].
        -- apply remove_pkt_in in Ho. assert (H := Hecho_token_sender_not pkt' Ho Hbp).
           intro Htin. apply Hmsgs_cla in Htin as [Hto|[Heq|[Hs2 Hbt2]]].
           ++ exact (H (remove_pkt_in _ _ _ Hto)).
           ++ injection Heq; intros; discriminate.
           ++ (* Token(B→A) has src=self: B=self. Echo(A→self) in gs0, self Idle → edni contradiction. *)
              simpl in Hs2. assert (Hcontra := Hecho_dst_not_idle pkt' Ho Hbp).
              rewrite Hs2 in Hcontra. exact (Hcontra Hself_idle).
        -- (* pkt' = Echo(self→sender): Token(sender→self) ∉ gs'.msgs *)
           subst pkt'. simpl. intro Htin. apply Hmsgs_cla in Htin as [Hto|[Heq|[Hs2 Hbt2]]].
           ++ (* Hto : In (mkPkt sender self Token) (es_msgs gs_mid) = remove_pkt pkt gs0.msgs. *)
              assert (Hpkt_eq : pkt = mkPkt sender self Token).
              { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
              rewrite <- Hpkt_eq in Hto. exact (token_at_most_once_remove_not_in gs0 pkt Htoken_at_most_once Hbody Hin Hto).
           ++ injection Heq; intros; discriminate.
           ++ exact (Hsender_ne_self Hs2).
        -- rewrite Hbt in Hbp. discriminate.
      * (* cipt: self.children=[] → only old children matter. Token from new msgs only from self. *)
        intros m c Hch.
        destruct (node_eq m self) as [-> | Hne].
        -- rewrite Hself_ch in Hch. contradiction.
        -- rewrite (Hother m Hne) in Hch. assert (H := Hchildren_no_parent_token m c Hch).
           intro Hpin. apply Hmsgs_cla in Hpin as [Ho|[Heq|[Hs Hbt]]].
           ++ exact (H (remove_pkt_in _ _ _ Ho)).
           ++ injection Heq; intros; discriminate.
           ++ simpl in Hs. exact (Hne Hs).
      * (* enic: old Echoes IH (no old Echo dst=self). New Echo(self→sender): self∉children(sender). *)
        intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|[Heq|[Hs Hbt]]].
        -- apply remove_pkt_in in Ho. assert (H := Hecho_not_in_children pkt' Ho Hbp).
           destruct (node_eq (ep_dst pkt') self) as [-> | Hne].
           ++ rewrite Hself_ch. intro Hc; exact Hc.
           ++ rewrite (Hother _ Hne). exact H.
        -- subst pkt'. simpl. rewrite (Hother sender Hsender_ne_self).
           intro Hch.
           assert (Hpkt_eq : pkt = mkPkt sender self Token).
           { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
           rewrite Hpkt_eq in Hin. exact (Hchildren_no_parent_token sender self Hch Hin).
        -- rewrite Hbt in Hbp. discriminate.
      * (* esif: old Echoes (no old Echo dst=self). New Echo(self→sender): parent(sender)≠Some self from tdnp. *)
        intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|[Heq|[Hs Hbt]]].
        -- apply remove_pkt_in in Ho. assert (H := Hecho_src_in_fwds pkt' Ho Hbp).
           destruct (node_eq (ep_dst pkt') self) as [Heq | Hne].
           ++ (* ep_dst pkt' = self: self was Idle, contradiction with edni *)
              assert (Hcontra := Hecho_dst_not_idle pkt' Ho Hbp). rewrite Heq in Hcontra.
              exact (False_ind _ (Hcontra Hself_idle)).
           ++ rewrite (Hother _ Hne). exact H.
        -- subst pkt'. simpl. rewrite (Hother sender Hsender_ne_self).
           change sender with (ep_src pkt). change self with (ep_dst pkt).
           exact (Htoken_dst_not_parent pkt Hin Hbody).
        -- rewrite Hbt in Hbp. discriminate.
      * (* pec_ge: self Active, pending=|fwds|, children=[], act_fwds=fwds. Others IH. *)
        intros m Hph.
        destruct (node_eq m self) as [-> | Hne].
        -- rewrite Hself_pend, Hself_ch. simpl length. rewrite Nat.add_0_r.
           assert (Haf : act_fwds gs' self = fwds).
           { rewrite (act_fwds_some_eq gs' self sender Hself_par).
             exact (filter_adj_ne_parent_eq self sender). }
           rewrite Haf. apply Nat.le_refl.
        -- rewrite (Hother m Hne) in Hph.
           assert (H := Hpending_count m Hph).
           assert (Hag : act_fwds gs' m = act_fwds gs0 m).
           { apply act_fwds_parent_agree. rewrite (Hother m Hne). reflexivity. }
           rewrite Hag. rewrite (Hother m Hne). exact H.

    (* ======================================== Token / Active *)
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      assert (Hmg : es_msgs gs' = es_msgs gs_mid ++ [mkPkt self sender Echo]).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      assert (Hprf : forall q, proc_of gs' q = proc_of gs0 q)
        by (intro q; unfold proc_of; rewrite Hpr; reflexivity).
      assert (Hmg_cla : forall q, In q (es_msgs gs') ->
          In q (es_msgs gs_mid) \/ q = mkPkt self sender Echo).
      { intro q; rewrite Hmg; intro H; apply in_app_iff in H as [H|H];
        [left; exact H| destruct H as [<-|[]]; right; reflexivity]. }
      assert (Hpkt_eq : pkt = mkPkt sender self Token).
      { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
      assert (Hsender_ne_idle : (proc_of gs0 sender).(ps_phase) <> Idle)
        by exact (Htoken_src_not_idle pkt Hin Hbody).
      assert (Hself_act : (proc_of gs0 self).(ps_phase) = Active)
        by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
      assert (Hsender_ne_self : sender <> self).
      { intro Heq.
        assert (Hadj := proj1 (proj2 (proj2 Hinv)) pkt Hin).
        unfold sender, self in Heq. rewrite Heq in Hadj.
        rewrite adj_irrefl in Hadj. discriminate. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * intros pkt' Hpin Hbp. apply Hmg_cla in Hpin as [Ho|Heq].
        -- apply remove_pkt_in in Ho. rewrite Hprf. exact (Hecho_dst_not_idle pkt' Ho Hbp).
        -- subst pkt'. simpl. rewrite Hprf. exact Hsender_ne_idle.
      * intros pkt' Hpin Hbp. apply Hmg_cla in Hpin as [Ho|Heq].
        -- apply remove_pkt_in in Ho. assert (H := Hecho_token_sender_not pkt' Ho Hbp).
           intro Htin. apply Hmg_cla in Htin as [Hto|Heq].
           ++ exact (H (remove_pkt_in _ _ _ Hto)).
           ++ injection Heq; intros; discriminate.
        -- subst pkt'. simpl. intro Htin. apply Hmg_cla in Htin as [Hto|Heq].
           ++ (* Hto : In (mkPkt sender self Token) (es_msgs gs_mid) = remove_pkt pkt gs0.msgs *)
              rewrite <- Hpkt_eq in Hto. exact (token_at_most_once_remove_not_in gs0 pkt Htoken_at_most_once Hbody Hin Hto).
           ++ injection Heq; intros; discriminate.
      * intros m c Hch. rewrite Hprf in Hch. assert (H := Hchildren_no_parent_token m c Hch).
        intro Hpin. apply Hmg_cla in Hpin as [Ho|Heq].
        -- exact (H (remove_pkt_in _ _ _ Ho)).
        -- injection Heq; intros; discriminate.
      * intros pkt' Hpin Hbp. apply Hmg_cla in Hpin as [Ho|Heq].
        -- apply remove_pkt_in in Ho. rewrite Hprf. exact (Hecho_not_in_children pkt' Ho Hbp).
        -- subst pkt'. simpl. rewrite Hprf.
           intro Hch. rewrite Hpkt_eq in Hin. exact (Hchildren_no_parent_token sender self Hch Hin).
      * intros pkt' Hpin Hbp. apply Hmg_cla in Hpin as [Ho|Heq].
        -- apply remove_pkt_in in Ho. rewrite Hprf.
           exact (Hecho_src_in_fwds pkt' Ho Hbp).
        -- subst pkt'. simpl. rewrite Hprf.
           change sender with (ep_src pkt). change self with (ep_dst pkt).
           exact (Htoken_dst_not_parent pkt Hin Hbody).
      * intros m Hph. rewrite Hprf in Hph.
        assert (H := Hpending_count m Hph).
        assert (Hag : act_fwds gs' m = act_fwds gs0 m).
        { apply act_fwds_parent_agree. rewrite Hprf. reflexivity. }
        rewrite Hag. rewrite Hprf. exact H.

    (* ======================================== Token / Decided, Echo / Idle, Echo / Decided *)
    (* These three cases are identical: procs unchanged, msgs shorten by remove_pkt. *)
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      assert (Hprf : forall q, proc_of gs' q = proc_of gs0 q)
        by (intro q; unfold proc_of; rewrite Hpr; reflexivity).
      assert (Hmsub : forall q, In q (es_msgs gs') -> In q (es_msgs gs0)).
      { intro q. unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. simpl. intro H. exact (remove_pkt_in _ _ _ H). }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_dst_not_idle pkt' (Hmsub pkt' Hpin) Hbp).
      * intros pkt' Hpin Hbp. intro Htin. exact (Hecho_token_sender_not pkt' (Hmsub pkt' Hpin) Hbp (Hmsub _ Htin)).
      * intros m c Hch. rewrite Hprf in Hch. intro Htin. exact (Hchildren_no_parent_token m c Hch (Hmsub _ Htin)).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_not_in_children pkt' (Hmsub pkt' Hpin) Hbp).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_src_in_fwds pkt' (Hmsub pkt' Hpin) Hbp).
      * intros m Hph. rewrite Hprf in Hph.
        assert (H := Hpending_count m Hph).
        assert (Hag : act_fwds gs' m = act_fwds gs0 m) by
          (apply act_fwds_parent_agree; rewrite Hprf; reflexivity).
        rewrite Hag. rewrite Hprf. exact H.
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      assert (Hprf : forall q, proc_of gs' q = proc_of gs0 q)
        by (intro q; unfold proc_of; rewrite Hpr; reflexivity).
      assert (Hmsub : forall q, In q (es_msgs gs') -> In q (es_msgs gs0)).
      { intro q. unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. simpl. intro H. exact (remove_pkt_in _ _ _ H). }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_dst_not_idle pkt' (Hmsub pkt' Hpin) Hbp).
      * intros pkt' Hpin Hbp. intro Htin. exact (Hecho_token_sender_not pkt' (Hmsub pkt' Hpin) Hbp (Hmsub _ Htin)).
      * intros m c Hch. rewrite Hprf in Hch. intro Htin. exact (Hchildren_no_parent_token m c Hch (Hmsub _ Htin)).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_not_in_children pkt' (Hmsub pkt' Hpin) Hbp).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_src_in_fwds pkt' (Hmsub pkt' Hpin) Hbp).
      * intros m Hph. rewrite Hprf in Hph.
        assert (H := Hpending_count m Hph).
        assert (Hag : act_fwds gs' m = act_fwds gs0 m) by
          (apply act_fwds_parent_agree; rewrite Hprf; reflexivity).
        rewrite Hag. rewrite Hprf. exact H.

    (* ======================================== Echo / Active *)
    + destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0|] eqn:Hpar0.

        -- (* pending=1, parent=Some par0: Active; sends Echo(self→par0) *)
           set (np := mkProc Active (Some par0) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np)
                                            (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold np; rewrite Hpeq; reflexivity. }
           assert (Hself_ph_old : (proc_of gs0 self).(ps_phase) = Active)
             by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
           assert (Hself_par_old : (proc_of gs0 self).(ps_parent) = Some par0)
             by (unfold proc_of; rewrite <- Hpeq; exact Hpar0).
           assert (Hpend1 : (proc_of gs0 self).(ps_pending) >= 1).
           { unfold proc_of. rewrite <- Hpeq. apply Nat.eqb_eq in Hone. rewrite Hone.
             simpl. exact (Nat.le_refl _). }
           assert (Hpending_pos_self := Hpending_pos self par0 Hself_ph_old Hself_par_old Hpend1).
           assert (Hself_not_child_par0 : ~ In self (proc_of gs0 par0).(ps_children))
             by exact (proj2 Hpending_pos_self).
           assert (Hpar0_ne_idle : (proc_of gs0 par0).(ps_phase) <> Idle).
           { assert (Hself_in_all : In self all_nodes) by exact (proj2 (Hpkt_in_all_nodes pkt Hin)).
             destruct (Hparent_active self Hself_in_all par0 Hself_par_old) as [Ha|Hd].
             - rewrite Ha. discriminate.
             - rewrite Hd. discriminate. }
           assert (Hpar0_ne_self : par0 <> self).
           { intro Heq. subst par0.
             (* parent(self) = Some self contradicts no_self_parent (INV) *)
             exact (proj1 (proj2 (proj1 Hinv)) self Hself_par_old). }
           assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
           { intros q Hne. rewrite Hge, proc_of_upd.
             destruct (node_eq self q) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
             unfold proc_of. reflexivity. }
           assert (Hself_par_new : (proc_of gs' self).(ps_parent) = Some par0).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold np. simpl. reflexivity. }
           assert (Hself_ch_new : (proc_of gs' self).(ps_children) = sender :: ps_children p).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold np. simpl. reflexivity. }
           assert (Hself_pend_new : (proc_of gs' self).(ps_pending) = Nat.pred (ps_pending p)).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold np. simpl. reflexivity. }
           assert (Hself_ph_new : (proc_of gs' self).(ps_phase) = Active).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold np. simpl. reflexivity. }
           assert (Hmsgs_cla : forall q, In q (es_msgs gs') ->
               In q (es_msgs gs_mid) \/ q = mkPkt self par0 Echo).
           { intro q. rewrite Hge. simpl es_msgs. intro H.
             apply in_app_iff in H as [H|H]; [left; exact H|].
             destruct H as [<-|[]]; right; reflexivity. }
           assert (Hpkt_echo : pkt = mkPkt sender self Echo).
           { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
           assert (Hetsn_pkt : ~ In (mkPkt (ep_dst pkt) (ep_src pkt) Token) (es_msgs gs0))
             by exact (Hecho_token_sender_not pkt Hin Hbody).
           assert (Htsn_par0_self : ~ In (mkPkt par0 self Token) (es_msgs gs0))
             by exact (Htoken_from_parent self par0 Hself_par_old).
           refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
           ++ (* edni *)
              intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|Heq].
              ** apply remove_pkt_in in Ho. assert (H := Hecho_dst_not_idle pkt' Ho Hbp).
                 destruct (node_eq (ep_dst pkt') self) as [-> | Hne].
                 --- rewrite Hself_ph_new. discriminate.
                 --- rewrite (Hother _ Hne). exact H.
              ** subst pkt'. simpl.
                 destruct (node_eq par0 self) as [Heq|Hne].
                 --- rewrite Heq. rewrite Hself_ph_new. discriminate.
                 --- rewrite (Hother par0 Hpar0_ne_self). exact Hpar0_ne_idle.
           ++ (* etsn *)
              intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|Heq].
              ** apply remove_pkt_in in Ho. assert (H := Hecho_token_sender_not pkt' Ho Hbp).
                 intro Htin. apply Hmsgs_cla in Htin as [Hto|Heq].
                 --- exact (H (remove_pkt_in _ _ _ Hto)).
                 --- injection Heq; intros; discriminate.
              ** subst pkt'. simpl. intro Htin. apply Hmsgs_cla in Htin as [Hto|Heq].
                 --- apply remove_pkt_in in Hto. exact (Htsn_par0_self Hto).
                 --- injection Heq; intros; discriminate.
           ++ (* cipt *)
              intros m c Hch.
              destruct (node_eq m self) as [-> | Hne].
              ** rewrite Hself_ch_new in Hch. simpl in Hch. destruct Hch as [<-|Hrest].
                 --- (* c = sender: Token(self→sender) ∉ gs'.msgs.
                         Echo(sender→self)=pkt in bag → etsn: Token(self→sender)∉gs0.msgs.
                         gs'.msgs ⊆ gs0.msgs (via gs_mid) ++ [Echo(self→par0)]. No Token there. *)
                     intro Htin. apply Hmsgs_cla in Htin as [Hto|Heq].
                     +++ apply remove_pkt_in in Hto.
                         simpl in Hetsn_pkt. exact (Hetsn_pkt Hto).
                     +++ injection Heq; intros; discriminate.
                 --- intro Htin. apply Hmsgs_cla in Htin as [Hto|Heq].
                     +++ exact (Hchildren_no_parent_token self c Hrest (remove_pkt_in _ _ _ Hto)).
                     +++ injection Heq; intros; discriminate.
              ** rewrite (Hother m Hne) in Hch. assert (H := Hchildren_no_parent_token m c Hch).
                 intro Htin. apply Hmsgs_cla in Htin as [Hto|Heq].
                 --- exact (H (remove_pkt_in _ _ _ Hto)).
                 --- injection Heq as H1 H2 H3. exact (Hne H1).
           ++ (* enic *)
              intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|Heq].
              ** assert (Ho_orig := Ho). apply remove_pkt_in in Ho.
                 assert (H := Hecho_not_in_children pkt' Ho Hbp).
                 destruct (node_eq (ep_dst pkt') self) as [Hdst_eq | Hne].
                 --- (* dst=self *)
                     rewrite Hdst_eq. rewrite Hself_ch_new. intro Hch. simpl in Hch.
                     destruct Hch as [Heqs|Hrest].
                     +++ (* ep_src pkt' = sender. pkt' ∈ remove_pkt(pkt)(gs0). eamo contradiction. *)
                         assert (Hpkt'_eq : pkt' = mkPkt sender self Echo).
                         { destruct pkt' as [src dst body]. simpl in Heqs, Hdst_eq, Hbp |- *.
                           subst src dst body. reflexivity. }
                         rewrite Hpkt'_eq, <- Hpkt_echo in Ho_orig.
                         exact (echo_at_most_once_remove_not_in gs0 pkt Hecho_at_most_once Hbody Hin Ho_orig).
                     +++ rewrite Hdst_eq in H. exact (H Hrest).
                 --- rewrite (Hother _ Hne). exact H.
              ** (* pkt' = Echo(self→par0): self ∉ children(par0 in gs').
                     By ppa: self Active, parent=par0, pending≥1 → self∉children(par0). *)
                 subst pkt'. simpl. rewrite (Hother par0 Hpar0_ne_self).
                 exact Hself_not_child_par0.
           ++ (* esif *)
              intros pkt' Hpin Hbp. apply Hmsgs_cla in Hpin as [Ho|Heq].
              ** apply remove_pkt_in in Ho. assert (H := Hecho_src_in_fwds pkt' Ho Hbp).
                 destruct (node_eq (ep_dst pkt') self) as [Hdst_eq | Hne].
                 --- rewrite Hdst_eq. rewrite Hself_par_new. intro Heq2.
                     assert (Hcontra : (proc_of gs0 (ep_dst pkt')).(ps_parent) = Some (ep_src pkt')).
                     { rewrite Hdst_eq. exact (eq_trans Hself_par_old Heq2). }
                     exact (H Hcontra).
                 --- rewrite (Hother _ Hne). exact H.
              ** subst pkt'. simpl. rewrite (Hother par0 Hpar0_ne_self).
                 exact (Hno_mutual_parent self par0 Hself_par_old).
           ++ (* pec_ge: self: (pred 1 + S|ch|) = 0 + S|ch| ≥ |act_fwds|=|act_fwds_old| by IH with pending=1. *)
              intros m Hph.
              destruct (node_eq m self) as [-> | Hne].
              ** rewrite Hself_pend_new, Hself_ch_new. simpl length. rewrite Nat.add_succ_r.
                 assert (Hag : act_fwds gs' self = act_fwds gs0 self).
                 { apply act_fwds_parent_agree.
                   rewrite Hge, proc_of_upd.
                   destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
                   simpl. unfold np. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0). }
                 rewrite Hag.
                 assert (Hph_old : (proc_of gs0 self).(ps_phase) = Active \/
                                   (proc_of gs0 self).(ps_phase) = Decided) by (left; exact Hself_ph_old).
                 assert (H := Hpending_count self Hph_old).
                 unfold proc_of in H. rewrite <- Hpeq in H. simpl in H.
                 lia.
              ** rewrite (Hother m Hne) in Hph. assert (H := Hpending_count m Hph).
                 assert (Hag : act_fwds gs' m = act_fwds gs0 m).
                 { apply act_fwds_parent_agree. rewrite (Hother m Hne). reflexivity. }
                 rewrite Hag. rewrite (Hother m Hne). exact H.

        -- (* pending=1, parent=None: self decides *)
           set (dec := mkProc Decided None 0 (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self dec) (es_msgs gs_mid)).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold dec; rewrite Hpeq; reflexivity. }
           assert (Hself_ph_old : (proc_of gs0 self).(ps_phase) = Active)
             by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
           assert (Hself_par_old : (proc_of gs0 self).(ps_parent) = None)
             by (unfold proc_of; rewrite <- Hpeq; exact Hpar0).
           assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
           { intros q Hne. rewrite Hge, proc_of_upd.
             destruct (node_eq self q) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
             unfold proc_of. reflexivity. }
           assert (Hself_ch_new : (proc_of gs' self).(ps_children) = sender :: ps_children p).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold dec. simpl. reflexivity. }
           assert (Hself_ph_new : (proc_of gs' self).(ps_phase) = Decided).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold dec. simpl. reflexivity. }
           assert (Hself_par_new : (proc_of gs' self).(ps_parent) = None).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold dec. simpl. reflexivity. }
           assert (Hself_pend_new : (proc_of gs' self).(ps_pending) = 0).
           { rewrite Hge, proc_of_upd.
             destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
             simpl. unfold dec. simpl. reflexivity. }
           assert (Hpkt_echo : pkt = mkPkt sender self Echo).
           { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
           assert (Hetsn_pkt : ~ In (mkPkt (ep_dst pkt) (ep_src pkt) Token) (es_msgs gs0))
             by exact (Hecho_token_sender_not pkt Hin Hbody).
           assert (Hmsub : forall q, In q (es_msgs gs') -> In q (es_msgs gs0)).
           { intro q. rewrite Hge. simpl. intro H. exact (remove_pkt_in _ _ _ H). }
           refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
           ++ intros pkt' Hpin Hbp. apply Hmsub in Hpin. assert (H := Hecho_dst_not_idle pkt' Hpin Hbp).
              destruct (node_eq (ep_dst pkt') self) as [-> | Hne].
              ** rewrite Hself_ph_new. discriminate.
              ** rewrite (Hother _ Hne). exact H.
           ++ intros pkt' Hpin Hbp. assert (H := Hecho_token_sender_not pkt' (Hmsub pkt' Hpin) Hbp).
              intro Htin. exact (H (Hmsub _ Htin)).
           ++ intros m c Hch.
              destruct (node_eq m self) as [-> | Hne].
              ** rewrite Hself_ch_new in Hch. simpl in Hch. destruct Hch as [<-|Hrest].
                 --- intro Htin. apply Hmsub in Htin. simpl in Hetsn_pkt. exact (Hetsn_pkt Htin).
                 --- intro Htin. exact (Hchildren_no_parent_token self c Hrest (Hmsub _ Htin)).
              ** rewrite (Hother m Hne) in Hch. intro Htin. exact (Hchildren_no_parent_token m c Hch (Hmsub _ Htin)).
           ++ intros pkt' Hpin Hbp. assert (Hpin_orig := Hpin). apply Hmsub in Hpin.
              assert (H := Hecho_not_in_children pkt' Hpin Hbp).
              destruct (node_eq (ep_dst pkt') self) as [Hdst_eq2 | Hne].
              ** rewrite Hdst_eq2. rewrite Hself_ch_new. simpl.
                 intro Hin'. destruct Hin' as [Heqs2|Hrest].
                 --- assert (Hpkt'_eq : pkt' = mkPkt sender self Echo).
                     { destruct pkt' as [a b c]. simpl in Heqs2, Hdst_eq2, Hbp |- *.
                       subst a b c. reflexivity. }
                     rewrite Hge in Hpin_orig. simpl in Hpin_orig.
                     rewrite Hpkt'_eq, <- Hpkt_echo in Hpin_orig.
                     exact (echo_at_most_once_remove_not_in gs0 pkt Hecho_at_most_once Hbody Hin Hpin_orig).
                 --- rewrite Hdst_eq2 in H. exact (H Hrest).
              ** rewrite (Hother _ Hne). exact H.
           ++ intros pkt' Hpin Hbp. apply Hmsub in Hpin. assert (H := Hecho_src_in_fwds pkt' Hpin Hbp).
              destruct (node_eq (ep_dst pkt') self) as [-> | Hne].
              ** rewrite Hself_par_new. discriminate.
              ** rewrite (Hother _ Hne). exact H.
           ++ intros m Hph.
              destruct (node_eq m self) as [-> | Hne].
              ** rewrite Hself_pend_new, Hself_ch_new. simpl length.
                 assert (Hag : act_fwds gs' self = act_fwds gs0 self).
                 { apply act_fwds_parent_agree.
                   rewrite Hge, proc_of_upd.
                   destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
                   simpl. unfold dec. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0). }
                 rewrite Hag.
                 assert (Hph_old : (proc_of gs0 self).(ps_phase) = Active \/
                                   (proc_of gs0 self).(ps_phase) = Decided) by (left; exact Hself_ph_old).
                 assert (H := Hpending_count self Hph_old).
                 unfold proc_of in H. rewrite <- Hpeq in H. simpl in H.
                 simpl. apply Nat.eqb_eq in Hone.
                 rewrite Hone in H. simpl in H. exact H.
              ** rewrite (Hother m Hne) in Hph. assert (H := Hpending_count m Hph).
                 assert (Hag : act_fwds gs' m = act_fwds gs0 m).
                 { apply act_fwds_parent_agree. rewrite (Hother m Hne). reflexivity. }
                 rewrite Hag. rewrite (Hother m Hne). exact H.

      * (* pending ≠ 1: no new Echo *)
        set (np := mkProc Active (ps_parent p) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
        assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np) (es_msgs gs_mid)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
          rewrite Hbody, Hphase, Hone; unfold np; rewrite Hpeq; reflexivity. }
        assert (Hself_ph_old : (proc_of gs0 self).(ps_phase) = Active)
          by (unfold proc_of; rewrite Hpeq in Hphase; exact Hphase).
        assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
        { intros q Hne. rewrite Hge, proc_of_upd.
          destruct (node_eq self q) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
          unfold proc_of. reflexivity. }
        assert (Hself_ch_new : (proc_of gs' self).(ps_children) = sender :: ps_children p).
        { rewrite Hge, proc_of_upd.
          destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
          simpl. unfold np. simpl. reflexivity. }
        assert (Hself_ph_new : (proc_of gs' self).(ps_phase) = Active).
        { rewrite Hge, proc_of_upd.
          destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
          simpl. unfold np. simpl. reflexivity. }
        assert (Hself_par_new : (proc_of gs' self).(ps_parent) = ps_parent p).
        { rewrite Hge, proc_of_upd.
          destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
          simpl. unfold np. simpl. reflexivity. }
        assert (Hself_pend_new : (proc_of gs' self).(ps_pending) = Nat.pred (ps_pending p)).
        { rewrite Hge, proc_of_upd.
          destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
          simpl. unfold np. simpl. reflexivity. }
        assert (Hpkt_echo : pkt = mkPkt sender self Echo).
        { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
        assert (Hetsn_pkt : ~ In (mkPkt (ep_dst pkt) (ep_src pkt) Token) (es_msgs gs0))
          by exact (Hecho_token_sender_not pkt Hin Hbody).
        assert (Hmsub : forall q, In q (es_msgs gs') -> In q (es_msgs gs0)).
        { intro q. rewrite Hge. simpl. intro H. exact (remove_pkt_in _ _ _ H). }
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        ++ intros pkt' Hpin Hbp. apply Hmsub in Hpin. assert (H := Hecho_dst_not_idle pkt' Hpin Hbp).
           destruct (node_eq (ep_dst pkt') self) as [-> | Hne].
           ** rewrite Hself_ph_new. discriminate.
           ** rewrite (Hother _ Hne). exact H.
        ++ intros pkt' Hpin Hbp. assert (H := Hecho_token_sender_not pkt' (Hmsub pkt' Hpin) Hbp).
           intro Htin. exact (H (Hmsub _ Htin)).
        ++ intros m c Hch.
           destruct (node_eq m self) as [-> | Hne].
           ** rewrite Hself_ch_new in Hch. simpl in Hch. destruct Hch as [<-|Hrest].
              --- intro Htin. apply Hmsub in Htin. simpl in Hetsn_pkt. exact (Hetsn_pkt Htin).
              --- intro Htin. exact (Hchildren_no_parent_token self c Hrest (Hmsub _ Htin)).
           ** rewrite (Hother m Hne) in Hch. intro Htin. exact (Hchildren_no_parent_token m c Hch (Hmsub _ Htin)).
        ++ intros pkt' Hpin Hbp. assert (Hpin_orig := Hpin). apply Hmsub in Hpin.
           assert (H := Hecho_not_in_children pkt' Hpin Hbp).
           destruct (node_eq (ep_dst pkt') self) as [Hdst3 | Hne].
           ** rewrite Hdst3. rewrite Hself_ch_new. simpl. intro Hin'. destruct Hin' as [Heqs3|Hrest].
              --- assert (Hpkt'_eq : pkt' = mkPkt sender self Echo).
                  { destruct pkt' as [a b c]. simpl in Heqs3, Hdst3, Hbp |- *. subst a b c. reflexivity. }
                  rewrite Hge in Hpin_orig. simpl in Hpin_orig.
                  rewrite Hpkt'_eq, <- Hpkt_echo in Hpin_orig.
                  exact (echo_at_most_once_remove_not_in gs0 pkt Hecho_at_most_once Hbody Hin Hpin_orig).
              --- rewrite Hdst3 in H. exact (H Hrest).
           ** rewrite (Hother _ Hne). exact H.
        ++ intros pkt' Hpin Hbp. apply Hmsub in Hpin. assert (H := Hecho_src_in_fwds pkt' Hpin Hbp).
           destruct (node_eq (ep_dst pkt') self) as [Hdst3 | Hne].
           ** (* esif for self *)
              intro Heq. apply H. rewrite Hdst3.
              unfold proc_of. change (es_procs gs0 self) with p.
              rewrite Hdst3 in Heq.
              rewrite <- Hself_par_new. exact Heq.
           ** rewrite (Hother _ Hne). exact H.
        ++ intros m Hph.
           destruct (node_eq m self) as [-> | Hne].
           ** rewrite Hself_pend_new, Hself_ch_new. simpl length. rewrite Nat.add_succ_r.
              assert (Hag : act_fwds gs' self = act_fwds gs0 self).
              { apply act_fwds_parent_agree.
                rewrite Hge, proc_of_upd.
                destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
                simpl. unfold np. simpl. unfold proc_of. reflexivity. }
              rewrite Hag.
              assert (Hph_old : (proc_of gs0 self).(ps_phase) = Active \/
                                (proc_of gs0 self).(ps_phase) = Decided) by (left; exact Hself_ph_old).
              assert (H := Hpending_count self Hph_old).
              unfold proc_of in H. rewrite <- Hpeq in H. simpl in H. lia.
           ** rewrite (Hother m Hne) in Hph. assert (H := Hpending_count m Hph).
              assert (Hag : act_fwds gs' m = act_fwds gs0 m).
              { apply act_fwds_parent_agree. rewrite (Hother m Hne). reflexivity. }
              rewrite Hag. rewrite (Hother m Hne). exact H.

    (* ======================================== Echo / Decided *)
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      assert (Hprf : forall q, proc_of gs' q = proc_of gs0 q)
        by (intro q; unfold proc_of; rewrite Hpr; reflexivity).
      assert (Hmsub : forall q, In q (es_msgs gs') -> In q (es_msgs gs0)).
      { intro q. unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. simpl. intro H. exact (remove_pkt_in _ _ _ H). }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_dst_not_idle pkt' (Hmsub pkt' Hpin) Hbp).
      * intros pkt' Hpin Hbp. intro Htin. exact (Hecho_token_sender_not pkt' (Hmsub pkt' Hpin) Hbp (Hmsub _ Htin)).
      * intros m c Hch. rewrite Hprf in Hch. intro Htin. exact (Hchildren_no_parent_token m c Hch (Hmsub _ Htin)).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_not_in_children pkt' (Hmsub pkt' Hpin) Hbp).
      * intros pkt' Hpin Hbp. rewrite Hprf. exact (Hecho_src_in_fwds pkt' (Hmsub pkt' Hpin) Hbp).
      * intros m Hph. rewrite Hprf in Hph. assert (H := Hpending_count m Hph).
        assert (Hag : act_fwds gs' m = act_fwds gs0 m) by
          (apply act_fwds_parent_agree; rewrite Hprf; reflexivity).
        rewrite Hag. rewrite Hprf. exact H.
Qed.

(** The invariants are proved together as [token_echo_accounting] because their
    step-case proofs mutually depend on each other (e.g. [pending_exact_count_ge]
    needs [echo_src_in_fwds] and [echo_not_in_children] in the Echo/Active case).
    We use [invariant_by_induction] with a 19-component conjunction. *)
Definition token_echo_accounting (gs : EState) : Prop :=
  echo_dst_not_idle gs /\ echo_token_sender_not gs /\
  children_implies_no_parent_token gs /\ echo_not_in_children gs /\
  echo_src_in_fwds gs /\ pending_exact_count_ge gs /\
  pending_pos_active gs /\ token_at_most_once gs /\
  token_from_parent_consumed gs /\ parent_is_active gs /\
  idle_not_in_children gs /\ token_src_not_idle gs /\ echo_src_not_idle gs /\
  pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs /\
  token_dst_not_parent gs /\ no_mutual_parent_prop gs /\ INV gs /\
  echo_at_most_once gs.

Theorem token_echo_accounting_holds : is_invariant ELts token_echo_accounting.
Proof.
  apply invariant_by_induction.
  - intros gs Hi.
    unfold token_echo_accounting.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
    + intros p H _. rewrite (proj2 Hi) in H. contradiction.
    + intros p H _. rewrite (proj2 Hi) in H. contradiction.
    + intros m c H H'. rewrite (proj2 Hi) in H'. contradiction.
    + intros p H _. rewrite (proj2 Hi) in H. contradiction.
    + intros p H _. rewrite (proj2 Hi) in H. contradiction.
    + intros m [H|H]; unfold proc_of in H; rewrite (proj1 Hi m) in H; simpl in H; discriminate.
    + exact (pending_pos_active_base gs Hi).
    + exact (token_at_most_once_base gs Hi).
    + exact (token_from_parent_consumed_base gs Hi).
    + exact (parent_is_active_base gs Hi).
    + exact (idle_not_in_children_base gs Hi).
    + exact (token_src_not_idle_base gs Hi).
    + exact (echo_src_not_idle_base gs Hi).
    + exact (proj1 (pkt_nodes_in_all_nodes_base gs Hi)).
    + exact (proj2 (pkt_nodes_in_all_nodes_base gs Hi)).
    + intros p H _. rewrite (proj2 Hi) in H. contradiction.
    + intros m par H. unfold proc_of in H. rewrite (proj1 Hi) in H. simpl in H. discriminate.
    + exact (INV_init gs Hi).
    + intros p _. rewrite (proj2 Hi) in *. unfold count_pkt. simpl. exact (Nat.le_0_l _).
  - intros gs lbl gs'
      [Hecho_dst_not_idle [Hecho_token_sender_not [Hchildren_no_parent_token [Hecho_not_in_children [Hecho_src_in_fwds [Hpending_count
      [Hpending_pos [Htoken_at_most_once [Htoken_from_parent [Hparent_active [Hidle_not_in_children [Htoken_src_not_idle [Hecho_src_not_idle [Hpkt_in_all_nodes [Hparent_in_all_nodes
      [Htoken_dst_not_parent [Hno_mutual_parent [Hinv Hecho_at_most_once]]]]]]]]]]]]]]]]]] Hstep.
    unfold token_echo_accounting.
    destruct (token_echo_accounting_step gs lbl gs' Hecho_dst_not_idle Hecho_token_sender_not Hchildren_no_parent_token Hecho_not_in_children Hecho_src_in_fwds Hpending_count Hecho_at_most_once
              Hpending_pos Htoken_at_most_once Htoken_from_parent Hparent_active Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hpkt_in_all_nodes Hparent_in_all_nodes Htoken_dst_not_parent Hno_mutual_parent Hinv Hstep)
      as [Hecho_dst_not_idle' [Hecho_token_sender_not' [Hchildren_no_parent_token' [Hecho_not_in_children' [Hecho_src_in_fwds' Hpending_count']]]]].
    refine (conj Hecho_dst_not_idle' (conj Hecho_token_sender_not' (conj Hchildren_no_parent_token' (conj Hecho_not_in_children' (conj Hecho_src_in_fwds' (conj Hpending_count'
      (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
    + exact (pending_pos_active_step gs lbl gs' Hpending_pos Htoken_from_parent Hidle_not_in_children Hecho_src_not_idle
                      (proj1 (proj2 (proj2 Hinv))) (proj1 (proj1 Hinv)) Hstep).
    + exact (token_at_most_once_step gs lbl gs' Htoken_at_most_once Htoken_src_not_idle Hstep).
    + exact (token_from_parent_consumed_step gs lbl gs' Htoken_at_most_once Htoken_from_parent Hparent_active Hstep).
    + exact (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep).
    + exact (idle_not_in_children_step gs lbl gs' Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hstep).
    + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep).
    + exact (echo_src_not_idle_step gs lbl gs' Hecho_src_not_idle Hstep).
    + exact (proj1 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
    + exact (proj2 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
    + exact (token_dst_not_parent_step gs lbl gs' Htoken_dst_not_parent Htoken_src_not_idle Hstep).
    + exact (no_mutual_parent_step gs lbl gs' Hno_mutual_parent Hparent_active Hpkt_in_all_nodes (proj1 (proj2 (proj2 Hinv))) Hstep).
    + destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hpin Heq].
      * exact (INV_step_start gs0 Hinv Hph).
      * exact (INV_step_deliver gs0 pkt gs0' Hinv Hpin Heq).
    + exact (echo_at_most_once_step gs lbl gs' Hecho_at_most_once Hecho_src_not_idle Hecho_token_sender_not Hpending_pos Hstep).
Qed.

Theorem echo_dst_not_idle_holds : is_invariant ELts echo_dst_not_idle.
Proof. intros gs Hr. exact (proj1 (token_echo_accounting_holds gs Hr)). Qed.

Theorem echo_token_sender_not_holds : is_invariant ELts echo_token_sender_not.
Proof. intros gs Hr. exact (proj1 (proj2 (token_echo_accounting_holds gs Hr))). Qed.

Theorem children_implies_no_parent_token_holds : is_invariant ELts children_implies_no_parent_token.
Proof. intros gs Hr. exact (proj1 (proj2 (proj2 (token_echo_accounting_holds gs Hr)))). Qed.

Theorem echo_not_in_children_holds : is_invariant ELts echo_not_in_children.
Proof. intros gs Hr. exact (proj1 (proj2 (proj2 (proj2 (token_echo_accounting_holds gs Hr))))). Qed.

Theorem echo_src_in_fwds_holds : is_invariant ELts echo_src_in_fwds.
Proof. intros gs Hr. exact (proj1 (proj2 (proj2 (proj2 (proj2 (token_echo_accounting_holds gs Hr)))))). Qed.

Theorem pending_exact_count_ge_holds : is_invariant ELts pending_exact_count_ge.
Proof. intros gs Hr. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (token_echo_accounting_holds gs Hr))))))). Qed.

Theorem echo_at_most_once_holds : is_invariant ELts echo_at_most_once.
Proof.
  intros gs Hr. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (token_echo_accounting_holds gs Hr))))))))))))))))))).
Qed.

(* ================================================================== *)
(** *** Proof of weak_pending_ge_count_holds *)

(** Key algebraic lemma: given children ⊆ act_fwds (cif) and NoDup children (ndc),
    the filter of act_fwds for "in children" has the same length as children. *)
Lemma filter_nodup_subset_length (children act : list node) :
    NoDup children ->
    (forall c, In c children -> In c act) ->
    NoDup act ->
    length children = length (filter (fun n =>
      existsb (fun c => if node_eq c n then true else false) children) act).
Proof.
  intros Hndc Hcif Hndact.
  revert Hndc Hcif.
  induction children as [| hd tl IH].
  - intros _ _. simpl. rewrite filter_false. simpl. reflexivity.
  - intros Hndc Hcif.
    apply NoDup_cons_iff in Hndc as [Hhd_notin Hnd_tl].
    cbn [length].
    assert (Hhd_in_act : In hd act) by exact (Hcif hd (or_introl eq_refl)).
    assert (IH' := IH Hnd_tl (fun c Hc => Hcif c (or_intror Hc))).
    (* existsb extension: for n ≠ hd, (existsb ... (hd::tl)) = (existsb ... tl) *)
    assert (Hext : forall n, n <> hd ->
        existsb (fun c => if node_eq c n then true else false) (hd :: tl) =
        existsb (fun c => if node_eq c n then true else false) tl).
    { intros n Hne. simpl.
      destruct (node_eq hd n) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|reflexivity]. }
    assert (Hhd_true : existsb (fun c => if node_eq c hd then true else false) (hd :: tl) = true).
    { simpl. destruct (node_eq hd hd) as [_|Hc]; [reflexivity|exact (False_ind _ (Hc eq_refl))]. }
    assert (Hhd_tl_false : existsb (fun c => if node_eq c hd then true else false) tl = false).
    { apply not_true_is_false. intro H. apply existsb_exists in H as [c [Hc Heq]].
      destruct (node_eq c hd) as [-> | _]; [exact (Hhd_notin Hc) | discriminate]. }
    apply in_split in Hhd_in_act as [act1 [act2 Hact_split]].
    assert (Hhd_not_act1 : ~ In hd act1).
    { rewrite Hact_split in Hndact. apply NoDup_remove in Hndact as [_ H].
      intro Hin. apply H. apply in_or_app. left; exact Hin. }
    assert (Hhd_not_act2 : ~ In hd act2).
    { rewrite Hact_split in Hndact. apply NoDup_remove in Hndact as [_ H].
      intro Hin. apply H. apply in_or_app. right; exact Hin. }
    (* Relate filter over (hd::tl) and tl for each part *)
    assert (Hact1_ext : filter (fun n => existsb (fun c => if node_eq c n then true else false) (hd :: tl)) act1 =
                        filter (fun n => existsb (fun c => if node_eq c n then true else false) tl) act1).
    { apply filter_ext_in. intros n Hn. apply Hext. intro Heq. subst. exact (Hhd_not_act1 Hn). }
    assert (Hact2_ext : filter (fun n => existsb (fun c => if node_eq c n then true else false) (hd :: tl)) act2 =
                        filter (fun n => existsb (fun c => if node_eq c n then true else false) tl) act2).
    { apply filter_ext_in. intros n Hn. apply Hext. intro Heq. subst. exact (Hhd_not_act2 Hn). }
    (* Use IH': act already = act1 ++ hd :: act2 so rewrite Hact_split *)
    rewrite Hact_split in IH'.
    rewrite filter_app in IH'.
    (* Now IH' : length tl = length (filter tl act1 ++ filter tl (hd :: act2)) *)
    (* filter tl (hd :: act2): hd gives false since Hhd_tl_false *)
    assert (Hfilter_tl_hd : filter (fun n => existsb (fun c => if node_eq c n then true else false) tl) (hd :: act2) =
                             filter (fun n => existsb (fun c => if node_eq c n then true else false) tl) act2).
    { simpl. rewrite Hhd_tl_false. reflexivity. }
    rewrite Hfilter_tl_hd in IH'.
    (* Now IH' : length tl = length (filter tl act1 ++ filter tl act2) *)
    (* The goal: S (length tl) = length (filter (hd::tl) act) *)
    (* Rewrite act as act1 ++ hd :: act2 *)
    rewrite Hact_split.
    rewrite (filter_app (fun n => existsb (fun c => if node_eq c n then true else false) (hd :: tl)) act1 (hd :: act2)).
    (* goal: S (length tl) = length (filter (hd::tl) act1 ++ filter (hd::tl) (hd :: act2)) *)
    rewrite Hact1_ext.
    (* filter (hd::tl) (hd :: act2): hd gives true *)
    assert (Hfilter_hdtl_hd : filter (fun n => existsb (fun c => if node_eq c n then true else false) (hd :: tl)) (hd :: act2) =
                               hd :: filter (fun n => existsb (fun c => if node_eq c n then true else false) (hd :: tl)) act2).
    { cbn [filter]. rewrite Hhd_true. reflexivity. }
    rewrite Hfilter_hdtl_hd.
    rewrite Hact2_ext.
    (* goal: S (length tl) = length (filter tl act1 ++ hd :: filter tl act2) *)
    rewrite length_app. rewrite length_app in IH'.
    simpl length. simpl length in IH'.
    lia.
Qed.

(** nodup_children: NoDup (children(m)) for all m.
    Proof: children grows by 1 in Echo/Active. The new element (sender) ∉ old_children
    because Echo(sender→self) is in bag (enic says sender ∉ old_children). NoDup old by IH. *)
Definition nodup_children_inv (gs : EState) : Prop :=
  forall m, NoDup (proc_of gs m).(ps_children).

Lemma ndc_init : forall gs, lts_init ELts gs -> nodup_children_inv gs.
Proof.
  intros gs [Hproc _] m.
  unfold proc_of. rewrite Hproc. simpl. exact (NoDup_nil _).
Qed.

Lemma ndc_step gs lbl gs' :
    nodup_children_inv gs -> echo_not_in_children gs -> token_at_most_once gs ->
    lts_trans ELts gs lbl gs' -> nodup_children_inv gs'.
Proof.
  intros Hndc Hecho_not_in_children Htoken_at_most_once Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - (* step_start: init.children = [] *)
    set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_ch : (proc_of gs' initiator).(ps_children) = []).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intro m. destruct (node_eq m initiator) as [-> | Hne].
    + rewrite Hinit_ch. exact (NoDup_nil _).
    + rewrite (Hother m Hne). exact (Hndc m).
  - subst gs0'.
    set (self := ep_dst pkt). set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intro m.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    + (* Token/Idle: self.children = [] *)
      assert (Hself_ch : (proc_of gs' self).(ps_children) = []).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        destruct (Nat.eqb _ 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. destruct (Nat.eqb _ 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      destruct (node_eq m self) as [-> | Hne].
      * rewrite Hself_ch. exact (NoDup_nil _).
      * rewrite (Hother m Hne). exact (Hndc m).
    + (* Token/Active *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of. rewrite Hpr. exact (Hndc m).
    + (* Token/Decided *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of. rewrite Hpr. exact (Hndc m).
    + (* Echo/Idle *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of. rewrite Hpr. exact (Hndc m).
    + (* Echo/Active: sender added to children(self) *)
      destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0|] eqn:Hpar0.
        -- set (np := mkProc Active (Some par0) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np)
                                            (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold np; rewrite Hpeq; reflexivity. }
           destruct (node_eq m self) as [-> | Hne].
           ++ rewrite Hge, proc_of_upd.
              destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
              simpl. unfold np. simpl. constructor.
              ** (* sender ∉ ps_children p *)
                 intro Hch. exact (Hecho_not_in_children pkt Hin Hbody Hch).
              ** exact (Hndc self).
           ++ rewrite Hge, proc_of_upd.
              destruct (node_eq self m) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
              unfold proc_of. exact (Hndc m).
        -- set (dec := mkProc Decided None 0 (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self dec) (es_msgs gs_mid)).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold dec; rewrite Hpeq; reflexivity. }
           destruct (node_eq m self) as [-> | Hne].
           ++ rewrite Hge, proc_of_upd.
              destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
              simpl. unfold dec. simpl. constructor.
              ** intro Hch.
                 assert (Hpkt_eq : pkt = mkPkt sender self Echo).
                 { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
                 exact (Hecho_not_in_children pkt Hin Hbody Hch).
              ** exact (Hndc self).
           ++ rewrite Hge, proc_of_upd.
              destruct (node_eq self m) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
              unfold proc_of. exact (Hndc m).
      * set (np := mkProc Active (ps_parent p) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
        assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np) (es_msgs gs_mid)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
          rewrite Hbody, Hphase, Hone; unfold np; rewrite Hpeq; reflexivity. }
        destruct (node_eq m self) as [-> | Hne].
        ++ rewrite Hge, proc_of_upd.
           destruct (node_eq self self) as [_|Hc]; [|exact (False_ind _ (Hc eq_refl))].
           simpl. unfold np. simpl. constructor.
           ** intro Hch.
              assert (Hpkt_eq : pkt = mkPkt sender self Echo).
              { destruct pkt as [a b c]; simpl in *; rewrite Hbody; reflexivity. }
              exact (Hecho_not_in_children pkt Hin Hbody Hch).
           ** exact (Hndc self).
        ++ rewrite Hge, proc_of_upd.
           destruct (node_eq self m) as [Heq|_]; [exact (False_ind _ (Hne (eq_sym Heq)))|].
           unfold proc_of. exact (Hndc m).
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of. rewrite Hpr. exact (Hndc m).
Qed.

(** nodup_children_holds: *)
Theorem nodup_children_holds : is_invariant ELts nodup_children_inv.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => nodup_children_inv gs /\
               echo_dst_not_idle gs /\ echo_token_sender_not gs /\
               children_implies_no_parent_token gs /\ echo_not_in_children gs /\
               echo_src_in_fwds gs /\ pending_exact_count_ge gs /\
               pending_pos_active gs /\ token_at_most_once gs /\
               token_from_parent_consumed gs /\ parent_is_active gs /\
               idle_not_in_children gs /\ token_src_not_idle gs /\ echo_src_not_idle gs /\
               pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs /\
               token_dst_not_parent gs /\ no_mutual_parent_prop gs /\ INV gs /\
               echo_at_most_once gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      refine (conj (ndc_init gs Hi) _).
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
      all: first [
        exact (pending_pos_active_base gs Hi) | exact (token_at_most_once_base gs Hi) | exact (token_from_parent_consumed_base gs Hi) |
        exact (parent_is_active_base gs Hi) | exact (idle_not_in_children_base gs Hi) | exact (token_src_not_idle_base gs Hi) |
        exact (echo_src_not_idle_base gs Hi) | exact (INV_init gs Hi) | exact (echo_at_most_once_base gs Hi) |
        exact (no_mutual_parent_base gs Hi) | exact (token_dst_not_parent_base gs Hi) |
        exact (proj1 (pkt_nodes_in_all_nodes_base gs Hi)) | exact (proj2 (pkt_nodes_in_all_nodes_base gs Hi)) |
        (intros p H _; rewrite (proj2 Hi) in H; contradiction) |
        (intros m c H H'; rewrite (proj2 Hi) in H'; contradiction) |
        (intros m [H|H]; unfold proc_of in H; rewrite (proj1 Hi) in H; simpl in H; discriminate) |
        (intros m par H; unfold proc_of in H; rewrite (proj1 Hi) in H; simpl in H; discriminate)
      ].
    - intros gs lbl gs'
        [Hndc [Hecho_dst_not_idle [Hecho_token_sender_not [Hchildren_no_parent_token [Hecho_not_in_children [Hecho_src_in_fwds [Hpending_count
        [Hpending_pos [Htoken_at_most_once [Htoken_from_parent [Hparent_active [Hidle_not_in_children [Htoken_src_not_idle [Hecho_src_not_idle [Hpkt_in_all_nodes [Hparent_in_all_nodes
        [Htoken_dst_not_parent [Hno_mutual_parent [Hinv Hecho_at_most_once]]]]]]]]]]]]]]]]]]] Hstep.
      destruct (token_echo_accounting_step gs lbl gs' Hecho_dst_not_idle Hecho_token_sender_not Hchildren_no_parent_token Hecho_not_in_children Hecho_src_in_fwds Hpending_count Hecho_at_most_once
                Hpending_pos Htoken_at_most_once Htoken_from_parent Hparent_active Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hpkt_in_all_nodes Hparent_in_all_nodes Htoken_dst_not_parent Hno_mutual_parent Hinv Hstep)
        as [Hecho_dst_not_idle' [Hecho_token_sender_not' [Hchildren_no_parent_token' [Hecho_not_in_children' [Hecho_src_in_fwds' Hpending_count']]]]].
      refine (conj _ (conj Hecho_dst_not_idle' (conj Hecho_token_sender_not' (conj Hchildren_no_parent_token' (conj Hecho_not_in_children' (conj Hecho_src_in_fwds' (conj Hpending_count'
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))))).
      + exact (ndc_step gs lbl gs' Hndc Hecho_not_in_children Htoken_at_most_once Hstep).
      + exact (pending_pos_active_step gs lbl gs' Hpending_pos Htoken_from_parent Hidle_not_in_children Hecho_src_not_idle
                        (proj1 (proj2 (proj2 Hinv))) (proj1 (proj1 Hinv)) Hstep).
      + exact (token_at_most_once_step gs lbl gs' Htoken_at_most_once Htoken_src_not_idle Hstep).
      + exact (token_from_parent_consumed_step gs lbl gs' Htoken_at_most_once Htoken_from_parent Hparent_active Hstep).
      + exact (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep).
      + exact (idle_not_in_children_step gs lbl gs' Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hstep).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep).
      + exact (echo_src_not_idle_step gs lbl gs' Hecho_src_not_idle Hstep).
      + exact (proj1 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (proj2 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (token_dst_not_parent_step gs lbl gs' Htoken_dst_not_parent Htoken_src_not_idle Hstep).
      + exact (no_mutual_parent_step gs lbl gs' Hno_mutual_parent Hparent_active Hpkt_in_all_nodes (proj1 (proj2 (proj2 Hinv))) Hstep).
      + destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hin Heq].
        * exact (INV_step_start gs0 Hinv Hph).
        * exact (INV_step_deliver gs0 pkt gs0' Hinv Hin Heq).
      + exact (echo_at_most_once_step gs lbl gs' Hecho_at_most_once Hecho_src_not_idle Hecho_token_sender_not Hpending_pos Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(** weak_pending_ge_count_holds is proved after children_parent_ne_holds below. *)

(** The key lemma we need for children_in_fwds (cif): *)
(** children_in_all_nodes: c ∈ children(m) → c ∈ all_nodes *)
(** children_parent_ne: c ∈ children(m) → parent(m) ≠ Some c *)

(** From the big combined invariant, we have echo_src_in_fwds: Echo(src→dst) ∈ bag → parent(dst) ≠ Some src. *)
(** And children_are_neighbors: c ∈ children(m) → adj(m,c). *)
(** And pkt_nodes_in_all_nodes: ep_src pkt ∈ all_nodes when pkt ∈ bag. *)

(** For children_in_all_nodes, we need c ∈ all_nodes. This requires that c was the source of some Echo.
    But that Echo might not be in the bag anymore. So we need a separate invariant. *)

(** children_in_all_nodes_inv: c ∈ children(m) → c ∈ all_nodes *)
Definition children_in_all_nodes (gs : EState) : Prop :=
  forall m c, In c (proc_of gs m).(ps_children) -> In c all_nodes.

(** This invariant follows from pkt_nodes_in_all_nodes: when Echo(c→m) was delivered (adding c to children),
    c was ep_src of pkt, and pkt ∈ old_bag, so c ∈ all_nodes. Once c is in children, it stays in all_nodes
    since all_nodes doesn't change (it's a Variable). *)

Lemma cian_step gs lbl gs' :
    children_in_all_nodes gs ->
    pkt_nodes_in_all_nodes gs ->
    lts_trans ELts gs lbl gs' ->
    children_in_all_nodes gs'.
Proof.
  intros Hcian Hpkt_in_all_nodes Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - (* step_start: init.children=[], others unchanged *)
    set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_ch : (proc_of gs' initiator).(ps_children) = []).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m c Hch.
    destruct (node_eq m initiator) as [-> | Hne].
    + rewrite Hinit_ch in Hch. contradiction.
    + rewrite (Hother m Hne) in Hch. exact (Hcian m c Hch).
  - subst gs0'.
    set (self := ep_dst pkt). set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros m c Hch.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    + (* Token/Idle: self.children = [] *)
      assert (Hself_ch : (proc_of gs' self).(ps_children) = []).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        destruct (Nat.eqb _ 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. destruct (Nat.eqb _ 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      destruct (node_eq m self) as [-> | Hne].
      * rewrite Hself_ch in Hch. contradiction.
      * rewrite (Hother m Hne) in Hch. exact (Hcian m c Hch).
    + (* Token/Active *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch. rewrite Hpr in Hch. exact (Hcian m c Hch).
    + (* Token/Decided *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch. rewrite Hpr in Hch. exact (Hcian m c Hch).
    + (* Echo/Idle *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch. rewrite Hpr in Hch. exact (Hcian m c Hch).
    + (* Echo/Active: self.children grows by sender *)
      destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0|] eqn:Hpar0.
        -- set (np := mkProc Active (Some par0) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np)
                                            (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold np; rewrite Hpeq; reflexivity. }
           rewrite Hge, proc_of_upd in Hch.
           destruct (node_eq self m) as [<-|Hne].
           ++ simpl in Hch. unfold np in Hch. simpl in Hch.
              destruct Hch as [<- | Hrest].
              ** exact (proj1 (Hpkt_in_all_nodes pkt Hin)).
              ** exact (Hcian self c Hrest).
           ++ unfold proc_of in Hch. exact (Hcian m c Hch).
        -- set (dec := mkProc Decided None 0 (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self dec) (es_msgs gs_mid)).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold dec; rewrite Hpeq; reflexivity. }
           rewrite Hge, proc_of_upd in Hch.
           destruct (node_eq self m) as [<-|Hne].
           ++ simpl in Hch. unfold dec in Hch. simpl in Hch.
              destruct Hch as [<- | Hrest].
              ** exact (proj1 (Hpkt_in_all_nodes pkt Hin)).
              ** exact (Hcian self c Hrest).
           ++ unfold proc_of in Hch. exact (Hcian m c Hch).
      * set (np := mkProc Active (ps_parent p) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
        assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np) (es_msgs gs_mid)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
          rewrite Hbody, Hphase, Hone; unfold np; rewrite Hpeq; reflexivity. }
        rewrite Hge, proc_of_upd in Hch.
        destruct (node_eq self m) as [<-|Hne].
        ++ simpl in Hch. unfold np in Hch. simpl in Hch.
           destruct Hch as [<- | Hrest].
           ** exact (proj1 (Hpkt_in_all_nodes pkt Hin)).
           ** exact (Hcian self c Hrest).
        ++ unfold proc_of in Hch. exact (Hcian m c Hch).
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch. rewrite Hpr in Hch. exact (Hcian m c Hch).
Qed.

Theorem children_in_all_nodes_holds : is_invariant ELts children_in_all_nodes.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => children_in_all_nodes gs /\ pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs)).
  { apply invariant_by_induction.
    - intros gs Hi. refine (conj _ (conj (proj1 (pkt_nodes_in_all_nodes_base gs Hi)) (proj2 (pkt_nodes_in_all_nodes_base gs Hi)))).
      intros m c H. rewrite (proj1 Hi) in H. simpl in H. contradiction.
    - intros gs lbl gs' [Hcian [Hpkt_in_all_nodes Hparent_in_all_nodes]] Hstep.
      refine (conj _ (conj _ _)).
      + exact (cian_step gs lbl gs' Hcian Hpkt_in_all_nodes Hstep).
      + exact (proj1 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (proj2 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(** children_parent_ne: c ∈ children(m) → parent(m) ≠ Some c *)
(** This follows from echo_src_in_fwds combined with invariant induction:
    When Echo(c→m) is delivered (adding c to children), esif says parent(m) ≠ Some c.
    Parent doesn't change in Echo/Active. So parent(m in gs') ≠ Some c after the step.
    For older children: IH. *)
Definition children_parent_ne (gs : EState) : Prop :=
  forall m c, In c (proc_of gs m).(ps_children) ->
    (proc_of gs m).(ps_parent) <> Some c.

Lemma children_parent_ne_step gs lbl gs' :
    children_parent_ne gs -> echo_src_in_fwds gs ->
    lts_trans ELts gs lbl gs' -> children_parent_ne gs'.
Proof.
  intros Hcpne Hecho_src_in_fwds Hstep.
  destruct Hstep as [gs0 Hph0 | gs0 pkt gs0' Hin Heq].
  - (* step_start *)
    set (gs' := initiator_start node_eq initiator all_nodes adj gs0).
    assert (Hother : forall n, n <> initiator -> proc_of gs' n = proc_of gs0 n).
    { intros n Hne. unfold gs', proc_of, initiator_start. simpl.
      rewrite upd_other; [reflexivity | intro H; exact (Hne (eq_sym H))]. }
    assert (Hinit_ch : (proc_of gs' initiator).(ps_children) = []).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    assert (Hinit_par : (proc_of gs' initiator).(ps_parent) = None).
    { unfold gs', proc_of, initiator_start. simpl. rewrite upd_self. simpl. reflexivity. }
    intros m c Hch.
    destruct (node_eq m initiator) as [-> | Hne].
    + rewrite Hinit_ch in Hch. contradiction.
    + rewrite (Hother m Hne) in Hch. rewrite (Hother m Hne).
      exact (Hcpne m c Hch).
  - subst gs0'.
    set (self := ep_dst pkt). set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs' := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    intros m c Hch.
    destruct (ep_body pkt) eqn:Hbody; destruct (ps_phase p) eqn:Hphase.
    + (* Token/Idle: self.children=[] *)
      assert (Hself_ch : (proc_of gs' self).(ps_children) = []).
      { unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p. rewrite Hbody, Hphase.
        destruct (Nat.eqb _ 0); simpl es_procs; rewrite upd_self; simpl; reflexivity. }
      assert (Hother : forall q, q <> self -> proc_of gs' q = proc_of gs0 q).
      { intros q Hne. unfold gs', proc_of, handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. destruct (Nat.eqb _ 0);
        simpl es_procs; apply upd_other; intro H; exact (Hne (eq_sym H)). }
      destruct (node_eq m self) as [-> | Hne].
      * rewrite Hself_ch in Hch. contradiction.
      * rewrite (Hother m Hne) in Hch. rewrite (Hother m Hne). exact (Hcpne m c Hch).
    + (* Token/Active *)
      assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch |- *. rewrite Hpr in Hch |- *. exact (Hcpne m c Hch).
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch |- *. rewrite Hpr in Hch |- *. exact (Hcpne m c Hch).
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch |- *. rewrite Hpr in Hch |- *. exact (Hcpne m c Hch).
    + (* Echo/Active: sender added to children(self). parent(self) preserved (or changed to None). *)
      destruct (Nat.eqb (ps_pending p) 1) eqn:Hone.
      * destruct (ps_parent p) as [par0|] eqn:Hpar0.
        -- set (np := mkProc Active (Some par0) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np)
                                            (es_msgs gs_mid ++ [mkPkt self par0 Echo])).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold np; rewrite Hpeq; reflexivity. }
           rewrite Hge, proc_of_upd in Hch.
           rewrite Hge, proc_of_upd.
           destruct (node_eq self m) as [<-|Hne].
           ++ simpl in Hch |- *. unfold np in Hch |- *. simpl in Hch |- *.
              destruct Hch as [<- | Hrest].
              ** (* c = sender: parent(self in gs') = Some par0. Need par0 ≠ sender.
                     From esif: Echo(sender→self) ∈ gs0 → parent(self in gs0) ≠ Some sender.
                     parent(self in gs0) = Some par0 (Hpar0). So par0 ≠ sender. ✓ *)
                 intro Heq. injection Heq as Heq'.
                 (* Heq' : par0 = sender = ep_src pkt *)
                 (* Hecho_src_in_fwds says: ep_dst pkt = self, ep_src pkt = sender, so parent(self) ≠ Some sender *)
                 assert (H := Hecho_src_in_fwds pkt Hin Hbody).
                 (* H : (proc_of gs0 (ep_dst pkt)).(ps_parent) <> Some (ep_src pkt) *)
                 (* = parent(self).(gs0) <> Some sender *)
                 assert (Hpar_self : (proc_of gs0 self).(ps_parent) = Some (ep_src pkt)).
                 { unfold proc_of. rewrite <- Hpeq. rewrite Hpar0. f_equal. exact Heq'. }
                 unfold self in H. exact (H Hpar_self).
              ** intro Hc. apply (Hcpne self c Hrest). unfold proc_of. rewrite <- Hpeq. rewrite Hpar0. exact Hc.
           ++ unfold proc_of in Hch |- *. exact (Hcpne m c Hch).
        -- set (dec := mkProc Decided None 0 (sender :: ps_children p)).
           assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self dec) (es_msgs gs_mid)).
           { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
             rewrite Hbody, Hphase, Hone, Hpar0; unfold dec; rewrite Hpeq; reflexivity. }
           rewrite Hge, proc_of_upd in Hch.
           rewrite Hge, proc_of_upd.
           destruct (node_eq self m) as [<-|Hne].
           ++ simpl in Hch |- *. unfold dec in Hch |- *. simpl in Hch |- *.
              destruct Hch as [<- | Hrest].
              ** discriminate.
              ** intro Hc. apply (Hcpne self c Hrest). unfold proc_of. rewrite <- Hpeq. rewrite Hpar0. exact Hc.
           ++ unfold proc_of in Hch |- *. exact (Hcpne m c Hch).
      * set (np := mkProc Active (ps_parent p) (Nat.pred (ps_pending p)) (sender :: ps_children p)).
        assert (Hge : gs' = mkEchoState (update_proc node_eq (es_procs gs0) self np) (es_msgs gs_mid)).
        { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p;
          rewrite Hbody, Hphase, Hone; unfold np; rewrite Hpeq; reflexivity. }
        rewrite Hge, proc_of_upd in Hch.
        rewrite Hge, proc_of_upd.
        destruct (node_eq self m) as [<-|Hne].
        ++ simpl in Hch |- *. unfold np in Hch |- *. simpl in Hch |- *.
           destruct Hch as [<- | Hrest].
           ** (* c = sender: parent(self in gs') = ps_parent p. Need ps_parent p ≠ Some sender.
                  From esif: parent(self in gs0)=(proc_of gs0 self).(ps_parent)=ps_parent p ≠ Some sender. *)
              assert (H := Hecho_src_in_fwds pkt Hin Hbody). simpl in H.
              intro Heq. apply H.
              unfold proc_of. change (es_procs gs0 self) with p. exact Heq.
           ** exact (Hcpne self c Hrest).
        ++ unfold proc_of in Hch |- *. exact (Hcpne m c Hch).
    + assert (Hpr : es_procs gs' = es_procs gs0).
      { unfold gs'; unfold handle_msg; change (es_procs gs_mid self) with p; rewrite Hbody, Hphase; reflexivity. }
      unfold proc_of in Hch |- *. rewrite Hpr in Hch |- *. exact (Hcpne m c Hch).
Qed.

Theorem children_parent_ne_holds : is_invariant ELts children_parent_ne.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => children_parent_ne gs /\
               echo_dst_not_idle gs /\ echo_token_sender_not gs /\
               children_implies_no_parent_token gs /\ echo_not_in_children gs /\
               echo_src_in_fwds gs /\ pending_exact_count_ge gs /\
               pending_pos_active gs /\ token_at_most_once gs /\
               token_from_parent_consumed gs /\ parent_is_active gs /\
               idle_not_in_children gs /\ token_src_not_idle gs /\ echo_src_not_idle gs /\
               pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs /\
               token_dst_not_parent gs /\ no_mutual_parent_prop gs /\ INV gs /\
               echo_at_most_once gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      refine (conj _ _).
      + intros m c H. rewrite (proj1 Hi) in H. simpl in H. contradiction.
      + refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
        all: first [
          exact (pending_pos_active_base gs Hi) | exact (token_at_most_once_base gs Hi) | exact (token_from_parent_consumed_base gs Hi) |
          exact (parent_is_active_base gs Hi) | exact (idle_not_in_children_base gs Hi) | exact (token_src_not_idle_base gs Hi) |
          exact (echo_src_not_idle_base gs Hi) | exact (INV_init gs Hi) | exact (echo_at_most_once_base gs Hi) |
          exact (no_mutual_parent_base gs Hi) | exact (token_dst_not_parent_base gs Hi) |
          exact (proj1 (pkt_nodes_in_all_nodes_base gs Hi)) | exact (proj2 (pkt_nodes_in_all_nodes_base gs Hi)) |
          (intros p H _; rewrite (proj2 Hi) in H; contradiction) |
          (intros m c H H'; rewrite (proj2 Hi) in H'; contradiction) |
          (intros m [H|H]; unfold proc_of in H; rewrite (proj1 Hi) in H; simpl in H; discriminate) |
          (intros m par H; unfold proc_of in H; rewrite (proj1 Hi) in H; simpl in H; discriminate)
        ].
    - intros gs lbl gs'
        [Hcpne [Hecho_dst_not_idle [Hecho_token_sender_not [Hchildren_no_parent_token [Hecho_not_in_children [Hecho_src_in_fwds [Hpending_count
        [Hpending_pos [Htoken_at_most_once [Htoken_from_parent [Hparent_active [Hidle_not_in_children [Htoken_src_not_idle [Hecho_src_not_idle [Hpkt_in_all_nodes [Hparent_in_all_nodes
        [Htoken_dst_not_parent [Hno_mutual_parent [Hinv Hecho_at_most_once]]]]]]]]]]]]]]]]]]] Hstep.
      destruct (token_echo_accounting_step gs lbl gs' Hecho_dst_not_idle Hecho_token_sender_not Hchildren_no_parent_token Hecho_not_in_children Hecho_src_in_fwds Hpending_count Hecho_at_most_once
                Hpending_pos Htoken_at_most_once Htoken_from_parent Hparent_active Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hpkt_in_all_nodes Hparent_in_all_nodes Htoken_dst_not_parent Hno_mutual_parent Hinv Hstep)
        as [Hecho_dst_not_idle' [Hecho_token_sender_not' [Hchildren_no_parent_token' [Hecho_not_in_children' [Hecho_src_in_fwds' Hpending_count']]]]].
      refine (conj _ (conj Hecho_dst_not_idle' (conj Hecho_token_sender_not' (conj Hchildren_no_parent_token' (conj Hecho_not_in_children' (conj Hecho_src_in_fwds' (conj Hpending_count'
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))))).
      + exact (children_parent_ne_step gs lbl gs' Hcpne Hecho_src_in_fwds Hstep).
      + exact (pending_pos_active_step gs lbl gs' Hpending_pos Htoken_from_parent Hidle_not_in_children Hecho_src_not_idle
                        (proj1 (proj2 (proj2 Hinv))) (proj1 (proj1 Hinv)) Hstep).
      + exact (token_at_most_once_step gs lbl gs' Htoken_at_most_once Htoken_src_not_idle Hstep).
      + exact (token_from_parent_consumed_step gs lbl gs' Htoken_at_most_once Htoken_from_parent Hparent_active Hstep).
      + exact (parent_is_active_step gs lbl gs' Hparent_active Htoken_src_not_idle Hstep).
      + exact (idle_not_in_children_step gs lbl gs' Hidle_not_in_children Htoken_src_not_idle Hecho_src_not_idle Hstep).
      + exact (token_src_not_idle_step gs lbl gs' Htoken_src_not_idle Hstep).
      + exact (echo_src_not_idle_step gs lbl gs' Hecho_src_not_idle Hstep).
      + exact (proj1 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (proj2 (pkt_nodes_in_all_nodes_step gs lbl gs' Hpkt_in_all_nodes Hparent_in_all_nodes Hstep)).
      + exact (token_dst_not_parent_step gs lbl gs' Htoken_dst_not_parent Htoken_src_not_idle Hstep).
      + exact (no_mutual_parent_step gs lbl gs' Hno_mutual_parent Hparent_active Hpkt_in_all_nodes (proj1 (proj2 (proj2 Hinv))) Hstep).
      + destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hin Heq].
        * exact (INV_step_start gs0 Hinv Hph).
        * exact (INV_step_deliver gs0 pkt gs0' Hinv Hin Heq).
      + exact (echo_at_most_once_step gs lbl gs' Hecho_at_most_once Hecho_src_not_idle Hecho_token_sender_not Hpending_pos Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

Theorem weak_pending_ge_count_holds : is_invariant ELts weak_pending_ge_count.
Proof.
  intros gs Hr m Hph.
  set (children := (proc_of gs m).(ps_children)).
  set (act := act_fwds gs m).
  set (pending := (proc_of gs m).(ps_pending)).
  assert (Hpending_count := pending_exact_count_ge_holds gs Hr m Hph).
  fold children act pending in Hpending_count.
  assert (Hcif : forall c, In c children -> In c act).
  { intros c Hch. unfold act, children.
    apply act_fwds_spec. split; [| split].
    - exact (children_in_all_nodes_holds gs Hr m c Hch).
    - exact (proj1 (proj2 (INV_holds gs Hr)) m c Hch).
    - exact (children_parent_ne_holds gs Hr m c Hch). }
  assert (Hndc : NoDup children) by exact (nodup_children_holds gs Hr m).
  assert (Hndact : NoDup act) by exact (nodup_act_fwds gs m).
  unfold remaining_fwds. fold act children.
  assert (Hpart : forall (f : node -> bool) (l : list node),
      length (filter f l) + length (filter (fun x => negb (f x)) l) = length l).
  { intros f l. induction l as [|hd tl IH]; [simpl; reflexivity|].
    simpl. destruct (f hd); simpl; lia. }
  set (f := fun n => existsb (fun c => if node_eq c n then true else false) children).
  assert (Hpart_act := Hpart f act).
  assert (Hlen_eq : length children = length (filter f act))
    by exact (filter_nodup_subset_length children act Hndc Hcif Hndact).
  unfold f in *. lia.
Qed.

(* ================================================================== *)
(** *** pending_propagates and pending_chain_to_initiator

    Starting from any Active node m with pending >= 1, repeatedly apply
    [pending_propagates] along the parent chain.  The chain reaches the
    initiator in finitely many steps (by [active_non_init_has_chain]).
    Therefore pending(initiator) >= 1. *)

Lemma pending_propagates :
  forall gs, reachable ELts gs ->
    forall m par,
      In m all_nodes ->
      (proc_of gs m).(ps_phase) = Active ->
      (proc_of gs m).(ps_parent) = Some par ->
      (proc_of gs m).(ps_pending) >= 1 ->
      (proc_of gs par).(ps_pending) >= 1.
Proof.
  intros gs Hr m par Hm Hact Hpar Hpend.
  (* par ∈ all_nodes *)
  assert (Hpar_in : In par all_nodes)
    by exact (parent_in_all_nodes_holds gs Hr m par Hpar).
  (* par is Active or Decided *)
  assert (Hpar_phase : (proc_of gs par).(ps_phase) = Active \/
                       (proc_of gs par).(ps_phase) = Decided)
    by exact (parent_is_active_holds gs Hr m Hm par Hpar).
  (* m ∉ children(par): from pending_pos_active *)
  assert (Hm_not_child : ~ In m (proc_of gs par).(ps_children))
    by exact (proj2 (pending_pos_active_holds gs Hr m par Hact Hpar Hpend)).
  (* m ∈ act_fwds(par): from parent_is_neighbor (adj par m) + adj_sym + no_mutual_parent + m ∈ all_nodes *)
  assert (Hadj_m_par : adj m par = true)
    by exact (proj1 (proj1 (INV_holds gs Hr)) m par Hpar).
  assert (Hadj_par_m : adj par m = true) by exact (adj_sym m par Hadj_m_par).
  assert (Hno_mut : (proc_of gs par).(ps_parent) <> Some m)
    by exact (no_mutual_parent_holds gs Hr m par Hpar).
  assert (Hm_in_fwds : In m (act_fwds gs par)).
  { apply act_fwds_spec. exact (conj Hm (conj Hadj_par_m Hno_mut)). }
  (* remaining_fwds(par) ≥ 1: m ∈ act_fwds(par) and m ∉ children(par) *)
  assert (Hrem : remaining_fwds gs par >= 1)
    by exact (remaining_fwds_pos gs par m Hm_in_fwds Hm_not_child).
  (* pending(par) ≥ remaining_fwds(par) ≥ 1 *)
  apply Nat.le_trans with (m := remaining_fwds gs par); [exact Hrem |].
  exact (weak_pending_ge_count_holds gs Hr par Hpar_phase).
Qed.

Lemma pending_chain_to_initiator :
  forall gs, reachable ELts gs ->
    forall m,
      In m all_nodes ->
      (proc_of gs m).(ps_phase) = Active ->
      (proc_of gs m).(ps_pending) >= 1 ->
      (proc_of gs initiator).(ps_pending) >= 1.
Proof.
  intros gs Hr.
  (* Use well-founded induction on k from reaches_initiator. *)
  assert (Hchain : forall m k, In m all_nodes ->
      parent_path gs m k = Some initiator ->
      (proc_of gs m).(ps_phase) = Active ->
      (proc_of gs m).(ps_pending) >= 1 ->
      (proc_of gs initiator).(ps_pending) >= 1).
  { intros m k. revert m. induction k as [| k' IHk].
    - simpl. intros m _ Heq Hact Hpend. injection Heq as <-. exact Hpend.
    - simpl. intros m Hm Hpath Hact Hpend.
      destruct ((proc_of gs m).(ps_parent)) as [par|] eqn:Hpar; [| discriminate].
      assert (Hpend_par : (proc_of gs par).(ps_pending) >= 1)
        by exact (pending_propagates gs Hr m par Hm Hact Hpar Hpend).
      destruct (parent_is_active_holds gs Hr m Hm par Hpar) as [Hact_par | Hdec_par].
      + apply (IHk par).
        * exact (parent_in_all_nodes_holds gs Hr m par Hpar).
        * exact Hpath.
        * exact Hact_par.
        * exact Hpend_par.
      + exfalso.
        assert (Hz := decided_pending_zero_holds gs Hr par Hdec_par).
        rewrite Hz in Hpend_par. inversion Hpend_par. }
  intros m Hm Hact Hpend.
  destruct (node_eq m initiator) as [-> | Hne].
  - exact Hpend.
  - destruct (active_non_init_has_chain gs Hr m Hm Hact Hne) as [k Hk].
    exact (Hchain m k Hm Hk Hact Hpend).
Qed.

Theorem no_token_idle_decided :
  forall gs, reachable ELts gs -> initiator_decided gs ->
    forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Token ->
      (proc_of gs (ep_dst pkt)).(ps_phase) <> Idle.
Proof.
  intros gs Hr Hdec pkt Hpin Hbody Hidle.
  set (n := ep_dst pkt). set (m := ep_src pkt).
  (* m is not Idle *)
  assert (Hm_not_idle : (proc_of gs m).(ps_phase) <> Idle)
    by exact (token_src_not_idle_holds gs Hr pkt Hpin Hbody).
  (* n ∈ act_fwds(m) *)
  assert (Hadj : adj m n = true) by exact (valid_packets_holds gs Hr pkt Hpin).
  assert (Hpar_ne : (proc_of gs m).(ps_parent) <> Some n)
    by exact (token_dst_not_parent_holds gs Hr pkt Hpin Hbody).
  assert (Hn_in_all : In n all_nodes)
    by exact (proj2 (pkt_nodes_in_all_nodes_holds gs Hr pkt Hpin)).
  assert (Hm_in_all : In m all_nodes)
    by exact (proj1 (pkt_nodes_in_all_nodes_holds gs Hr pkt Hpin)).
  assert (Hn_in_fwds : In n (act_fwds gs m)).
  { apply act_fwds_spec. exact (conj Hn_in_all (conj Hadj Hpar_ne)). }
  (* n ∉ children(m): n is Idle *)
  assert (Hn_not_child : ~ In n (proc_of gs m).(ps_children))
    by exact (idle_not_in_children_holds gs Hr m n Hidle).
  (* remaining_fwds(m) ≥ 1 *)
  assert (Hrem : remaining_fwds gs m >= 1)
    by exact (remaining_fwds_pos gs m n Hn_in_fwds Hn_not_child).
  (* m is Active or Decided *)
  assert (Hm_phase : (proc_of gs m).(ps_phase) = Active \/
                     (proc_of gs m).(ps_phase) = Decided).
  { destruct (ps_phase (proc_of gs m)) eqn:Hph.
    - exact (False_ind _ (Hm_not_idle eq_refl)).
    - left; reflexivity.
    - right; reflexivity. }
  (* pending(m) ≥ 1 via weak_pending_ge_count *)
  assert (Hpend : (proc_of gs m).(ps_pending) >= 1).
  { apply Nat.le_trans with (m := remaining_fwds gs m); [exact Hrem |].
    exact (weak_pending_ge_count_holds gs Hr m Hm_phase). }
  (* pending(initiator) ≥ 1 *)
  assert (Hpend_init : (proc_of gs initiator).(ps_pending) >= 1).
  { destruct Hm_phase as [Hact | Hdecm].
    - exact (pending_chain_to_initiator gs Hr m Hm_in_all Hact Hpend).
    - (* m Decided → m = initiator *)
      assert (Hm_init : m = initiator).
      { destruct (node_eq m initiator) as [Heq | Hne]; [exact Heq |].
        exact (False_ind _ (non_init_not_decided_holds gs Hr m Hne Hdecm)). }
      rewrite <- Hm_init. exact Hpend. }
  (* decided_pending_zero: pending(initiator) = 0 *)
  assert (Hzero := decided_pending_zero_holds gs Hr initiator Hdec).
  rewrite Hzero in Hpend_init. inversion Hpend_init.
Qed.

(** BFS spanning tree rooted at [initiator].
    [wave_depth n] is the depth of n in the tree; every non-initiator has
    a neighbor of strictly smaller depth (graph connectivity). *)
Variable wave_depth : node -> nat.
Variable wave_depth_props :
  wave_depth initiator = 0 /\
  forall n, In n all_nodes -> n <> initiator ->
    exists m, In m all_nodes /\ adj n m = true /\ wave_depth m < wave_depth n.

Definition wave_depth_initiator : wave_depth initiator = 0 := proj1 wave_depth_props.
Definition wave_depth_nbr :
  forall n, In n all_nodes -> n <> initiator ->
    exists m, In m all_nodes /\ adj n m = true /\ wave_depth m < wave_depth n :=
  proj2 wave_depth_props.

(** The one-hop causal fact: proved from token_sent_or_notidle, parent_is_active,
    and no_token_idle_decided. *)
Theorem one_hop_active :
  forall gs, reachable ELts gs -> initiator_decided gs ->
    forall m n, In m all_nodes -> In n all_nodes ->
      adj m n = true ->
      wave_depth m < wave_depth n ->
      (proc_of gs m).(ps_phase) <> Idle ->
      (proc_of gs n).(ps_phase) = Active.
Proof.
  intros gs Hr Hdec m n Hm Hn Hadj Hwd Hm_not_idle.
  (* n ≠ initiator: wave_depth n > wave_depth m ≥ 0 = wave_depth initiator *)
  assert (Hne : n <> initiator).
  { intro Heq. subst. rewrite wave_depth_initiator in Hwd.
    exact (Nat.nlt_0_r _ Hwd). }
  (* n is not Decided *)
  assert (Hndec : (proc_of gs n).(ps_phase) <> Decided)
    by exact (non_init_not_decided_holds gs Hr n Hne).
  (* Case split on parent(m) = Some n vs ≠ Some n *)
  assert (Hpar_dec :
    (proc_of gs m).(ps_parent) = Some n \/
    (proc_of gs m).(ps_parent) <> Some n).
  { destruct ((proc_of gs m).(ps_parent)) as [par |] eqn:Hpv.
    - destruct (node_eq par n) as [Heq | Hpne].
      + subst par. left. reflexivity.
      + right. intro H. injection H as Heq. exact (Hpne Heq).
    - right. discriminate. }
  destruct Hpar_dec as [Heqpar | Hnepar'].
  - (* parent(m) = Some n: by parent_is_active, n is Active or Decided *)
    destruct (parent_is_active_holds gs Hr m Hm n Heqpar) as [Hact | Hdec2].
    + exact Hact.
    + exact (False_ind _ (Hndec Hdec2)).
  - (* parent(m) ≠ Some n: by token_sent_or_notidle, n not Idle OR Token(m,n) in bag *)
    destruct (token_sent_or_notidle_holds gs Hr m n Hm Hn Hadj Hm_not_idle Hnepar')
      as [Hn_not_idle | [pkt [Hpin [Hps [Hpd Hpb]]]]].
    + (* n not Idle: n is Active or Decided → n is Active *)
      destruct (ps_phase (proc_of gs n)) eqn:Hph.
      * exact (False_ind _ (Hn_not_idle eq_refl)).
      * reflexivity.
      * exact (False_ind _ (Hndec eq_refl)).
    + (* Token(m,n) in bag: by no_token_idle_decided, n not Idle *)
      assert (Hn_not_idle : (proc_of gs (ep_dst pkt)).(ps_phase) <> Idle).
      { exact (no_token_idle_decided gs Hr Hdec pkt Hpin Hpb). }
      rewrite Hpd in Hn_not_idle.
      destruct (ps_phase (proc_of gs n)) eqn:Hph.
      * exact (False_ind _ (Hn_not_idle eq_refl)).
      * reflexivity.
      * exact (False_ind _ (Hndec eq_refl)).
Qed.

(** decided_implies_all_active: proved by well-founded induction on wave_depth,
    using wf_inverse_image (Coq.Init.Wf) to lift lt_wf from nat to node.
    At each depth d, the inductive hypothesis gives that all non-initiator nodes
    at depth < d are Active; one_hop_active then handles the d → d+1 step. *)
Theorem decided_implies_all_active :
  forall gs, reachable ELts gs -> initiator_decided gs ->
    forall n, In n all_nodes -> n <> initiator ->
      (proc_of gs n).(ps_phase) = Active.
Proof.
  intros gs Hr Hdec.
  apply (well_founded_ind
           (wf_inverse_image node nat lt wave_depth lt_wf)
           (fun n => In n all_nodes -> n <> initiator ->
                     (proc_of gs n).(ps_phase) = Active)).
  intros n IH Hn Hne.
  (* n is not Decided *)
  assert (Hndec : (proc_of gs n).(ps_phase) <> Decided)
    by exact (non_init_not_decided_holds gs Hr n Hne).
  (* Get a neighbor m with strictly smaller wave depth *)
  destruct (wave_depth_nbr n Hn Hne) as [m [Hmin [Hadj Hlt]]].
  (* m is not Idle *)
  assert (Hm_not_idle : (proc_of gs m).(ps_phase) <> Idle).
  { destruct (node_eq m initiator) as [-> | Hmne].
    - (* initiator is Decided, not Idle *)
      intro Heq. unfold initiator_decided in Hdec.
      rewrite Heq in Hdec. discriminate.
    - (* m ≠ initiator: by IH (wave_depth m < wave_depth n), m is Active *)
      intro Heq. rewrite (IH m Hlt Hmin Hmne) in Heq. discriminate. }
  (* By one_hop_active: n is Active.
     wave_depth_nbr gives adj n m; adj_sym gives adj m n. *)
  exact (one_hop_active gs Hr Hdec m n Hmin Hn (adj_sym n m Hadj) Hlt Hm_not_idle).
Qed.

(** Main liveness theorem: when the initiator decides, the spanning tree
    is complete — every node in the network has a chain of ps_parent
    pointers leading back to the initiator.

    Proof outline:
    - n = initiator: trivial (depth-0 path).
    - n ≠ initiator: A4 says n is Active; A5 gives the parent chain. *)
Theorem decided_reaches_initiator :
  forall gs,
    reachable ELts gs ->
    initiator_decided gs ->
    forall n, In n all_nodes -> reaches_initiator gs n.
Proof.
  intros gs Hr Hdec n Hn.
  destruct (node_eq n initiator) as [-> | Hne].
  - (* n = initiator: parent_path at depth 0 is Some initiator *)
    exists 0. simpl. reflexivity.
  - (* n ≠ initiator: by A4 it is Active; by A5 it has a chain *)
    apply (active_non_init_has_chain gs Hr n Hn).
    + exact (decided_implies_all_active gs Hr Hdec n Hn Hne).
    + exact Hne.
Qed.

(* ================================================================== *)
(** ** 9. Termination measure *)

(** Termination measure: number of Idle nodes remaining.
    Every execution step either fires step_start (which decreases idle_count
    by 1, proved in start_decreases_idle) or delivers a packet (which either
    wakes an Idle node, also decreasing the count, or processes an already
    Active/Decided node, never increasing it).  So the execution must
    terminate in at most |all_nodes| steps for the wave to fully propagate. *)
Definition idle_count (gs : EState) : nat :=
  length (filter (fun n => match (proc_of gs n).(ps_phase) with
                           | Idle => true | _ => false end) all_nodes).

(** Helper: if in a NoDup list [x] satisfies [f x = true] but [f' x = false],
    and all other elements agree ([forall y, y <> x -> f' y = f y]),
    then [length (filter f' l) < length (filter f l)]. *)
(** Key list lemma: flipping one element from true to false strictly shrinks
    the filtered list.  NoDup ensures x appears exactly once so the length
    decreases by exactly 1 rather than possibly more.  The Nat.succ_lt_mono
    step requires proj1 (not apply) because succ_lt_mono is an iff. *)
Lemma filter_length_flip {A} (x : A) (f f' : A -> bool) :
    forall l : list A,
    NoDup l -> In x l ->
    f x = true -> f' x = false ->
    (forall y, y <> x -> f' y = f y) ->
    length (filter f' l) < length (filter f l).
Proof.
  induction l as [| hd tl IH]; intros Hnd Hin Hfx Hfx' Hoth.
  - contradiction.
  - inversion Hnd as [| ? ? Hnin Hnd_tl]; subst.
    simpl in Hin. destruct Hin as [<- | Htl].
    + (* hd = x: f' hd = false, f hd = true *)
      (* All elements of tl have f' = f *)
      assert (Heq : filter f' tl = filter f tl).
      { apply filter_ext_in. intros y Hy.
        apply Hoth. intro Heq. subst. exact (Hnin Hy). }
      (* Compute filter for hd explicitly *)
      assert (Hlhs : length (filter f' (hd :: tl)) = length (filter f tl)).
      { simpl filter. rewrite Hfx', Heq. reflexivity. }
      assert (Hrhs : length (filter f (hd :: tl)) = S (length (filter f tl))).
      { simpl filter. rewrite Hfx. reflexivity. }
      rewrite Hlhs, Hrhs. apply Nat.lt_succ_diag_r.
    + (* hd ≠ x, x ∈ tl *)
      assert (Hhd_ne : hd <> x).
      { intro Heq. subst. exact (Hnin Htl). }
      assert (k := IH Hnd_tl Htl Hfx Hfx' Hoth).
      (* Rewrite filter for hd in terms of f (using Hoth) *)
      assert (Hlhs : length (filter f' (hd :: tl)) =
                     if f hd then S (length (filter f' tl))
                             else length (filter f' tl)).
      { simpl filter. rewrite (Hoth hd Hhd_ne).
        destruct (f hd); reflexivity. }
      assert (Hrhs : length (filter f (hd :: tl)) =
                     if f hd then S (length (filter f tl))
                             else length (filter f tl)).
      { simpl filter. destruct (f hd); reflexivity. }
      rewrite Hlhs, Hrhs.
      destruct (f hd).
      * exact (proj1 (Nat.succ_lt_mono _ _) k).
      * exact k.
Qed.

(** step_start strictly decreases idle_count: the initiator leaves Idle,
    and no other node changes phase.  Uses filter_length_flip with x =
    initiator, f = Idle-indicator in old state, f' = same in new state.
    upd_self / proc_of_upd drive the update_proc reduction instead of
    rewrite upd_self, which fails when es_procs (mkEchoState ...) is not
    reduced by cbn. *)
Lemma start_decreases_idle gs :
    (proc_of gs initiator).(ps_phase) = Idle ->
    idle_count (initiator_start node_eq initiator all_nodes adj gs)
    < idle_count gs.
Proof.
  intro Hphase.
  unfold idle_count.
  apply (filter_length_flip initiator
    (fun n => match (proc_of gs n).(ps_phase) with Idle => true | _ => false end)
    (fun n => match (proc_of (initiator_start node_eq initiator all_nodes adj gs) n).(ps_phase)
              with Idle => true | _ => false end)).
  - exact nodup_nodes.
  - exact initiator_in_nodes.
  - (* f initiator = true *)
    rewrite Hphase. reflexivity.
  - (* f' initiator = false: after start, initiator is Active *)
    unfold initiator_start.
    rewrite proc_of_upd.
    destruct (node_eq initiator initiator) as [_ | Hc].
    + reflexivity.
    + exact (False_ind _ (Hc eq_refl)).
  - (* for all n ≠ initiator: f' n = f n *)
    intros n Hne.
    unfold initiator_start.
    rewrite proc_of_upd.
    destruct (node_eq initiator n) as [Heq | _].
    + exact (False_ind _ (Hne (eq_sym Heq))).
    + reflexivity.
Qed.

End EchoCorrectness.
