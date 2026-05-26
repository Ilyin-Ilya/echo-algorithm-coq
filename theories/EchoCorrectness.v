(** * Correctness of the Echo Algorithm — full proofs *)

From Stdlib Require Import List Arith Bool Arith.Wf_nat Init.Wf Wellfounded.Inverse_Image.
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

(** A3. Reliable message delivery.
    Any packet that is in the bag of an reachable state will eventually
    be delivered: there exists a later reachable state from which the
    delivery step has been taken.  This is a fairness / scheduling axiom
    and is NOT derivable from the LTS structure alone.

    Formally: if [gs] is reachable and [pkt ∈ gs.(es_msgs)], then
    there exists a reachable [gs'] such that [step_deliver pkt] fires. *)
Let ELts   := echo_LTS node node_eq initiator all_nodes adj.
Let EState := @echo_state node.

Variable reliable_delivery :
  forall gs pkt,
    reachable ELts gs ->
    In pkt (es_msgs gs) ->
    exists gs_mid gs_after,
      reachable ELts gs_mid /\
      In pkt (es_msgs gs_mid) /\
      lts_trans ELts gs_mid (ELDeliver pkt) gs_after.

(** Why this helps [decided_reaches_initiator]:
    Without reliable delivery the Token wave might stall (a packet sits
    in the bag forever).  With it we can argue by induction on the
    spanning-tree depth that every node eventually goes Active and sets
    its parent, which is what decided_reaches_initiator needs. *)

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

Lemma anip_init : forall gs, lts_init ELts gs -> active_non_init_parent gs.
Proof.
  intros gs [Hproc Hmsgs] n Hne Hph.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma anip_step gs lbl gs' :
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
  - apply anip_init.
  - intros gs lbl gs' Hinv Hstep.
    exact (anip_step gs lbl gs' Hinv Hstep).
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

Lemma nind_init : forall gs, lts_init ELts gs -> non_init_not_decided gs.
Proof.
  intros gs [Hproc _] n _ Hph.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma nind_step gs lbl gs' :
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
    - intros gs Hi. split; [apply nind_init | apply anip_init]; exact Hi.
    - intros gs lbl gs' [Hnind Hanip] Hstep. split.
      + exact (nind_step gs lbl gs' Hnind Hanip Hstep).
      + exact (anip_step gs lbl gs' Hanip Hstep). }
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

Lemma tsni_init : forall gs, lts_init ELts gs -> token_src_not_idle gs.
Proof.
  intros gs [_ Hmsgs] pkt Hin _.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma tsni_step gs lbl gs' :
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    token_src_not_idle gs'.
Proof.
  intros Htsni Hstep.
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
        by exact (Htsni pkt' Hold Hbp).
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
        assert (H := Htsni q Hqin Hqb).
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
             by exact (Htsni pkt' Hold Hbp).
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
             by exact (Htsni pkt' Hold Hbp).
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
          by exact (Htsni pkt' Hold Hbp).
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
        by exact (Htsni pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.

    (* ===== Echo / Idle: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Htsni pkt' Hpin Hbp).
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
                by exact (Htsni pkt' Hold Hbp).
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
             by exact (Htsni pkt' Hpin Hbp).
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
          by exact (Htsni pkt' Hpin Hbp).
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
        by exact (Htsni pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.
Qed.

Theorem token_src_not_idle_holds : is_invariant ELts token_src_not_idle.
Proof.
  apply invariant_by_induction.
  - apply tsni_init.
  - intros gs lbl gs' Hinv Hstep.
    exact (tsni_step gs lbl gs' Hinv Hstep).
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

Lemma tsno_init : forall gs, lts_init ELts gs -> token_sent_or_notidle gs.
Proof.
  intros gs [Hproc _] m n Hm Hn Hadj Hph Hpar.
  exfalso. apply Hph.
  unfold proc_of. rewrite Hproc. simpl. reflexivity.
Qed.

Lemma tsno_step gs lbl gs' :
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
  - apply tsno_init.
  - intros gs lbl gs' Hinv Hstep.
    exact (tsno_step gs lbl gs' Hinv Hstep).
Qed.

(* ================================================================== *)
(** ** Invariant C: parent_is_active *)

(** If n is m's parent, then n is Active or Decided. *)
Definition parent_is_active (gs : EState) : Prop :=
  forall m, In m all_nodes ->
    forall n, (proc_of gs m).(ps_parent) = Some n ->
    (proc_of gs n).(ps_phase) = Active \/ (proc_of gs n).(ps_phase) = Decided.

Lemma pia_init : forall gs, lts_init ELts gs -> parent_is_active gs.
Proof.
  intros gs [Hproc _] m _ n Hpar.
  unfold proc_of in Hpar. rewrite Hproc in Hpar. simpl in Hpar. discriminate.
Qed.

Lemma pia_step gs lbl gs' :
    parent_is_active gs ->
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    parent_is_active gs'.
Proof.
  intros Hpia Htsni Hstep.
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
      destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
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
        { exact (Htsni pkt Hin Hbody). }
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
        destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
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
      destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.

    (* ===== Token / Decided: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hpar.
      destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.

    (* ===== Echo / Idle: procs unchanged ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hother : forall n0, proc_of gs' n0 = proc_of gs0 n0).
      { intro n0. unfold proc_of. rewrite Hgs'_procs. reflexivity. }
      rewrite (Hother m) in Hpar.
      destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
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
              destruct (Hpia self Hm par Hpar_gs0) as [Hact | Hdec].
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
              destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
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
              destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
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
           destruct (Hpia self Hm n Hpar) as [Hact | Hdec].
           ** left.
              destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. exact Hself_phase_gs'.
              --- rewrite (Hother n Hnen). exact Hact.
           ** destruct (node_eq n self) as [Heqn | Hnen].
              --- subst n. left. exact Hself_phase_gs'.
              --- right. rewrite (Hother n Hnen). exact Hdec.
        ++ rewrite (Hother m Hnem) in Hpar.
           destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
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
      destruct (Hpia m Hm n Hpar) as [Hact | Hdec].
      * left. rewrite (Hother n). exact Hact.
      * right. rewrite (Hother n). exact Hdec.
Qed.

Theorem parent_is_active_holds : is_invariant ELts parent_is_active.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => parent_is_active gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. split; [apply pia_init | apply tsni_init]; exact Hi.
    - intros gs lbl gs' [Hpia Htsni] Hstep. split.
      + exact (pia_step gs lbl gs' Hpia Htsni Hstep).
      + exact (tsni_step gs lbl gs' Htsni Hstep). }
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

Lemma pnpian_init : forall gs, lts_init ELts gs ->
    pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs.
Proof.
  intros gs [Hproc Hmsgs]. split.
  - intros pkt Hin. rewrite Hmsgs in Hin. contradiction.
  - intros n par Hpar. unfold proc_of in Hpar. rewrite Hproc in Hpar. simpl in Hpar. discriminate.
Qed.

(** Combined step: prove pkt_nodes_in_all_nodes and parent_in_all_nodes together
    so each can use the other. *)
Lemma pnpian_step gs lbl gs' :
    pkt_nodes_in_all_nodes gs ->
    parent_in_all_nodes gs ->
    lts_trans ELts gs lbl gs' ->
    pkt_nodes_in_all_nodes gs' /\ parent_in_all_nodes gs'.
Proof.
  intros Hpnian Hpian Hstep.
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
      * exact (Hpnian pkt' Hold).
      * apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
        rewrite Hsrc. split.
        -- exact initiator_in_nodes.
        -- exact (filter_subset _ all_nodes _ Hdst).
    + (* parent_in_all_nodes gs' *)
      intros n par Hpar.
      destruct (node_eq n initiator) as [-> | Hne].
      * rewrite Hinit_par in Hpar. discriminate.
      * rewrite (Hother n Hne) in Hpar. exact (Hpian n par Hpar).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    assert (Hsender_in : In sender all_nodes) by exact (proj1 (Hpnian pkt Hin)).
    assert (Hself_in   : In self   all_nodes) by exact (proj2 (Hpnian pkt Hin)).
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
           ++ exact (Hpnian pkt' (remove_pkt_in _ _ _ Hold)).
           ++ destruct Hnew as [<- | []]. simpl. exact (conj Hself_in Hsender_in).
        -- apply in_app_iff in Hpin' as [Hold | Hnew].
           ++ exact (Hpnian pkt' (remove_pkt_in _ _ _ Hold)).
           ++ apply send_to_all_inv in Hnew as [Hsrc [Hdst _]].
              rewrite Hsrc. split.
              ** exact Hself_in.
              ** exact (filter_subset _ all_nodes _ (filter_subset _ _ _ Hdst)).
      * (* parent_in_all_nodes gs' *)
        intros n par Hpar.
        destruct (node_eq n self) as [-> | Hne].
        -- rewrite Hself_par in Hpar. injection Hpar as <-. exact Hsender_in.
        -- rewrite (Hother n Hne) in Hpar. exact (Hpian n par Hpar).

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
        -- exact (Hpnian pkt' (remove_pkt_in _ _ _ Hold)).
        -- destruct Hnew as [<- | []]. simpl. exact (conj Hself_in Hsender_in).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hpian n par Hpar).

    (* ===== Token/Decided: procs unchanged, msgs shrink ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        exact (Hpnian pkt' (remove_pkt_in _ _ _ Hpin')).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hpian n par Hpar).

    (* ===== Echo/Idle: procs unchanged, msgs shrink ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        exact (Hpnian pkt' (remove_pkt_in _ _ _ Hpin')).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hpian n par Hpar).

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
           (* par0 ∈ all_nodes: from parent_in_all_nodes (Hpian) applied to (self, par0) *)
           assert (Hpar0_in : In par0 all_nodes).
           { apply (Hpian self par0). unfold proc_of. rewrite Hpeq in Hpar0. exact Hpar0. }
           assert (Hagree : forall n, (proc_of gs' n).(ps_parent) = (proc_of gs0 n).(ps_parent)).
           { intros n. rewrite Hgs'eq. rewrite proc_of_upd.
             destruct (node_eq self n) as [Heq | Hne].
             - subst n. simpl. unfold proc_of. rewrite <- Hpeq. exact (eq_sym Hpar0).
             - unfold proc_of. reflexivity. }
           split.
           ++ (* pkt_nodes_in_all_nodes gs' *)
              intros pkt' Hpin'. rewrite Hgs'eq in Hpin'. simpl in Hpin'.
              apply in_app_iff in Hpin' as [Hold | Hnew].
              ** exact (Hpnian pkt' (remove_pkt_in _ _ _ Hold)).
              ** destruct Hnew as [<- | []]. simpl. exact (conj Hself_in Hpar0_in).
           ++ (* parent_in_all_nodes gs' *)
              intros n par Hpar.
              rewrite (Hagree n) in Hpar. exact (Hpian n par Hpar).
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
              exact (Hpnian pkt' (remove_pkt_in _ _ _ Hpin')).
           ++ intros n par Hpar. rewrite (Hagree n) in Hpar. exact (Hpian n par Hpar).
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
           exact (Hpnian pkt' (remove_pkt_in _ _ _ Hpin')).
        -- intros n par Hpar. rewrite (Hagree n) in Hpar. exact (Hpian n par Hpar).

    (* ===== Echo/Decided: procs unchanged, msgs shrink ===== *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      split.
      * intros pkt' Hpin'. rewrite Hgs'_msgs in Hpin'.
        exact (Hpnian pkt' (remove_pkt_in _ _ _ Hpin')).
      * intros n par Hpar. unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hpian n par Hpar).
Qed.

Theorem pkt_nodes_in_all_nodes_holds : is_invariant ELts pkt_nodes_in_all_nodes.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs)).
  { apply invariant_by_induction.
    - intro gs. exact (pnpian_init gs).
    - intros gs lbl gs' [Hpnian Hpian] Hstep.
      exact (pnpian_step gs lbl gs' Hpnian Hpian Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

Theorem parent_in_all_nodes_holds : is_invariant ELts parent_in_all_nodes.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs)).
  { apply invariant_by_induction.
    - intro gs. exact (pnpian_init gs).
    - intros gs lbl gs' [Hpnian Hpian] Hstep.
      exact (pnpian_step gs lbl gs' Hpnian Hpian Hstep). }
  intros gs Hr. exact (proj2 (Hcomb gs Hr)).
Qed.

(* ================================================================== *)
(** ** no_mutual_parent: no two nodes are mutual parents *)

Definition no_mutual_parent_prop (gs : EState) : Prop :=
  forall m par,
    (proc_of gs m).(ps_parent) = Some par ->
    (proc_of gs par).(ps_parent) <> Some m.

Lemma nmp_init : forall gs, lts_init ELts gs -> no_mutual_parent_prop gs.
Proof.
  intros gs [Hproc _] m par Hpar.
  unfold proc_of in Hpar. rewrite Hproc in Hpar. simpl in Hpar. discriminate.
Qed.

Lemma nmp_step gs lbl gs' :
    no_mutual_parent_prop gs ->
    parent_is_active gs ->
    pkt_nodes_in_all_nodes gs ->
    valid_packets gs ->
    lts_trans ELts gs lbl gs' ->
    no_mutual_parent_prop gs'.
Proof.
  intros Hnmp Hpia Hpnian Hvpkt Hstep.
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
        exact (Hnmp m par Hpar Hcontra).

  (* ---- step_deliver ---- *)
  - subst gs0'.
    set (self   := ep_dst pkt).
    set (sender := ep_src pkt).
    set (gs_mid := mkEchoState gs0.(es_procs) (remove_pkt node_eq pkt gs0.(es_msgs))).
    set (gs'    := handle_msg node_eq all_nodes adj self gs_mid pkt).
    set (p      := gs_mid.(es_procs) self).
    assert (Hpeq : p = gs0.(es_procs) self) by reflexivity.
    assert (Hsender_in : In sender all_nodes) by exact (proj1 (Hpnian pkt Hin)).
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
        destruct (Hpia sender Hsender_in self Hcontra) as [Hact | Hdec].
        { unfold proc_of in Hact. rewrite <- Hpeq in Hact. rewrite Hphase in Hact. discriminate. }
        { unfold proc_of in Hdec. rewrite <- Hpeq in Hdec. rewrite Hphase in Hdec. discriminate. }
      * rewrite (Hother m Hnem) in Hpar.
        destruct (node_eq par self) as [Heqp | Hnep].
        { (* par = self: Hpar says parent(gs0 m) = Some self;
             Hcontra says parent(gs' self) = Some m;
             Hself_par says parent(gs' self) = Some sender;
             so sender = m; then Hpia m gives phase(gs0 self) Active/Decided,
             contradicting Hphase : phase(gs0 self) = Idle *)
          subst par. rewrite Hself_par in Hcontra. injection Hcontra as Hmend.
          (* Hmend : sender = m; rewrite in Hpar *)
          rewrite <- Hmend in Hpar.
          destruct (Hpia sender Hsender_in self Hpar) as [Hact | Hdec].
          - unfold proc_of in Hact. rewrite <- Hpeq in Hact. rewrite Hphase in Hact. discriminate.
          - unfold proc_of in Hdec. rewrite <- Hpeq in Hdec. rewrite Hphase in Hdec. discriminate. }
        { rewrite (Hother par Hnep) in Hcontra.
          exact (Hnmp m par Hpar Hcontra). }

    (* Token/Active, Token/Decided, Echo/Idle, Echo/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hnmp m par Hpar Hcontra).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hnmp m par Hpar Hcontra).
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hnmp m par Hpar Hcontra).

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
      exact (Hnmp m par Hpar Hcontra).

    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hnmp m par Hpar Hcontra).
Qed.

Theorem no_mutual_parent_holds : is_invariant ELts no_mutual_parent_prop.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => no_mutual_parent_prop gs /\ parent_is_active gs /\
               pkt_nodes_in_all_nodes gs /\ parent_in_all_nodes gs /\
               token_src_not_idle gs /\ INV gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      refine (conj (nmp_init gs Hi) (conj (pia_init gs Hi) (conj _ (conj _ (conj (tsni_init gs Hi) (INV_init gs Hi)))))).
      + exact (proj1 (pnpian_init gs Hi)).
      + exact (proj2 (pnpian_init gs Hi)).
    - intros gs lbl gs' [Hnmp [Hpia [Hpnian [Hpian [Htsni Hinv]]]]] Hstep.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      + exact (nmp_step gs lbl gs' Hnmp Hpia Hpnian (proj1 (proj2 (proj2 Hinv))) Hstep).
      + exact (pia_step gs lbl gs' Hpia Htsni Hstep).
      + exact (proj1 (pnpian_step gs lbl gs' Hpnian Hpian Hstep)).
      + exact (proj2 (pnpian_step gs lbl gs' Hpnian Hpian Hstep)).
      + exact (tsni_step gs lbl gs' Htsni Hstep).
      + destruct Hstep as [gs0 Hph | gs0 pkt gs0' Hin Heq].
        * exact (INV_step_start gs0 Hinv Hph).
        * exact (INV_step_deliver gs0 pkt gs0' Hinv Hin Heq). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(* ================================================================== *)
(** ** Invariants supporting no_token_idle_decided *)

(* ------------------------------------------------------------------ *)
(** *** echo_src_not_idle: Echo senders are never Idle. *)

Definition echo_src_not_idle (gs : EState) : Prop :=
  forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Echo ->
    (proc_of gs (ep_src pkt)).(ps_phase) <> Idle.

Lemma esni_init : forall gs, lts_init ELts gs -> echo_src_not_idle gs.
Proof.
  intros gs [_ Hmsgs] pkt Hin _.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma esni_step gs lbl gs' :
    echo_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    echo_src_not_idle gs'.
Proof.
  intros Hesni Hstep.
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
        by exact (Hesni pkt' Hold Hbp).
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
             by exact (Hesni pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq | Hne].
           ++ rewrite Heq in Hne_idle. unfold proc_of in Hne_idle.
              rewrite <- Hpeq in Hne_idle. exact (False_ind _ (Hne_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact Hne_idle.
        -- (* new Echo(self→sender): src=self, now Active *)
           destruct Hnew as [<- | []]. simpl ep_src. rewrite Hself_active. discriminate.
      * apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Hesni pkt' Hold Hbp).
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
          by exact (Hesni pkt' Hold Hbp).
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
        by exact (Hesni pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.

    (* Echo/Idle: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      assert (Hne_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
        by exact (Hesni pkt' Hpin Hbp).
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
                by exact (Hesni pkt' Hold Hbp).
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
             by exact (Hesni pkt' Hpin Hbp).
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
          by exact (Hesni pkt' Hpin Hbp).
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
        by exact (Hesni pkt' Hpin Hbp).
      unfold proc_of in *. rewrite Hgs'_procs. exact Hne_idle.
Qed.

Theorem echo_src_not_idle_holds : is_invariant ELts echo_src_not_idle.
Proof.
  apply invariant_by_induction.
  - apply esni_init.
  - intros gs lbl gs' Hinv Hstep.
    exact (esni_step gs lbl gs' Hinv Hstep).
Qed.

(* ------------------------------------------------------------------ *)
(** *** idle_not_in_children: Idle nodes never appear in any children list. *)

Definition idle_not_in_children (gs : EState) : Prop :=
  forall m n,
    (proc_of gs n).(ps_phase) = Idle ->
    ~ In n (proc_of gs m).(ps_children).

Lemma inic_init : forall gs, lts_init ELts gs -> idle_not_in_children gs.
Proof.
  intros gs [Hproc _] m n _ Hin.
  unfold proc_of in Hin. rewrite Hproc in Hin. simpl in Hin. contradiction.
Qed.

Lemma inic_step gs lbl gs' :
    idle_not_in_children gs ->
    token_src_not_idle gs ->
    echo_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    idle_not_in_children gs'.
Proof.
  intros Hinic Htsni Hesni Hstep.
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
        exact (Hinic m n Hn_idle Hin_child).

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
           exact (Hinic m n Hn_idle Hin_child).

    (* Token/Active: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinic m n Hn_idle Hin_child).

    (* Token/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinic m n Hn_idle Hin_child).

    (* Echo/Idle: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinic m n Hn_idle Hin_child).

    (* Echo/Active: sender added to children(self) *)
    + (* The key case: sender is the echo sender; sender was Active (non-Idle) *)
      assert (Hsender_not_idle : (proc_of gs0 sender).(ps_phase) <> Idle).
      { exact (Hesni pkt Hin Hbody). }
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
              ** exact (Hinic self n Hn_idle0 Hrest).
           ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
              destruct (node_eq self m) as [Heq | _].
              ** exact (False_ind _ (Hne (eq_sym Heq))).
              ** unfold proc_of in *. simpl in Hin_child.
                 exact (Hinic m n Hn_idle0 Hin_child).
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
              ** exact (Hinic self n Hn_idle0 Hrest).
           ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
              destruct (node_eq self m) as [Heq | _].
              ** exact (False_ind _ (Hne (eq_sym Heq))).
              ** unfold proc_of in *. simpl in Hin_child.
                 exact (Hinic m n Hn_idle0 Hin_child).
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
           ** exact (Hinic self n Hn_idle0 Hrest).
        ++ rewrite Hgs'eq in Hin_child. rewrite proc_of_upd in Hin_child.
           destruct (node_eq self m) as [Heq | _].
           ** exact (False_ind _ (Hne (eq_sym Heq))).
           ** unfold proc_of in *. simpl in Hin_child.
              exact (Hinic m n Hn_idle0 Hin_child).

    (* Echo/Decided: procs unchanged *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold proc_of in *. rewrite Hgs'_procs in *. exact (Hinic m n Hn_idle Hin_child).
Qed.

Theorem idle_not_in_children_holds : is_invariant ELts idle_not_in_children.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => idle_not_in_children gs /\ token_src_not_idle gs /\ echo_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. refine (conj (inic_init gs Hi) (conj _ _)).
      + apply tsni_init. exact Hi.
      + apply esni_init. exact Hi.
    - intros gs lbl gs' [Hinic [Htsni Hesni]] Hstep.
      refine (conj _ (conj _ _)).
      + exact (inic_step gs lbl gs' Hinic Htsni Hesni Hstep).
      + exact (tsni_step gs lbl gs' Htsni Hstep).
      + exact (esni_step gs lbl gs' Hesni Hstep). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Invariant: token_dst_not_parent
    The destination of a Token packet is not the source's parent. *)

Definition token_dst_not_parent (gs : EState) : Prop :=
  forall pkt,
    In pkt (es_msgs gs) -> ep_body pkt = Token ->
    (proc_of gs (ep_src pkt)).(ps_parent) <> Some (ep_dst pkt).

Lemma tdnp_init : forall gs, lts_init ELts gs -> token_dst_not_parent gs.
Proof.
  intros gs [_ Hmsgs] pkt Hin _.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma tdnp_step gs lbl gs' :
    token_dst_not_parent gs ->
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    token_dst_not_parent gs'.
Proof.
  intros Htdnp Htsni Hstep.
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
      assert (Hne_par := Htdnp pkt' Hold Hbp).
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
             by exact (Htsni pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq_src | Hne].
           ++ (* ep_src pkt' = self which was Idle → contradiction *)
              rewrite Heq_src in Hsrc_not_idle.
              unfold proc_of in Hsrc_not_idle. rewrite <- Hpeq in Hsrc_not_idle.
              exact (False_ind _ (Hsrc_not_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact (Htdnp pkt' Hold Hbp).
        -- destruct Hnew as [<- | []]. simpl in Hbp. discriminate.
      * (* internal: msgs = remove_pkt bag ++ send_to_all self fwds Token *)
        apply in_app_iff in Hpin as [Hold | Hnew].
        -- apply remove_pkt_in in Hold.
           assert (Hsrc_not_idle : (proc_of gs0 (ep_src pkt')).(ps_phase) <> Idle)
             by exact (Htsni pkt' Hold Hbp).
           destruct (node_eq (ep_src pkt') self) as [Heq_src | Hne].
           ++ (* ep_src pkt' = self which was Idle → contradiction *)
              rewrite Heq_src in Hsrc_not_idle.
              unfold proc_of in Hsrc_not_idle. rewrite <- Hpeq in Hsrc_not_idle.
              exact (False_ind _ (Hsrc_not_idle Hphase)).
           ++ rewrite (Hother _ Hne). exact (Htdnp pkt' Hold Hbp).
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
        exact (Htdnp pkt' (remove_pkt_in _ _ _ Hold) Hbp).
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
      exact (Htdnp pkt' Hold Hbp).

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
      exact (Htdnp pkt' Hold Hbp).

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
      exact (Htdnp pkt' (remove_pkt_in _ _ _ Htoken_in_mid) Hbp).

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
      exact (Htdnp pkt' Hold Hbp).
Qed.

Theorem token_dst_not_parent_holds : is_invariant ELts token_dst_not_parent.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => token_dst_not_parent gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. split; [apply tdnp_init | apply tsni_init]; exact Hi.
    - intros gs lbl gs' [Htdnp Htsni] Hstep. split.
      + exact (tdnp_step gs lbl gs' Htdnp Htsni Hstep).
      + exact (tsni_step gs lbl gs' Htsni Hstep). }
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

Lemma dpz_init : forall gs, lts_init ELts gs -> decided_pending_zero gs.
Proof.
  intros gs [Hproc _] n Hph.
  unfold proc_of in Hph. rewrite Hproc in Hph. simpl in Hph. discriminate.
Qed.

Lemma dpz_step gs lbl gs' :
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
  - apply dpz_init.
  - intros gs lbl gs' Hdpz Hstep.
    exact (dpz_step gs lbl gs' Hdpz Hstep).
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
  unfold count_pkt. rewrite filter_app. rewrite app_length. reflexivity.
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
Lemma tamo_remove_not_in (gs : EState) (pkt : @echo_packet node) :
    token_at_most_once gs ->
    ep_body pkt = Token ->
    In pkt (es_msgs gs) ->
    ~ In pkt (remove_pkt node_eq pkt (es_msgs gs)).
Proof.
  intros Htamo Hbody Hin Hin'.
  assert (H1 : count_pkt pkt (es_msgs gs) <= 1) by exact (Htamo pkt Hbody).
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

Lemma tamo_init : forall gs, lts_init ELts gs -> token_at_most_once gs.
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
Lemma tamo_count_idle_src gs pkt :
    token_src_not_idle gs ->
    ep_body pkt = Token ->
    (proc_of gs (ep_src pkt)).(ps_phase) = Idle ->
    count_pkt pkt (es_msgs gs) = 0.
Proof.
  intros Htsni Hbody Hidle.
  apply count_pkt_zero_if_no_match.
  intros q Hq.
  unfold pkt_matches.
  destruct (node_eq (ep_src pkt) (ep_src q)) as [Hsrc | _]; [| reflexivity].
  destruct (node_eq (ep_dst pkt) (ep_dst q)) as [_ | _]; [| reflexivity].
  destruct (ep_body pkt) eqn:Hbp; [| rewrite Hbody in Hbp; discriminate].
  destruct (ep_body q) eqn:Hbq; [| reflexivity].
  exfalso. apply (Htsni q Hq Hbq).
  rewrite <- Hsrc. exact Hidle.
Qed.

Lemma tamo_step gs lbl gs' :
    token_at_most_once gs ->
    token_src_not_idle gs ->
    lts_trans ELts gs lbl gs' ->
    token_at_most_once gs'.
Proof.
  intros Htamo Htsni Hstep.
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
      rewrite (tamo_count_idle_src gs0 pkt2 Htsni Hbody2 Hidle_src).
      simpl Nat.add.
      apply count_pkt_send_to_all_le_one.
      * exact Hsrc.
      * exact Hbody2.
      * apply NoDup_filter. exact nodup_nodes.
    + (* pkt2.src ≠ initiator: new tokens have src=init, old ≤ 1 *)
      rewrite (count_pkt_src_mismatch pkt2 initiator my_nbrs Token Hnsrc).
      rewrite Nat.add_0_r.
      exact (Htamo pkt2 Hbody2).

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
      assert (H2 : count_pkt pkt2 (es_msgs gs0) <= 1) by exact (Htamo pkt2 Hbody2).
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
           { apply tamo_count_idle_src; [exact Htsni | exact Hbody2 |].
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
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)]. }
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
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)].

    (* Echo/Idle: drop. *)
    + assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs.
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)].

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
             [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)]. }
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
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)].
      * assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
        { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
          rewrite Hbody, Hphase, Hone. rewrite Hpeq. reflexivity. }
        rewrite Hgs'_msgs.
        apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)].

    (* Echo/Decided: drop. *)
    + assert (Hgs'_msgs : es_msgs gs' = remove_pkt node_eq pkt (es_msgs gs0)).
      { unfold gs', handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      rewrite Hgs'_msgs.
      apply Nat.le_trans with (m := count_pkt pkt2 (es_msgs gs0));
        [exact (count_pkt_remove_le pkt2 pkt (es_msgs gs0)) | exact (Htamo pkt2 Hbody2)].
Qed.

Theorem token_at_most_once_holds : is_invariant ELts token_at_most_once.
Proof.
  assert (Hcomb : is_invariant ELts (fun gs => token_at_most_once gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi. exact (conj (tamo_init gs Hi) (tsni_init gs Hi)).
    - intros gs lbl gs' [Htamo Htsni] Hstep.
      exact (conj (tamo_step gs lbl gs' Htamo Htsni Hstep)
                  (tsni_step gs lbl gs' Htsni Hstep)). }
  intros gs Hr. exact (proj1 (Hcomb gs Hr)).
Qed.

(** (A) token_from_parent_consumed (tfpc): parent(n) = Some p → Token(p→n) ∉ bag. *)
Definition token_from_parent_consumed (gs : EState) : Prop :=
  forall n p, (proc_of gs n).(ps_parent) = Some p ->
    ~ In (mkPkt p n Token) (es_msgs gs).

Lemma tfpc_init : forall gs, lts_init ELts gs -> token_from_parent_consumed gs.
Proof.
  intros gs [_ Hmsgs] n p _ Hin.
  rewrite Hmsgs in Hin. contradiction.
Qed.

Lemma tfpc_step gs lbl gs' :
    token_at_most_once gs ->
    token_from_parent_consumed gs ->
    parent_is_active gs ->
    lts_trans ELts gs lbl gs' ->
    token_from_parent_consumed gs'.
Proof.
  intros Htamo Htfpc Hpia Hstep.
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
      * exact (Htfpc n p Hpar Hold).
      * apply send_to_all_inv in Hnew as [Hsrc [Hdst Hbody]].
        assert (Heq_src : p = initiator) by exact Hsrc.
        subst p.
        (* n ∈ all_nodes since it appears as dst in send_to_all, which uses nbrs ⊆ all_nodes *)
        assert (Hn_in : In n all_nodes).
        { simpl in Hdst. exact (filter_subset _ all_nodes n Hdst). }
        destruct (Hpia n Hn_in initiator Hpar) as [Hact | Hdec].
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
        assert (Htamo_not_in : ~ In pkt (remove_pkt node_eq pkt (es_msgs gs0)))
          by exact (tamo_remove_not_in gs0 pkt Htamo Hbody Hin).
        unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
        rewrite Hbody, Hphase in Hpin.
        set (len1 := length (filter (fun x => if node_eq x (ep_src pkt) then false else true)
                                    (nbrs all_nodes adj self))) in Hpin.
        destruct (Nat.eqb len1 0);
        simpl in Hpin; apply in_app_iff in Hpin as [Hold | Hnew].
        -- (* pkt ∈ remove_pkt old: contradicts tamo_not_in *)
           exfalso. apply Htamo_not_in.
           assert (Hpkt : {| ep_src := sender; ep_dst := self; ep_body := Token |} = pkt).
           { destruct pkt as [s d b]. simpl in *. subst. reflexivity. }
           rewrite Hpkt in Hold. exact Hold.
        -- destruct Hnew as [H0 | []]. simpl in *. discriminate.
        -- exfalso. apply Htamo_not_in.
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
        -- exact (Htfpc n par Hpar (remove_pkt_in _ _ _ Hold)).
        -- destruct Hnew as [Hpkt_eq | []]. injection Hpkt_eq as _ _ Hbody_eq. discriminate.
        -- exact (Htfpc n par Hpar (remove_pkt_in _ _ _ Hold)).
        -- apply send_to_all_inv in Hnew as [Hsrc [Hpd _]].
           simpl in Hsrc, Hpd.
           (* Hsrc : par = self; Hpar : proc_of gs0 n.parent = Some par. Rewrite to get Some self.
              n ∈ all_nodes since n ∈ fwds ⊆ nbrs adj self ⊆ all_nodes *)
           assert (Hn_in : In n all_nodes).
           { apply filter_subset in Hpd.
             unfold nbrs in Hpd. apply (filter_subset _ all_nodes n Hpd). }
           rewrite Hsrc in Hpar.
           destruct (Hpia n Hn_in self Hpar) as [Hact | Hdec].
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
        exact (Htfpc n par Hpar Hold).
      * destruct Hnew as [Hpkt_eq | []]. injection Hpkt_eq as _ _ Hbody_eq. discriminate.

    (* Token/Decided: procs unchanged, pkt dropped *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
      exact (Htfpc n par Hpar Hpin).

    (* Echo/Idle: procs unchanged, pkt dropped *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
      exact (Htfpc n par Hpar Hpin).

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
              exact (Htfpc n par0 Hpar_old Hpin_old).
           ++ unfold proc_of in Hpar. exact (Htfpc n par Hpar Hpin_old).
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
           ++ unfold proc_of in Hpar. exact (Htfpc n par Hpar Hpin_old).
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
           exact (Htfpc n par Hpar_old Hpin_old).
        ++ unfold proc_of in Hpar. exact (Htfpc n par Hpar Hpin_old).

    (* Echo/Decided: procs unchanged, pkt dropped *)
    + assert (Hgs'_procs : es_procs gs' = es_procs gs0).
      { unfold gs'. unfold handle_msg. change (es_procs gs_mid self) with p.
        rewrite Hbody, Hphase. reflexivity. }
      unfold gs', handle_msg in Hpin. change (es_procs gs_mid self) with p in Hpin.
      rewrite Hbody, Hphase in Hpin. simpl in Hpin.
      apply remove_pkt_in in Hpin.
      unfold proc_of in Hpar. rewrite Hgs'_procs in Hpar.
      exact (Htfpc n par Hpar Hpin).
Qed.

Theorem token_from_parent_consumed_holds : is_invariant ELts token_from_parent_consumed.
Proof.
  assert (Hcomb : is_invariant ELts
    (fun gs => token_at_most_once gs /\ token_from_parent_consumed gs /\
               parent_is_active gs /\ token_src_not_idle gs)).
  { apply invariant_by_induction.
    - intros gs Hi.
      exact (conj (tamo_init gs Hi)
             (conj (tfpc_init gs Hi)
             (conj (pia_init gs Hi) (tsni_init gs Hi)))).
    - intros gs lbl gs' [Htamo [Htfpc [Hpia Htsni]]] Hstep.
      exact (conj (tamo_step gs lbl gs' Htamo Htsni Hstep)
             (conj (tfpc_step gs lbl gs' Htamo Htfpc Hpia Hstep)
             (conj (pia_step gs lbl gs' Hpia Htsni Hstep)
                   (tsni_step gs lbl gs' Htsni Hstep)))). }
  intros gs Hr. exact (proj1 (proj2 (Hcomb gs Hr))).
Qed.

(** When the initiator decides, no Token in the bag targets an Idle node.
    Proof strategy: .claude/no_token_idle_decided_proof.md.
    Supporting invariants above (decided_pending_zero, token_at_most_once,
    token_from_parent_consumed) build toward this; pending-chain argument remains. *)
Variable no_token_idle_decided :
  forall gs, reachable ELts gs -> initiator_decided gs ->
    forall pkt, In pkt (es_msgs gs) -> ep_body pkt = Token ->
      (proc_of gs (ep_dst pkt)).(ps_phase) <> Idle.

(** Wave-depth axioms for the token propagation argument.
    [wave_depth n] is n's depth in the BFS spanning tree rooted at [initiator].
    These encode the fact that the token wave propagates strictly outward
    (depth strictly increases along forward Token edges) and that the
    initiator sits at depth 0. *)
Variable wave_depth : node -> nat.
Variable wave_depth_initiator : wave_depth initiator = 0.

(** Every non-initiator node in all_nodes has a neighbor of strictly smaller depth.
    This captures connectivity: you can always find a path toward the initiator. *)
Variable wave_depth_nbr :
  forall n, In n all_nodes -> n <> initiator ->
    exists m, In m all_nodes /\ adj n m = true /\ wave_depth m < wave_depth n.

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
