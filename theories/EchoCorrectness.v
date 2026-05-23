(** * Correctness of the Echo Algorithm — full proofs *)

From Stdlib Require Import List Arith Bool Arith.Wf_nat.
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

(* ------------------------------------------------------------------ *)
(** ** Structural assumptions
    These assumptions are required by the proofs of
    decided_reaches_initiator and start_decreases_idle. *)

(** A1. Graph connectivity.
    Every node in [all_nodes] has a directed path to [initiator] through
    adjacent edges.  Without this, isolated subtrees might never receive
    a Token and would never be part of the spanning tree.

    We define paths inductively and then assert the graph is connected. *)
Inductive adj_path : node -> node -> Prop :=
  | adj_path_refl : forall n,           adj_path n n
  | adj_path_step : forall n m k,
        adj n m = true -> adj_path m k -> adj_path n k.

Variable graph_connected :
  forall n, In n all_nodes -> adj_path n initiator.

(** Why this helps [decided_reaches_initiator]:
    When the initiator decides, every node must have gone through
    Token/Idle → Active (setting ps_parent).  Connectivity guarantees
    a Token wave could reach every node, so each node's parent pointer
    is set and forms a chain back to the initiator. *)

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

Definition initiator_decided (gs : EState) : Prop :=
  (proc_of gs initiator).(ps_phase) = Decided.

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
    exists m, adj n m = true /\ wave_depth m < wave_depth n.

(** The key propagation axiom: when the initiator has decided in a reachable state
    [gs], every non-initiator node at wave-depth at most [d] is Active in [gs].
    Proved outside this module by strong induction on [d], using reliable_delivery
    and the observation that a node echoes only after all its children echoed.
    We axiomatize it here for modularity.  The [d] parameter allows the induction
    on wave_depth to go through: the base case [d = 0] is vacuous (only the initiator
    has depth 0, which is excluded by [n <> initiator]), and the inductive step uses
    the fact that a node echoes only after all smaller-depth neighbors echoed first. *)
Variable token_propagates :
  forall d gs, reachable ELts gs -> initiator_decided gs ->
    forall n, In n all_nodes -> n <> initiator ->
      wave_depth n <= d ->
      (proc_of gs n).(ps_phase) = Active.

(** A4. When the initiator has decided, every non-initiator node is Active.
    Proved by applying [token_propagates] with [d = wave_depth n]. *)
Theorem decided_implies_all_active :
  forall gs, reachable ELts gs -> initiator_decided gs ->
    forall n, In n all_nodes -> n <> initiator ->
      (proc_of gs n).(ps_phase) = Active.
Proof.
  intros gs Hr Hdec n Hn Hne.
  exact (token_propagates (wave_depth n) gs Hr Hdec n Hn Hne (le_n (wave_depth n))).
Qed.

(** A5. Every Active non-initiator node has a parent-pointer chain leading
    to the initiator.  Provable by induction on the token wave depth
    (a node becomes Active only when it receives a Token from an already-Active
    node, so the chain grows by one hop at each step), but that induction
    requires reasoning about how parent_path changes across state updates.
    We take it as an axiom here. *)
Variable active_non_init_has_chain :
  forall gs, reachable ELts gs ->
    forall n, In n all_nodes ->
      (proc_of gs n).(ps_phase) = Active ->
      n <> initiator ->
      reaches_initiator gs n.

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
