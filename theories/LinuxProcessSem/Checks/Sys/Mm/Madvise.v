(** * LinuxProcessSem.Checks.Sys.Mm.Madvise — the madvise (233) checker, and its proofs

    Mirrors [Sys/Mm/Madvise.v], which answers to Linux [mm/madvise.c]:
    this file holds the checker for the syscall defined there, and no
    other.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checker here is executable, and its proofs relate it to the
    relational spec in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Fs.ReadWrite.

(** A NOHUGEPAGE result has no memory effect and one of the returns
    admitted by [madvise_nohuge_result]. *)
Definition check_madvise_nohuge_result (allow_eagain : bool)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if madvise_nohuge_ret_okb allow_eagain (eff_ret eff)
  then check_ret_only eff (eff_ret eff) m []
  else CheckReject.

Definition check_madvise_nohuge (addr len : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if w_is0 len then check_madvise_nohuge_result false eff m
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else if madvise_nohuge_ok (m_vmmaps m) addr
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
       then check_madvise_nohuge_result true eff m
       else CheckUnmodeled.

(** The DONTNEED arm requires the exact zero-fill and post-model. *)
Definition check_madvise (addr len advice : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if madvise_nohuge_b advice then check_madvise_nohuge addr len eff m
  else if negb (madvise_dontneed_b advice) then CheckUnmodeled
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if madvise_dontneed_ok (m_vmmaps m) addr n then
      match eff with
      | mkEffectU r [] zs [] [] [] =>
          if w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk (madvise_dontneed_next m addr n) []
          else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled.

Lemma check_madvise_nohuge_result_sound_ok :
  forall allow eff m m' evs i,
    check_madvise_nohuge_result allow eff m = CheckOk m' evs ->
    madvise_nohuge_result allow i m (Ok eff m' evs).
Proof.
  intros allow [r ws zs us cs copyins] m m' evs i H.
  unfold check_madvise_nohuge_result in H.
  cbn [eff_ret] in H.
  destruct (madvise_nohuge_ret_okb allow r) eqn:Hr; [|discriminate].
  apply check_ret_only_ok_iff in H.
  destruct H as [Heff [-> ->]]. inversion Heff; subst.
  unfold madvise_nohuge_result.
  eapply bind_ok0; [apply (choose_ok _ r); exact Hr|apply pure_ok].
Qed.

Lemma check_madvise_nohuge_result_complete_ok :
  forall allow eff m m' evs i,
    madvise_nohuge_result allow i m (Ok eff m' evs) ->
    check_madvise_nohuge_result allow eff m = CheckOk m' evs.
Proof.
  intros allow eff m m' evs i H.
  unfold madvise_nohuge_result in H.
  sys_unfold. inv_ok.
  unfold check_madvise_nohuge_result.
  cbn [eff_ret]. rewrite H.
  cbn [check_ret_only]. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma madvise_nohuge_result_not_unmodeled :
  forall allow i m, ~ madvise_nohuge_result allow i m Unmodeled.
Proof.
  intros allow i m H.
  unfold madvise_nohuge_result in H. sys_unfold. inv_ok.
Qed.

Lemma check_madvise_nohuge_result_not_unmodeled :
  forall allow eff m,
    check_madvise_nohuge_result allow eff m <> CheckUnmodeled.
Proof.
  intros allow eff m H.
  unfold check_madvise_nohuge_result in H.
  destruct (madvise_nohuge_ret_okb allow (eff_ret eff));
    [now apply check_ret_only_no_unmodeled in H|discriminate].
Qed.

Lemma check_madvise_nohuge_sound_ok :
  forall addr len eff m m' evs i,
    check_madvise_nohuge addr len eff m = CheckOk m' evs ->
    madvise_nohuge_spec addr len i m (Ok eff m' evs).
Proof.
  intros addr len eff m m' evs i H.
  unfold check_madvise_nohuge in H.
  unfold madvise_nohuge_spec.
  destruct (w_is0 len) eqn:Hlen;
    [eapply check_madvise_nohuge_result_sound_ok; exact H|].
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (madvise_nohuge_ok (m_vmmaps m) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok;
    [|discriminate].
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  rewrite Hok. eapply check_madvise_nohuge_result_sound_ok; exact H.
Qed.

Lemma check_madvise_nohuge_sound_unmodeled :
  forall addr len eff m i,
    check_madvise_nohuge addr len eff m = CheckUnmodeled ->
    madvise_nohuge_spec addr len i m Unmodeled.
Proof.
  intros addr len eff m i H.
  unfold check_madvise_nohuge in H.
  unfold madvise_nohuge_spec.
  destruct (w_is0 len) eqn:Hlen.
  { now apply check_madvise_nohuge_result_not_unmodeled in H. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (madvise_nohuge_ok (m_vmmaps m) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  { now apply check_madvise_nohuge_result_not_unmodeled in H. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
  rewrite Hok. apply unmodeled_intro.
Qed.

Lemma check_madvise_nohuge_complete_ok :
  forall addr len eff m m' evs i,
    madvise_nohuge_spec addr len i m (Ok eff m' evs) ->
    check_madvise_nohuge addr len eff m = CheckOk m' evs.
Proof.
  intros addr len eff m m' evs i H.
  unfold madvise_nohuge_spec in H.
  unfold check_madvise_nohuge.
  destruct (w_is0 len) eqn:Hlen;
    [eapply check_madvise_nohuge_result_complete_ok; exact H|].
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  cbv zeta.
  destruct (madvise_nohuge_ok (m_vmmaps m) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok. }
  eapply check_madvise_nohuge_result_complete_ok.
  apply (proj1 (bind_get_model _ _ _ _)) in H.
  cbv beta zeta in H. rewrite Hok in H. exact H.
Qed.

Lemma check_madvise_nohuge_complete_unmodeled :
  forall addr len eff m i,
    madvise_nohuge_spec addr len i m Unmodeled ->
    check_madvise_nohuge addr len eff m = CheckUnmodeled.
Proof.
  intros addr len eff m i H.
  unfold madvise_nohuge_spec in H.
  unfold check_madvise_nohuge.
  destruct (w_is0 len) eqn:Hlen.
  { exfalso. eapply madvise_nohuge_result_not_unmodeled; exact H. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  cbv zeta.
  destruct (madvise_nohuge_ok (m_vmmaps m) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: reflexivity.
  exfalso. apply (proj1 (bind_get_model _ _ _ _)) in H.
  cbv beta zeta in H. rewrite Hok in H.
  eapply madvise_nohuge_result_not_unmodeled; exact H.
Qed.

Lemma check_madvise_sound_ok : forall addr len advice eff m m' evs i,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  madvise_spec addr len advice i m (Ok eff m' evs).
Proof.
  intros addr len advice eff m m' evs i H.
  unfold check_madvise in H. unfold madvise_spec.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (madvise_nohuge_b advice) eqn:Hnohuge.
  { eapply check_madvise_nohuge_sound_ok; exact H. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv; [discriminate|].
  destruct (w_is0 len) eqn:Hlen.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  cbv zeta in H.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok;
    [|discriminate].
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct us as [|? ?];
      [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|];
    try discriminate.
  destruct (w_is0 r
            && listNN_eqb zs
                 [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
    eqn:HC; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in HC as [Hr Hzs].
  unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
  apply listNN_eqb_eq in Hzs; subst zs.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  rewrite Hok.
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_madvise_sound_unmodeled : forall addr len advice eff m i,
  check_madvise addr len advice eff m = CheckUnmodeled ->
  madvise_spec addr len advice i m Unmodeled.
Proof.
  intros addr len advice [r ws zs us cs copyins] m i H.
  unfold check_madvise in H. unfold madvise_spec.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (madvise_nohuge_b advice) eqn:Hnohuge.
  { eapply check_madvise_nohuge_sound_unmodeled; exact H. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv;
    [apply unmodeled_intro|].
  destruct (w_is0 len) eqn:Hlen.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv zeta in H.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  { exfalso. destruct ws;
      [destruct us; [destruct cs; [destruct copyins|]|]|]; try discriminate.
    destruct (w_is0 r
              && listNN_eqb zs
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
      discriminate. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  rewrite Hok. apply unmodeled_intro.
Qed.

Lemma check_madvise_complete_ok : forall addr len advice eff m m' evs i,
  madvise_spec addr len advice i m (Ok eff m' evs) ->
  check_madvise addr len advice eff m = CheckOk m' evs.
Proof.
  intros addr len advice eff m m' evs i H.
  unfold madvise_spec in H. unfold check_madvise.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (madvise_nohuge_b advice) eqn:Hnohuge.
  { eapply check_madvise_nohuge_complete_ok; exact H. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv.
  { unfold unmodeled in H. discriminate. }
  destruct (w_is0 len) eqn:Hlen.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  cbv zeta.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok. }
  sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok.
  cbv iota. unfold w_is0. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma check_madvise_complete_unmodeled : forall addr len advice m i eff,
  madvise_spec addr len advice i m Unmodeled ->
  check_madvise addr len advice eff m = CheckUnmodeled.
Proof.
  intros addr len advice m i eff H.
  unfold madvise_spec in H. unfold check_madvise.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (madvise_nohuge_b advice) eqn:Hnohuge.
  { eapply check_madvise_nohuge_complete_unmodeled; exact H. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv; [reflexivity|].
  destruct (w_is0 len) eqn:Hlen.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  cbv zeta.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: reflexivity.
  sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok.
Qed.
