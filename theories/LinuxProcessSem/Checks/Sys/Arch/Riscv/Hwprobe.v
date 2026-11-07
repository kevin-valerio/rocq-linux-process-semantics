(** Executable checker for the two-key riscv_hwprobe call. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export Prelude.
Import ListNotations.
Open Scope bv_scope.

Definition check_hwprobe_response (pairs ext perf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU ret ws [] [] [] reads =>
      if (bv_eqb ret (Z_to_bv 64 0)
          && writes_eqb ws [(pairs, hwprobe_bytes ext perf)]
          && access_ranges_eqb reads (hwprobe_key_reads pairs))%bool
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Definition check_riscv_hwprobe (i : SyscallInput)
    (pairs pair_count cpusetsize cpus flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (w_is0 flags) then
    if hwprobe_which_cpus_ready_b flags cpusetsize cpus
    then CheckUnmodeled
    else check_ret_only eff (errno_ret EINVAL) m []
  else if negb (bv_eqb pair_count (Z_to_bv 64 2)) then CheckUnmodeled
  else if negb (w_is0 cpusetsize && w_is0 cpus)%bool then CheckUnmodeled
  else
  match m_hwprobe m with
  | None => CheckUnmodeled
  | Some (ext, perf) =>
      if negb (hwprobe_response_wf ext perf) then CheckUnmodeled
      else if negb (access_okb pairs 32) then CheckUnmodeled
      else
      match read_u64 (in_mem i) pairs,
            read_u64 (in_mem i) (pairs + Z_to_bv 64 16),
            read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32) with
      | Some k4, Some k5, Some _ =>
          if (bv_eqb k4 (Z_to_bv 64 4) &&
              bv_eqb k5 (Z_to_bv 64 5))%bool
          then check_hwprobe_response pairs ext perf eff m
          else CheckUnmodeled
      | _, _, _ => CheckUnmodeled
      end
  end.

Lemma check_hwprobe_response_ok : forall pairs ext perf eff m m' evs,
  check_hwprobe_response pairs ext perf eff m = CheckOk m' evs ->
  eff = with_copyins (hwprobe_key_reads pairs)
          (mkEffect (Z_to_bv 64 0) [(pairs, hwprobe_bytes ext perf)] [])
  /\ m' = m /\ evs = [].
Proof.
  intros pairs ext perf [ret ws zs us cs reads] m m' evs H.
  unfold check_hwprobe_response in H.
  destruct zs as [|z zs]; destruct us as [|u us];
    destruct cs as [|c cs]; try discriminate.
  destruct (bv_eqb ret (Z_to_bv 64 0)
            && writes_eqb ws [(pairs, hwprobe_bytes ext perf)]
            && access_ranges_eqb reads (hwprobe_key_reads pairs))%bool
    eqn:HG; [|discriminate].
  apply andb_true_iff in HG as [HG Hr].
  apply andb_true_iff in HG as [Hret Hw].
  apply bv_eqb_eq in Hret; subst ret.
  apply writes_eqb_eq in Hw; subst ws.
  apply access_ranges_eqb_eq in Hr; subst reads.
  inversion H; subst. now repeat split.
Qed.

Lemma check_hwprobe_response_refl : forall pairs ext perf m,
  check_hwprobe_response pairs ext perf
    (with_copyins (hwprobe_key_reads pairs)
       (mkEffect (Z_to_bv 64 0) [(pairs, hwprobe_bytes ext perf)] [])) m
  = CheckOk m [].
Proof.
  intros.
  change ((if (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)
              && writes_eqb [(pairs, hwprobe_bytes ext perf)]
                   [(pairs, hwprobe_bytes ext perf)]
              && access_ranges_eqb (hwprobe_key_reads pairs)
                   (hwprobe_key_reads pairs))%bool
          then CheckOk m [] else CheckReject) = CheckOk m []).
  rewrite bv_eqb_refl.
  rewrite (proj2 (writes_eqb_eq _ _) eq_refl).
  rewrite access_ranges_eqb_refl. reflexivity.
Qed.

Lemma check_hwprobe_response_no_unmodeled : forall pairs ext perf eff m,
  check_hwprobe_response pairs ext perf eff m <> CheckUnmodeled.
Proof.
  intros pairs ext perf [ret ws zs us cs reads] m.
  unfold check_hwprobe_response.
  destruct zs as [|z zs]; destruct us as [|u us];
    destruct cs as [|c cs]; try discriminate.
  destruct (bv_eqb ret (Z_to_bv 64 0)
            && writes_eqb ws [(pairs, hwprobe_bytes ext perf)]
            && access_ranges_eqb reads (hwprobe_key_reads pairs)); discriminate.
Qed.

Lemma check_riscv_hwprobe_sound_ok :
  forall i pairs count cpusetsize cpus flags eff m m' evs,
  check_riscv_hwprobe i pairs count cpusetsize cpus flags eff m =
    CheckOk m' evs ->
  riscv_hwprobe_spec pairs count cpusetsize cpus flags i m
    (Ok eff m' evs).
Proof.
  intros i pairs count cpusetsize cpus flags eff m m' evs H.
  unfold check_riscv_hwprobe in H.
  unfold riscv_hwprobe_spec.
  destruct (negb (w_is0 flags)) eqn:Hflags.
  { destruct (hwprobe_which_cpus_ready_b flags cpusetsize cpus);
      [discriminate|].
    apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  cbv iota in H |- *.
  destruct (negb (bv_eqb count (Z_to_bv 64 2))) eqn:Hcount;
    [discriminate|].
  cbv iota in H |- *.
  destruct (negb (w_is0 cpusetsize && w_is0 cpus)%bool) eqn:Hcpus;
    [discriminate|].
  cbv iota in H |- *.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (m_hwprobe m) as [[ext perf]|] eqn:Hhw; [|discriminate].
  destruct (negb (hwprobe_response_wf ext perf)) eqn:Hwf;
    [discriminate|].
  destruct (negb (access_okb pairs 32)) eqn:Haccess;
    [discriminate|].
  destruct (read_u64 (in_mem i) pairs) as [k4|] eqn:Hk4;
    [|discriminate].
  destruct (read_u64 (in_mem i) (pairs + Z_to_bv 64 16))
    as [k5|] eqn:Hk5; [|discriminate].
  destruct (read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32))
    as [buf|] eqn:Hw; [|discriminate].
  destruct (bv_eqb k4 (Z_to_bv 64 4) &&
            bv_eqb k5 (Z_to_bv 64 5))%bool eqn:Hkeys;
    [|discriminate].
  apply check_hwprobe_response_ok in H as (-> & -> & ->).
  apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
Qed.

Lemma check_riscv_hwprobe_sound_unmodeled :
  forall i pairs count cpusetsize cpus flags eff m,
  check_riscv_hwprobe i pairs count cpusetsize cpus flags eff m =
    CheckUnmodeled ->
  riscv_hwprobe_spec pairs count cpusetsize cpus flags i m Unmodeled.
Proof.
  intros i pairs count cpusetsize cpus flags eff m H.
  unfold check_riscv_hwprobe in H.
  unfold riscv_hwprobe_spec.
  destruct (negb (w_is0 flags)) eqn:Hflags.
  { destruct (hwprobe_which_cpus_ready_b flags cpusetsize cpus).
    - apply unmodeled_intro.
    - now apply check_ret_only_no_unmodeled in H. }
  cbv iota in H |- *.
  destruct (negb (bv_eqb count (Z_to_bv 64 2))) eqn:Hcount.
  { apply unmodeled_intro. }
  cbv iota in H |- *.
  destruct (negb (w_is0 cpusetsize && w_is0 cpus)%bool) eqn:Hcpus.
  { apply unmodeled_intro. }
  cbv iota in H |- *.
  eapply bind_unmodeled2; [apply input_ok|].
  eapply bind_unmodeled2; [apply get_model_ok|].
  destruct (m_hwprobe m) as [[ext perf]|] eqn:Hhw;
    [|apply unmodeled_intro].
  destruct (negb (hwprobe_response_wf ext perf)) eqn:Hwf;
    [apply unmodeled_intro|].
  destruct (negb (access_okb pairs 32)) eqn:Haccess;
    [apply unmodeled_intro|].
  destruct (read_u64 (in_mem i) pairs) as [k4|] eqn:Hk4;
    [|apply unmodeled_intro].
  destruct (read_u64 (in_mem i) (pairs + Z_to_bv 64 16))
    as [k5|] eqn:Hk5; [|apply unmodeled_intro].
  destruct (read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32))
    as [buf|] eqn:Hw; [|apply unmodeled_intro].
  destruct (bv_eqb k4 (Z_to_bv 64 4) &&
            bv_eqb k5 (Z_to_bv 64 5))%bool eqn:Hkeys.
  - now apply check_hwprobe_response_no_unmodeled in H.
  - apply unmodeled_intro.
Qed.

Lemma check_riscv_hwprobe_complete_ok :
  forall i pairs count cpusetsize cpus flags eff m m' evs,
  riscv_hwprobe_spec pairs count cpusetsize cpus flags i m
    (Ok eff m' evs) ->
  check_riscv_hwprobe i pairs count cpusetsize cpus flags eff m =
    CheckOk m' evs.
Proof.
  intros i pairs count cpusetsize cpus flags eff m m' evs H.
  unfold riscv_hwprobe_spec in H.
  unfold check_riscv_hwprobe.
  destruct (negb (w_is0 flags)) eqn:Hflags.
  { destruct (hwprobe_which_cpus_ready_b flags cpusetsize cpus);
      [inversion H|].
    unfold err_ret, ret_only in H. inversion H; subst.
    now apply check_ret_only_ok_iff. }
  cbv iota in H |- *.
  destruct (negb (bv_eqb count (Z_to_bv 64 2))) eqn:Hcount;
    [inversion H|].
  cbv iota in H |- *.
  destruct (negb (w_is0 cpusetsize && w_is0 cpus)%bool) eqn:Hcpus;
    [inversion H|].
  cbv iota in H |- *.
  apply bind_input_model_inv in H.
  destruct (m_hwprobe m) as [[ext perf]|] eqn:Hhw;
    [|inversion H].
  destruct (negb (hwprobe_response_wf ext perf)) eqn:Hwf;
    [inversion H|].
  destruct (negb (access_okb pairs 32)) eqn:Haccess;
    [inversion H|].
  destruct (read_u64 (in_mem i) pairs) as [k4|] eqn:Hk4;
    [|inversion H].
  destruct (read_u64 (in_mem i) (pairs + Z_to_bv 64 16))
    as [k5|] eqn:Hk5; [|inversion H].
  destruct (read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32))
    as [buf|] eqn:Hw; [|inversion H].
  destruct (bv_eqb k4 (Z_to_bv 64 4) &&
            bv_eqb k5 (Z_to_bv 64 5))%bool eqn:Hkeys;
    [|inversion H].
  apply record_copyins_ok_inv in H as (core & Hcore & ->).
  unfold pure in Hcore. inversion Hcore; subst.
  cbn. apply check_hwprobe_response_refl.
Qed.

Lemma check_riscv_hwprobe_complete_unmodeled :
  forall i pairs count cpusetsize cpus flags eff m,
  riscv_hwprobe_spec pairs count cpusetsize cpus flags i m Unmodeled ->
  check_riscv_hwprobe i pairs count cpusetsize cpus flags eff m =
    CheckUnmodeled.
Proof.
  intros i pairs count cpusetsize cpus flags eff m H.
  unfold riscv_hwprobe_spec in H.
  unfold check_riscv_hwprobe.
  destruct (negb (w_is0 flags)) eqn:Hflags.
  { destruct (hwprobe_which_cpus_ready_b flags cpusetsize cpus);
      [reflexivity|].
    unfold err_ret, ret_only in H. discriminate H. }
  cbv iota in H |- *.
  destruct (negb (bv_eqb count (Z_to_bv 64 2))) eqn:Hcount;
    [reflexivity|].
  cbv iota in H |- *.
  destruct (negb (w_is0 cpusetsize && w_is0 cpus)%bool) eqn:Hcpus;
    [reflexivity|].
  cbv iota in H |- *.
  apply bind_input_model_inv in H.
  destruct (m_hwprobe m) as [[ext perf]|] eqn:Hhw;
    [|reflexivity].
  destruct (negb (hwprobe_response_wf ext perf)) eqn:Hwf;
    [reflexivity|].
  destruct (negb (access_okb pairs 32)) eqn:Haccess;
    [reflexivity|].
  destruct (read_u64 (in_mem i) pairs) as [k4|] eqn:Hk4;
    [|reflexivity].
  destruct (read_u64 (in_mem i) (pairs + Z_to_bv 64 16))
    as [k5|] eqn:Hk5; [|reflexivity].
  destruct (read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32))
    as [buf|] eqn:Hw; [|reflexivity].
  destruct (bv_eqb k4 (Z_to_bv 64 4) &&
            bv_eqb k5 (Z_to_bv 64 5))%bool eqn:Hkeys;
    [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  unfold pure in H. discriminate H.
Qed.
