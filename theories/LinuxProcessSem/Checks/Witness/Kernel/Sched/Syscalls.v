(** * LinuxProcessSem.Checks.Witness.Kernel.Sched.Syscalls — the sched_getaffinity (123), sched_setscheduler (119) and sched_yield (124) witnesses, and their proofs

    Mirrors [Sys/Kernel/Sched/Syscalls.v], which answers to Linux
    [kernel/sched/syscalls.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** An eight-byte mask is an admissible witness after the destination
    and first-observation gates pass. *)
Definition sched_getaffinity_witness (i : SyscallInput) (len : word) (m : Model)
    : outcome SyscallEffect :=
  if affinity_len_einval_b len then ret_outcome (errno_ret EINVAL) m
  else
  let pid := in_arg i 0 in
  let ptr := in_arg i 2 in
  if negb (sched_targets_self_b pid m) then Unmodeled else
  if negb (access_okb ptr 8) then Unmodeled else
  match read_bytes_map (in_wmem i) ptr (Z_to_bv 64 8) with
  | None => Unmodeled
  | Some _ =>
      if negb (affinity_size_ready_b len m) then Unmodeled else
      let bs := repeat (Z_to_bv 8 0) 8 in
      Ok (mkEffect (Z_to_bv 64 8) [(ptr, bs)] [])
         (affinity_after_success m) []
  end.

Lemma sched_getaffinity_witness_ok : forall len i m,
  sched_getaffinity_spec len i m (sched_getaffinity_witness i len m).
Proof.
  intros. unfold sched_getaffinity_spec, sched_getaffinity_witness.
  destruct (affinity_len_einval_b len) eqn:Hlen.
  - unfold err_ret, ret_only. apply pure_ok.
  - eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta.
    destruct (negb (sched_targets_self_b (in_arg i 0) m)) eqn:Hself;
      cbv iota; [apply unmodeled_intro|].
    destruct (negb (access_okb (in_arg i 2) 8)) eqn:Hacc;
      cbv iota; [apply unmodeled_intro|].
    destruct (read_bytes_map (in_wmem i) (in_arg i 2) (Z_to_bv 64 8))
      as [dst|] eqn:Hdst; cbv iota; [|apply unmodeled_intro].
    destruct (negb (affinity_size_ready_b len m)) eqn:Hready;
      cbv iota; [apply unmodeled_intro|].
    apply alt_r.
    eapply bind_step; [apply (choose_ok _ (repeat (Z_to_bv 8 0) 8));
                        now rewrite repeat_length|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(** [sched_setscheduler] (119) is deterministic on every branch — it
    draws nothing and the one success changes no model state — so the
    witness is the branch itself, ledger included.  Failing closed is an
    admissible outcome, which is what makes progress hold on the three
    declines. *)
Definition sched_setscheduler_witness (pid policy param : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if (sint32 policy <? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else if (w_is0 param || (sint32 pid <? 0)%Z)%bool
  then ret_outcome (errno_ret EINVAL) m
  else
  match read_bytes_map (in_mem i) param (Z_to_bv 64 4) with
  | None =>
      if negb (access_okb param 4)
      then ret_outcome (errno_ret EFAULT) m
      else Unmodeled
  | Some bs =>
      if negb (sched_targets_self_b pid m) then Unmodeled
      else
        match sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs)) with
        | Some r =>
            Ok (with_copyins [(param, 4%nat)] (mkEffect r [] [])) m []
        | None => Unmodeled
        end
  end.

Lemma sched_setscheduler_witness_ok : forall i pid policy param m,
  sched_setscheduler_spec pid policy param i m
    (sched_setscheduler_witness pid policy param i m).
Proof.
  intros. unfold sched_setscheduler_spec, sched_setscheduler_witness.
  destruct ((sint32 policy <? 0)%Z) eqn:Hpolneg;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  destruct ((w_is0 param || (sint32 pid <? 0)%Z)%bool) eqn:Hearly;
    [unfold err_ret, ret_only, ret_outcome; apply pure_ok|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (read_bytes_map (in_mem i) param (Z_to_bv 64 4)) as [bs|] eqn:Hread.
  - destruct (negb (sched_targets_self_b pid m)) eqn:Hself;
      [apply record_copyins_unmodeled; apply unmodeled_intro|].
    destruct (sched_setscheduler_answer (bv_unsigned (abi_low32 policy))
                (bv_unsigned (le_bytes_to_word bs))) as [r|] eqn:Hans.
    + apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
    + apply record_copyins_unmodeled; apply unmodeled_intro.
  - destruct (negb (access_okb param 4)) eqn:Hacc;
      [unfold err_ret, ret_only, ret_outcome; apply pure_ok
      |apply unmodeled_intro].
Qed.

(** [sched_yield] (124) has one outcome and no branch at all, so the
    witness is that outcome.  It is also the only arm here whose witness
    is never [Unmodeled]: the spec has no fail-closed branch to exhibit
    (see [Kernel.Sched.Syscalls.sched_yield_spec]). *)
Definition sched_yield_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (Z_to_bv 64 0) m.

Lemma sched_yield_witness_ok : forall i m,
  sched_yield_spec i m (sched_yield_witness m).
Proof.
  intros. unfold sched_yield_spec, sched_yield_witness.
  unfold ret_only, ret_outcome. apply pure_ok.
Qed.
