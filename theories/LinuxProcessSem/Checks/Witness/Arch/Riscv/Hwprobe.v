(** One admissible result for the two-key riscv_hwprobe call. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.
Import ListNotations.
Open Scope bv_scope.

Definition riscv_hwprobe_witness (i : SyscallInput)
    (pairs pair_count cpusetsize cpus flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (w_is0 flags) then
    if hwprobe_which_cpus_ready_b flags cpusetsize cpus
    then Unmodeled else ret_outcome (errno_ret EINVAL) m
  else if negb (bv_eqb pair_count (Z_to_bv 64 2)) then Unmodeled
  else if negb (w_is0 cpusetsize && w_is0 cpus)%bool then Unmodeled
  else
  match m_hwprobe m with
  | None => Unmodeled
  | Some (ext, perf) =>
      if negb (hwprobe_response_wf ext perf) then Unmodeled
      else if negb (access_okb pairs 32) then Unmodeled
      else
      match read_u64 (in_mem i) pairs,
            read_u64 (in_mem i) (pairs + Z_to_bv 64 16),
            read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32) with
      | Some k4, Some k5, Some _ =>
          if (bv_eqb k4 (Z_to_bv 64 4) &&
              bv_eqb k5 (Z_to_bv 64 5))%bool
          then Ok (with_copyins (hwprobe_key_reads pairs)
                     (mkEffect (Z_to_bv 64 0)
                        [(pairs, hwprobe_bytes ext perf)] [])) m []
          else Unmodeled
      | _, _, _ => Unmodeled
      end
  end.

Lemma riscv_hwprobe_witness_ok : forall i pairs count cpusetsize cpus flags m,
  riscv_hwprobe_spec pairs count cpusetsize cpus flags i m
    (riscv_hwprobe_witness i pairs count cpusetsize cpus flags m).
Proof.
  intros i pairs count cpusetsize cpus flags m.
  unfold riscv_hwprobe_spec, riscv_hwprobe_witness.
  destruct (negb (w_is0 flags)).
  { destruct (hwprobe_which_cpus_ready_b flags cpusetsize cpus);
      [apply unmodeled_intro|].
    unfold err_ret, ret_only; apply pure_ok. }
  destruct (negb (bv_eqb count (Z_to_bv 64 2)));
    [apply unmodeled_intro|].
  destruct (negb (w_is0 cpusetsize && w_is0 cpus)%bool);
    [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (m_hwprobe m) as [[ext perf]|];
    [|apply unmodeled_intro].
  destruct (negb (hwprobe_response_wf ext perf));
    [apply unmodeled_intro|].
  destruct (negb (access_okb pairs 32));
    [apply unmodeled_intro|].
  destruct (read_u64 (in_mem i) pairs) as [k4|];
    [|apply unmodeled_intro].
  destruct (read_u64 (in_mem i) (pairs + Z_to_bv 64 16)) as [k5|];
    [|apply unmodeled_intro].
  destruct (read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32))
    as [buf|]; [|apply unmodeled_intro].
  destruct (bv_eqb k4 (Z_to_bv 64 4) &&
            bv_eqb k5 (Z_to_bv 64 5))%bool;
    [|apply unmodeled_intro].
  apply record_copyins_ok_empty; [reflexivity|apply pure_ok].
Qed.
