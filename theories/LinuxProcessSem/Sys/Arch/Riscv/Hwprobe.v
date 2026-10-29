(** The two-key riscv_hwprobe call used by Go on riscv64.  The kernel
    implementation is arch/riscv/kernel/sys_hwprobe.c (Linux v6.18.46,
    commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** The covered hardware exposes exactly the base F/D and C bits through
    key 4.  Key 5 returns one of the kernel's five scalar misaligned access
    classes.  Optional ISA extensions need their own hardware scope. *)
Definition hwprobe_response_wf (ext perf : word) : bool :=
  (bv_eqb ext (Z_to_bv 64 3)
   && (bv_unsigned perf <=? 4)%Z)%bool.

Definition hwprobe_bytes (ext perf : word) : list byte :=
  word_le8 (Z_to_bv 64 4) ++ word_le8 ext ++
  word_le8 (Z_to_bv 64 5) ++ word_le8 perf.

Definition hwprobe_key_reads (pairs : word) : list (word * nat) :=
  [(pairs, 8%nat); (pairs + Z_to_bv 64 16, 8%nat)].

(** Flag 1 selects [hwprobe_get_cpus].  With a nonempty CPU set that
    branch can succeed, so it must not be given the reserved-flag errno. *)
Definition hwprobe_which_cpus_ready_b (flags cpusetsize cpus : word) : bool :=
  (bv_eqb flags (Z_to_bv 64 1) &&
   negb (w_is0 cpusetsize || w_is0 cpus))%bool.

(** Only pairs {IMA_EXT_0, CPUPERF_0}, all online CPUs, and flags 0 are
    covered.  The two values come from the launch input.  The kernel reads
    each key and writes back both key and value; a successful call has a
    32-byte output and two 8-byte key reads.  Partial user faults and other
    query shapes remain unmodeled. *)
Definition riscv_hwprobe_spec (pairs pair_count cpusetsize cpus flags : word)
    : Sys SyscallEffect :=
  if negb (w_is0 flags) then
    if hwprobe_which_cpus_ready_b flags cpusetsize cpus
    then unmodeled else err_ret EINVAL
  else if negb (bv_eqb pair_count (Z_to_bv 64 2)) then unmodeled
  else if negb (w_is0 cpusetsize && w_is0 cpus)%bool then unmodeled
  else
  i <- input ;;
  m <- get_model ;;
  match m_hwprobe m with
  | None => unmodeled
  | Some (ext, perf) =>
      if negb (hwprobe_response_wf ext perf) then unmodeled
      else if negb (access_okb pairs 32) then unmodeled
      else
      match read_u64 (in_mem i) pairs,
            read_u64 (in_mem i) (pairs + Z_to_bv 64 16),
            read_bytes_map (in_wmem i) pairs (Z_to_bv 64 32) with
      | Some k4, Some k5, Some _ =>
          if (bv_eqb k4 (Z_to_bv 64 4) &&
              bv_eqb k5 (Z_to_bv 64 5))%bool
          then record_copyins (hwprobe_key_reads pairs)
                 (pure (mkEffect (Z_to_bv 64 0)
                    [(pairs, hwprobe_bytes ext perf)] []))
          else unmodeled
      | _, _, _ => unmodeled
      end
  end.
