(** * LinuxProcessSem.Checks.Cases.Mm.Mprotect — worked examples over mprotect (226)

    Mirrors [Sys/Mm/Mprotect.v], which answers to Linux [mm/mprotect.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite.

Definition readonly_image_model : Model :=
  with_vmmaps
    (mkVmMapsFull [(65536, 4096)] [] [] 0 0 16384 0 demo_sp)
    noaccess_base.

Definition readonly_image_input : SyscallInput :=
  mkInput 226 [65536; 4096; 1; 0; 0; 0]
    (fun _ => Some 0x5a) (fun _ => Some 0x5a).

Example mprotect_readonly_image_accepts_success :
  check_syscall readonly_image_input
    (mkEffectU 0 [] [] [] [mkProtectRO 65536 4096] [])
    readonly_image_model = CheckOk readonly_image_model [].
Proof. check_eq. Qed.

Example mprotect_readonly_image_rejects_missing_permission_change :
  check_syscall readonly_image_input (mkEffect 0 [] [])
    readonly_image_model = CheckReject.
Proof. check_eq. Qed.

Example mprotect_middle_splits_noaccess_and_zeros_exactly :
  check_syscall
    (mkInput 226 [69632; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(65536, 12288)]
          [(65536, 4096); (73728, 4096)] 0 0 16384 0 demo_sp)
        noaccess_three_pages) [].
Proof. check_eq. Qed.

Example mprotect_noaccess_errno_preserves_ledger :
  check_syscall
    (mkInput 226 [69632; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

(** Exposing a reserved page consumes backed capacity at the permission
    transition.  With a zero-byte budget the successful effect is rejected,
    while the modeled ENOMEM outcome remains available. *)
Definition noaccess_zero_backing : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)
    noaccess_three_pages.

Example mprotect_over_backed_budget_rejects_success :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(65536, 4096)]) noaccess_zero_backing
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_over_backed_budget_allows_enomem :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_zero_backing
  = CheckOk noaccess_zero_backing [].
Proof. check_eq. Qed.

Example mprotect_unmapped_forged_success_is_unmodeled :
  check_syscall
    (mkInput 226 [131072; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mprotect_already_rw_errno_is_rejected :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_noaccess_outside_vm_maps_is_unmodeled :
  check_syscall
    (mkInput 226 [65536; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(65536, 4096)]) noaccess_unowned
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mprotect_wrapping_end_is_enomem :
  check_syscall
    (mkInput 226 [9223372036854775808; 9223372036854775808; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_wrapping_end_success_is_rejected :
  check_syscall
    (mkInput 226 [9223372036854775808; 9223372036854775808; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_wrapping_end_precedes_unsupported_prot :
  check_syscall
    (mkInput 226 [9223372036854775808; 9223372036854775808; 4; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_unaligned_precedes_zero_length :
  check_syscall
    (mkInput 226 [65537; 0; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_growsdown_alone_is_not_a_conflict :
  check_syscall
    (mkInput 226 [65536; 0; 16777219; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_growsup_alone_is_not_a_conflict :
  check_syscall
    (mkInput 226 [65536; 0; 33554435; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Example mprotect_growsdown_alone_einval_is_rejected :
  check_syscall
    (mkInput 226 [65536; 0; 16777219; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_growsup_alone_einval_is_rejected :
  check_syscall
    (mkInput 226 [65536; 0; 33554435; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckReject.
Proof. check_eq. Qed.

Example mprotect_grows_conflict_is_einval :
  check_syscall
    (mkInput 226 [65536; 0; 50331651; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = CheckOk noaccess_three_pages [].
Proof. check_eq. Qed.

Definition mprotect_lazy_guard : Model :=
  with_vm_backing [(65536, 8192)] [65536]
    (with_vmmaps
      (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 4096 0 demo_sp)
      noaccess_base).

(** Exposing a MAP_NORESERVE guard keeps its lazy provenance and the first
    page's existing first-touch charge; the second page is not charged until
    an instruction actually accesses it. *)
Example mprotect_lazy_guard_preserves_backing_provenance :
  check_syscall
    (mkInput 226 [69632; 4096; 3; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(69632, 4096)]) mprotect_lazy_guard
  = CheckOk (mprotect_model_next mprotect_lazy_guard 69632 4096) [].
Proof. check_eq. Qed.

Example mprotect_lazy_guard_does_not_eagerly_charge :
  let post := mprotect_model_next mprotect_lazy_guard 69632 4096 in
  m_vm_lazy post = [(65536, 8192)] /\
  m_vm_materialized post = [65536] /\
  vm_backing_used post = 4096%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

(** ** The read-only downgrade, pinned at the checker

    [mprotect(addr, len, PROT_READ)] over a live rw mapping is the shape
    an allocator reaches for after filling a buffer, and Linux answers it
    with 0 (mm/mprotect.c [do_mprotect_pkey] / [mprotect_fixup]: newflags
    loses VM_WRITE and the mapping stays live and readable).  The model
    declines it, and [Sys/Mm/Mprotect.v] argues why: anonymous memory has
    one representation, which is simultaneously the readable view and the
    writable one, so a readable-not-writable page cannot be encoded.

    These read the checker directly, and the first is the one that
    matters: offering the checker the answer the real kernel gives has
    to yield [CheckUnmodeled], not [CheckOk].
    A spec that widened [mprotect_modeled_b] to "prot is a subset of the
    permissions the range already has" would take that 0 and admit every
    later store to a page Linux has made read-only. *)
Example mprotect_read_only_downgrade_is_unmodeled :
  check_syscall
    (mkInput 226 [65536; 4096; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** The declining arm is reached on the ARGUMENT SHAPE, so no offered
    effect rescues it: a zero-fill range is refused for the same reason,
    rather than being rejected as the wrong effect for a modeled call. *)
Example mprotect_read_only_downgrade_with_zeros_is_unmodeled :
  check_syscall
    (mkInput 226 [65536; 4096; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(65536, 4096)])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** PROT_READ over a range that is still PROT_NONE is declined too, which
    is worth pinning separately: that range IS in [vm_noaccess], so the
    rw transition's own gate matches on everything but the prot word.  A
    spec that tested containment before the prot would expose the page
    and hand the effect's zero-fill to a program that may not write it. *)
Example mprotect_read_only_over_noaccess_is_unmodeled :
  check_syscall
    (mkInput 226 [69632; 4096; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** The positive half at the same prot: the gates ahead of the prot test
    answer for PROT_READ exactly as they do for the modeled rw, because
    Linux takes its zero-length return before validating prot at all.
    Its negative twin is below — a zero-length call admits 0 and nothing
    else. *)
Example mprotect_read_only_zero_length_is_zero :
  check_syscall
    (mkInput 226 [65536; 0; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckOk (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384)
               noaccess_base) [].
Proof. check_eq. Qed.

Example mprotect_read_only_zero_length_errno_is_rejected :
  check_syscall
    (mkInput 226 [65536; 0; 1 (* PROT_READ *); 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.
