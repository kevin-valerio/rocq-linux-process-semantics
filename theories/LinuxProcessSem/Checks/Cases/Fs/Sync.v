(** * LinuxProcessSem.Checks.Cases.Fs.Sync — worked examples over fsync (82), fdatasync (83)

    Mirrors [Sys/Fs/Sync.v], which answers to Linux [fs/sync.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

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

Definition fsync_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdFile [102] 7); (4, FdFileW [103] 9); (5, FdDir) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120]); ([103], [121])] None None None.

Example fsync_proc_maps_is_einval :
  let m := with_fds (fd_insert (m_fds fsync_model) 6 (FdProcMaps 0))
                       fsync_model in
  check_syscall
    (mkInput 82 [6; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
  /\ check_syscall
       (mkInput 83 [6; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m []
  /\ check_syscall
       (mkInput 82 [6; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) m = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE CHANNEL ARM ON fd 0.

    The second conjunct is what makes the first non-vacuous: a kernel
    claiming SUCCESS is rejected, so this pins -EINVAL rather than
    merely admitting it. *)

Example fsync_on_a_channel_is_einval :
  check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_model
  = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model
     = CheckReject
  (* and [fdatasync] answers fd 0 identically *)
  /\ check_syscall (mkInput 83 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fsync_model
     = CheckOk fsync_model []
  /\ check_syscall (mkInput 83 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE fd32 TRUNCATION ALIASES ONTO fd 0.

    What is worth pinning is that truncation ALIASES rather than
    REJECTS — a model comparing the full 64-bit register would have
    found no such fd and answered -EBADF.  The third conjunct rules that
    out.

    The first conjunct is an equation between two checker calls, so on
    its own it would hold vacuously if BOTH sides were [CheckReject].
    The second names the shared value outright, which is what makes the
    first say what it reads as saying. *)

Example fsync_fd_truncates_to_32_bits :
  check_syscall (mkInput 82 [Z_to_bv 64 (2 ^ 32); 0; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_model
  = check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret EINVAL) [] []) fsync_model
  (* ...and that shared value is an ACCEPTANCE, not a shared rejection *)
  /\ check_syscall (mkInput 82 [Z_to_bv 64 (2 ^ 32); 0; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fsync_model
     = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [Z_to_bv 64 (2 ^ 32); 0; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) fsync_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** SUCCESS IS INERT.  ADMISSION REASON: it pins model-internal state
    that no observation reveals.

    A real run sees only the 0.  That the fd's offset (7 and 9 here) and
    the file's contents came back UNCHANGED, and that no event was
    emitted, is a statement about the model's own state, and the
    equalities below are the whole of it: the returned model is the SAME
    model, and the event list is empty. *)

Example fsync_success_is_inert_on_every_file_kind :
  check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [5; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
  /\ check_syscall (mkInput 83 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model = CheckOk fsync_model [].
Proof. repeat split; check_eq. Qed.

(* -------------------------------------------------------------------------
   prlimit64 (261): the pin, and what no real run can show.

   Nearly all of this spec's fail-closed surface IS reachable from a
   real run — it just calls prlimit64 with a nonzero pid or an unmodeled
   resource id.  Three things a run cannot show are left, and they are
   the whole of this group:

   - THE ENVIRONMENT CANNOT PRODUCE a kernel reporting soft > hard.
     Linux maintains soft <= hard on every path that writes a limit.
     So [Kernel.Sys.rlim64_wf]'s ordering conjunct is stated here or
     nowhere.
   - Nor can it produce a later read delivering a DIFFERENT well-formed
     pair.
   - The rest pin MODEL-INTERNAL STATE — the recorded limit, and that a
     set REPLACES it.  A run reveals only the pair it happened to
     inherit, never that the model is holding it, so the claim is pinned
     here, where the recorded pair is chosen rather than inherited.
   ------------------------------------------------------------------------- *)

(** A [struct rlimit64] with single-byte soft and hard limits. *)
