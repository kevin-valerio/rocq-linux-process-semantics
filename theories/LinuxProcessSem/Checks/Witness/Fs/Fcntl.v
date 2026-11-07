(** * LinuxProcessSem.Checks.Witness.Fs.Fcntl — the fcntl (25) witness, and its proof

    Mirrors [Sys/Fs/Fcntl.v], which answers to Linux [fs/fcntl.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Fs.ReadWrite.

(** fcntl witness: -EBADF on a closed fd, 0 for F_SETFD and for an
    F_SETFL that provably changes nothing, the derived flag word for an
    F_GETFL on an fd kind [Fcntl.getfl_f_flags] answers for, the tracked
    channel descriptor bit for F_GETFD, and [Unmodeled] otherwise. *)
Definition fcntl_witness (fd cmd arg : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      if bv_eqb cmd F_SETFD then
        ret_outcome (Z_to_bv 64 0) (setfd_model fd arg e m)
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg
      then ret_outcome (Z_to_bv 64 0) m
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags m e with
        | Some fl => ret_outcome fl m
        | None => Unmodeled
        end
      else if bv_eqb cmd F_GETFD then
        match getfd_flags m fd e with
        | Some fl => ret_outcome fl m
        | None => Unmodeled
        end
      else Unmodeled
  end.

Lemma fcntl_witness_ok : forall fd cmd arg i m,
  fcntl_spec fd cmd arg i m (fcntl_witness fd cmd arg m).
Proof.
  intros. unfold fcntl_spec, fcntl_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - destruct (bv_eqb cmd F_SETFD) eqn:Hd.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd.
      eapply bind_step; [apply modify_ok|apply pure_ok].
    + destruct (bv_eqb cmd F_SETFL && setfl_noop_on e arg) eqn:Hl.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd; srw Hl. apply pure_ok.
      * destruct (bv_eqb cmd F_GETFL) eqn:Hg.
        -- destruct (getfl_f_flags m e) as [fl|] eqn:Hgf.
           ++ eapply bind_step; [apply get_model_ok|].
              cbv beta iota; srw Hfd; srw Hl; srw Hgf. apply pure_ok.
           ++ eapply bind_step; [apply get_model_ok|].
              cbv beta iota; srw Hfd; srw Hl; srw Hgf. apply unmodeled_intro.
        -- destruct (bv_eqb cmd F_GETFD) eqn:Hfdcmd.
           ++ destruct (getfd_flags m fd e) as [fl|] eqn:Hgf.
              ** eapply bind_step; [apply get_model_ok|].
                 cbv beta iota; srw Hfd; srw Hl; srw Hgf.
                 apply pure_ok.
              ** eapply bind_step; [apply get_model_ok|].
                 cbv beta iota; srw Hfd; srw Hl; srw Hgf.
                 apply unmodeled_intro.
           ++ eapply bind_step; [apply get_model_ok|].
              cbv beta iota; srw Hfd; srw Hl.
              apply unmodeled_intro.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
Qed.
