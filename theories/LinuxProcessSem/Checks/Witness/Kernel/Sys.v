(** * LinuxProcessSem.Checks.Witness.Kernel.Sys — the getpid (172), gettid (178), setsid (157), uname (160), prlimit64 (261) witnesses, and their proofs

    Mirrors [Sys/Kernel/Sys.v], which answers to Linux [kernel/sys.c]:
    this file holds the witnesses for the syscalls defined there, and no
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
  Prelude Kernel.Fork.

(** getpid witness: the same witness as set_tid_address's, because
    [Kernel.Sys.getpid_spec] is the same relation. *)

Definition getpid_witness : Model -> outcome SyscallEffect :=
  set_tid_address_witness.

Lemma getpid_witness_ok : forall i m, getpid_spec i m (getpid_witness m).
Proof. exact set_tid_address_witness_ok. Qed.

(** gettid witness: the same witness again, because
    [Kernel.Sys.gettid_spec] is the same relation. *)

Definition gettid_witness : Model -> outcome SyscallEffect :=
  set_tid_address_witness.

Lemma gettid_witness_ok : forall i m, gettid_spec i m (gettid_witness m).
Proof. exact set_tid_address_witness_ok. Qed.

(** setsid witness: -EPERM, which is admissible whatever the model
    believes — it is the only answer once a setsid has succeeded, and
    [Kernel.Sys.setsid_spec]'s untracked-environment arm before that.  It
    also leaves the model alone, which is why this witness needs no
    case split. *)
Definition setsid_witness (m : Model) : outcome SyscallEffect :=
  ret_outcome (errno_ret EPERM) m.

Lemma setsid_witness_ok : forall i m, setsid_spec i m (setsid_witness m).
Proof.
  intros. unfold setsid_spec, setsid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (m_setsid_succeeded m); cbv iota;
    [apply pure_ok | apply alt_l; apply pure_ok].
Qed.

(** ioctl witness: -EBADF on a closed fd, -ENOTTY on a terminal-only
    request, [Unmodeled] on any other request. *)

(* =========================================================================
   fsync (82) / fdatasync (83) — deterministic and, on success, inert:
   0 for any file or directory fd, -EINVAL for a channel, -EBADF
   otherwise.  No arm is [Unmodeled].
   ========================================================================= *)

(** One utsname inside [Kernel.Sys.utsname_wf]'s envelope: the two
    members the kernel source pins, and NUL for the four it does not.
    That is a name a real kernel can hold — [sethostname(name, 0)] and
    [setdomainname(name, 0)] each clear their member outright — but the
    witness does not need it to be: it exhibits ONE admissible outcome so
    that progress has something to step to, exactly as [rlim64_zero] does
    for the limit pair. *)
Definition utsname_default : list byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal [] ++ uts_literal [] ++ uts_literal []
  ++ uts_literal uts_machine_chars
  ++ uts_literal [].

Lemma utsname_default_wf : utsname_wf utsname_default = true.
Proof. vm_compute. reflexivity. Qed.

Definition uname_witness (name : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (access_okb name NEW_UTSNAME_SIZE)
  then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | None => Unmodeled
    | Some _ =>
        match m_utsname m with
        | Some bs => Ok (mkEffect (Z_to_bv 64 0) [(name, bs)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(name, utsname_default)] [])
               (with_utsname utsname_default m) []
        end
    end.

Lemma uname_witness_ok : forall name i m,
  uname_spec name i m (uname_witness name i m).
Proof.
  intros name i m. unfold uname_spec, uname_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb name NEW_UTSNAME_SIZE)); [apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) name (Z_to_bv 64 NEW_UTSNAME_SIZE))
    as [bs1|]; [|apply unmodeled_intro].
  destruct (m_utsname m) as [bs|]; [apply pure_ok|].
  eapply bind_step;
    [apply (choose_ok _ utsname_default); exact utsname_default_wf|].
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

Definition rlim64_zero : list byte := repeat (Z_to_bv 8 0) 16.

Lemma rlim64_zero_wf : rlim64_wf rlim64_zero = true.
Proof. reflexivity. Qed.

Definition prlimit64_core_witness (pid resource new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (w_is0 pid) then Unmodeled
  else if negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE) then Unmodeled
  else if (w_is0 new_rlim && w_is0 old_rlim)%bool then Unmodeled
  else if (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool then Unmodeled
  else if w_is0 new_rlim then
    match read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16) with
    | None =>
        if negb (access_okb old_rlim 16)
        then ret_outcome (errno_ret EFAULT) m else Unmodeled
    | Some _ =>
        match m_rlimit_core m with
        | Some bs => Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, rlim64_zero)] [])
               (with_rlimit_core rlim64_zero m) []
        end
    end
  else
    match m_rlimit_core m with
    | None => Unmodeled
    | Some bs0 =>
        match read_bytes_map (in_mem i) new_rlim (Z_to_bv 64 16) with
        | None =>
            if negb (access_okb new_rlim 16)
            then ret_outcome (errno_ret EFAULT) m else Unmodeled
        | Some nb =>
            outcome_copyins [(new_rlim, 16%nat)]
            (
            if (bv_unsigned (rlim64_hard nb) <? bv_unsigned (rlim64_soft nb))%Z
            then ret_outcome (errno_ret EINVAL) m
            else if negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0))
            then Unmodeled
            else ret_outcome (Z_to_bv 64 0) (with_rlimit_core nb m))
        end
    end.

Lemma prlimit64_core_witness_ok : forall pid resource new_rlim old_rlim i m,
  prlimit64_core_spec pid resource new_rlim old_rlim i m
    (prlimit64_core_witness pid resource new_rlim old_rlim i m).
Proof.
  intros pid resource new_rlim old_rlim i m.
  unfold prlimit64_core_spec, prlimit64_core_witness.
  destruct (negb (w_is0 pid)); [apply unmodeled_intro|].
  destruct (negb (Z.eqb (bv_unsigned resource) RLIMIT_CORE));
    [apply unmodeled_intro|].
  destruct (w_is0 new_rlim && w_is0 old_rlim)%bool; [apply unmodeled_intro|].
  destruct (negb (w_is0 new_rlim) && negb (w_is0 old_rlim))%bool;
    [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (w_is0 new_rlim).
  - destruct (read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16)) as [bs1|].
    + destruct (m_rlimit_core m) as [bs|]; [apply pure_ok|].
      eapply bind_step; [apply (choose_ok _ rlim64_zero); exact rlim64_zero_wf|].
      eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb old_rlim 16));
        [apply pure_ok|apply unmodeled_intro].
  - destruct (m_rlimit_core m) as [bs0|]; [|apply unmodeled_intro].
    destruct (read_bytes_map (in_mem i) new_rlim (Z_to_bv 64 16)) as [nb|].
    + apply record_copyins_outcome.
      destruct ((bv_unsigned (rlim64_hard nb)
                 <? bv_unsigned (rlim64_soft nb))%Z); [apply pure_ok|].
      destruct (negb (bv_eqb (rlim64_hard nb) (rlim64_hard bs0)));
        [apply unmodeled_intro|].
      eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (negb (access_okb new_rlim 16));
        [apply pure_ok|apply unmodeled_intro].
Qed.

Definition rlim64_stack_default : list byte :=
  let soft := word_le8 (Z_to_bv 64 stack_max_size) in soft ++ soft.

Lemma rlim64_stack_default_wf : rlim64_stack_wf rlim64_stack_default = true.
Proof. vm_compute. reflexivity. Qed.

Definition prlimit64_stack_witness (pid new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (w_is0 pid) then Unmodeled
  else if negb (w_is0 new_rlim) then Unmodeled
  else if w_is0 old_rlim then Unmodeled
  else
    match read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16) with
    | None =>
        if negb (access_okb old_rlim 16)
        then ret_outcome (errno_ret EFAULT) m else Unmodeled
    | Some _ =>
        match m_rlimit_stack m with
        | Some bs => Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, rlim64_stack_default)] [])
               (with_rlimit_stack rlim64_stack_default m) []
        end
    end.

Lemma prlimit64_stack_witness_ok : forall pid new_rlim old_rlim i m,
  prlimit64_stack_spec pid new_rlim old_rlim i m
    (prlimit64_stack_witness pid new_rlim old_rlim i m).
Proof.
  intros pid new_rlim old_rlim i m.
  unfold prlimit64_stack_spec, prlimit64_stack_witness.
  destruct (negb (w_is0 pid)); [apply unmodeled_intro|].
  destruct (negb (w_is0 new_rlim)); [apply unmodeled_intro|].
  destruct (w_is0 old_rlim); [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16)) as [bs1|].
  - destruct (m_rlimit_stack m) as [bs|]; [apply pure_ok|].
    eapply bind_step;
      [apply (choose_ok _ rlim64_stack_default); exact rlim64_stack_default_wf|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - destruct (negb (access_okb old_rlim 16));
      [apply pure_ok|apply unmodeled_intro].
Qed.

Definition rlim64_nofile_default (m : Model) : list byte :=
  word_le8 (m_nofile m) ++ word_le8 (Z_to_bv 64 (2 ^ 31 - 64)).

Lemma rlim64_nofile_default_wf : forall m,
  rlim64_nofile_ready_b m = true ->
  rlim64_nofile_wf (rlim64_nofile_default m) m = true.
Proof.
  intros m Hready.
  unfold rlim64_nofile_ready_b in Hready.
  apply andb_true_iff in Hready as [_ Hhi].
  assert (Hhard : forall w,
    rlim64_hard (word_le8 w ++ word_le8 (Z_to_bv 64 (2 ^ 31 - 64))) =
      Z_to_bv 64 (2 ^ 31 - 64)).
  { intro w. vm_compute. reflexivity. }
  unfold rlim64_nofile_wf, rlim64_nofile_default.
  rewrite Hhard.
  cbn [word_le8 app length firstn Nat.eqb].
  rewrite stat_bytes_eqb_refl.
  replace (bv_unsigned (Z_to_bv 64 (2 ^ 31 - 64)))
    with (2 ^ 31 - 64)%Z by (vm_compute; reflexivity).
  rewrite Z.leb_refl.
  cbn [andb].
  rewrite andb_true_r.
  exact Hhi.
Qed.

Definition prlimit64_nofile_witness (pid new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if negb (w_is0 pid) then Unmodeled
  else if negb (w_is0 new_rlim) then Unmodeled
  else if w_is0 old_rlim then Unmodeled
  else if negb (rlim64_nofile_ready_b m) then Unmodeled
  else
    match read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16) with
    | None =>
        if negb (access_okb old_rlim 16)
        then ret_outcome (errno_ret EFAULT) m else Unmodeled
    | Some _ =>
        match m_rlimit_nofile m with
        | Some bs => Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []) m []
        | None =>
            Ok (mkEffect (Z_to_bv 64 0)
                 [(old_rlim, rlim64_nofile_default m)] [])
               (with_rlimit_nofile (rlim64_nofile_default m) m) []
        end
    end.

Lemma prlimit64_nofile_witness_ok : forall pid new_rlim old_rlim i m,
  prlimit64_nofile_spec pid new_rlim old_rlim i m
    (prlimit64_nofile_witness pid new_rlim old_rlim i m).
Proof.
  intros pid new_rlim old_rlim i m.
  unfold prlimit64_nofile_spec, prlimit64_nofile_witness.
  destruct (negb (w_is0 pid)); [apply unmodeled_intro|].
  destruct (negb (w_is0 new_rlim)); [apply unmodeled_intro|].
  destruct (w_is0 old_rlim); [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (rlim64_nofile_ready_b m)) eqn:Hr;
    [apply unmodeled_intro|].
  destruct (read_bytes_map (in_wmem i) old_rlim (Z_to_bv 64 16)) as [bs1|].
  - destruct (m_rlimit_nofile m) as [bs|]; [apply pure_ok|].
    eapply bind_step;
      [apply (choose_ok _ (rlim64_nofile_default m));
       apply rlim64_nofile_default_wf;
       now apply Bool.negb_false_iff in Hr|].
    eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - destruct (negb (access_okb old_rlim 16));
      [apply pure_ok|apply unmodeled_intro].
Qed.

Definition prlimit64_witness (pid resource new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if Z.eqb (bv_unsigned resource) RLIMIT_STACK
  then prlimit64_stack_witness pid new_rlim old_rlim i m
  else if Z.eqb (bv_unsigned resource) RLIMIT_NOFILE
  then prlimit64_nofile_witness pid new_rlim old_rlim i m
  else prlimit64_core_witness pid resource new_rlim old_rlim i m.

Lemma prlimit64_witness_ok : forall pid resource new_rlim old_rlim i m,
  prlimit64_spec pid resource new_rlim old_rlim i m
    (prlimit64_witness pid resource new_rlim old_rlim i m).
Proof.
  intros. unfold prlimit64_spec, prlimit64_witness.
  destruct (Z.eqb (bv_unsigned resource) RLIMIT_STACK);
    [apply prlimit64_stack_witness_ok|].
  destruct (Z.eqb (bv_unsigned resource) RLIMIT_NOFILE);
    [apply prlimit64_nofile_witness_ok|apply prlimit64_core_witness_ok].
Qed.

(* =========================================================================
   The dispatcher
   ========================================================================= *)

(* =========================================================================
   ftruncate (46) — every arm is deterministic, so the witness is just the
   spec's own answer: there is no [alt] and no [errno_from] to choose a
   branch of, and receptivity needs no inhabitation lemma.
   ========================================================================= *)

(* =========================================================================
   Credentials — one admissible outcome for each of the eight id calls.
   ========================================================================= *)

Lemma In_ENOMEM_setid_errnos : forall b, In ENOMEM (setid_errnos b).
Proof. destruct b; simpl; auto. Qed.

(** The readers are total: the stored id, and no model step. *)
Definition getid_witness (sel : Creds -> word) (m : Model)
    : outcome SyscallEffect :=
  ret_outcome (sel (m_creds m)) m.

Lemma getid_witness_ok : forall sel i m, getid_spec sel i m (getid_witness sel m).
Proof.
  intros. unfold getid_spec, getid_witness.
  eapply bind_step; [apply get_model_ok|]. apply pure_ok.
Qed.

(** [setuid]/[setgid]: -EINVAL for [(uid_t)-1], and otherwise the
    -ENOMEM every other branch admits — [prepare_creds] can fail on all
    three of them, so one witness covers the whole spec without deciding
    which branch the credentials take. *)
Definition setid_witness (v : word) (m : Model) : outcome SyscallEffect :=
  if bv_eqb v ID_MINUS_ONE then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (errno_ret ENOMEM) m.

Lemma setid_witness_ok : forall get put user v i m,
  setid_spec get put user v i m (setid_witness v m).
Proof.
  intros. unfold setid_spec, setid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  repeat match goal with
         | |- context [ if ?b then _ else _ ] => destruct b eqn:?; cbv beta iota zeta
         end;
  first [ apply pure_ok
        | apply alt_l;
          (eapply bind_step;
            [ apply errno_from_witness; apply In_ENOMEM_setid_errnos
            | apply pure_ok ]) ].
Qed.

(** [setresuid]/[setresgid]: the no-op fast path and the -EPERM refusal
    are both total, and every remaining branch admits -ENOMEM, so the
    witness has to follow the spec's first two tests and can stop
    there. *)
Definition setresid_witness (get : Creds -> IdTriple) (r e s : word) (m : Model)
    : outcome SyscallEffect :=
  let t := get (m_creds m) in
  let pick (a : word) (cur : word) := if bv_eqb a ID_MINUS_ONE then cur else a in
  let nr := pick r (id_real t) in
  let ne := pick e (id_eff t) in
  let ns := pick s (id_saved t) in
  if andb (andb (bv_eqb nr (id_real t)) (bv_eqb ne (id_eff t)))
          (bv_eqb ns (id_saved t)) then
    ret_outcome (Z_to_bv 64 0) m
  else
    let is_old (x : word) :=
      orb (orb (bv_eqb x (id_real t)) (bv_eqb x (id_eff t))) (bv_eqb x (id_saved t)) in
    if andb (negb (andb (andb (is_old nr) (is_old ne)) (is_old ns)))
            (negb (creds_privileged (m_creds m))) then
      ret_outcome (errno_ret EPERM) m
    else
      ret_outcome (errno_ret ENOMEM) m.

Lemma setresid_witness_ok : forall get put user r e s i m,
  setresid_spec get put user r e s i m (setresid_witness get r e s m).
Proof.
  intros. unfold setresid_spec, setresid_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  repeat match goal with
         | |- context [ if ?b then _ else _ ] => destruct b eqn:?; cbv beta iota zeta
         end;
  first [ apply pure_ok
        | apply alt_l;
          (eapply bind_step;
            [ apply errno_from_witness; apply In_ENOMEM_setid_errnos
            | apply pure_ok ]) ].
Qed.

(** The VMA witness picks -EINVAL when the build configuration may
    disable anonymous VMA names.  The capability arm has a fixed answer. *)
Definition prctl_witness (i : SyscallInput) (option_ arg2 : word) (m : Model)
    : outcome SyscallEffect :=
  if Z.eqb (bv_unsigned option_) PR_CAPBSET_READ
  then if (CAP_LAST_CAP <? bv_unsigned arg2)%Z
       then ret_outcome (errno_ret EINVAL) m
       else ret_outcome (Z_to_bv 64 1) m
  else if Z.eqb (bv_unsigned option_) PR_SET_VMA
       then if negb (w_is0 arg2) then ret_outcome (errno_ret EINVAL) m
            else if prctl_vma_name_ready_b i m
                 then ret_outcome (errno_ret EINVAL) m
                 else Unmodeled
       else Unmodeled.

Lemma prctl_witness_ok : forall option_ arg2 i m,
  prctl_spec option_ arg2 i m (prctl_witness i option_ arg2 m).
Proof.
  intros option_ arg2 i m. unfold prctl_spec, prctl_witness.
  destruct (Z.eqb (bv_unsigned option_) PR_CAPBSET_READ).
  - destruct ((CAP_LAST_CAP <? bv_unsigned arg2)%Z); apply pure_ok.
  - destruct (Z.eqb (bv_unsigned option_) PR_SET_VMA).
    + unfold prctl_vma_name_spec.
      destruct (negb (w_is0 arg2)); [apply pure_ok|].
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta.
      destruct (prctl_vma_name_ready_b i m).
      * apply alt_l. apply pure_ok.
      * apply unmodeled_intro.
    + apply unmodeled_intro.
Qed.
