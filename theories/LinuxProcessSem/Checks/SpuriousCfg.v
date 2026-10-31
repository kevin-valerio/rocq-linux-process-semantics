(** * LinuxProcessSem.Checks.SpuriousCfg — the forced-only filter, on cases chosen by hand

    Not part of the trusted specification: this file is QA on
    [Run.SpuriousCfg], [Run.spurious_refusal_cfg] and [Run.sstep_cfg],
    written to be READ, in the manner of [Checks.Examples] and under the
    four admission reasons its header lists.  Every case here is one a
    single real run cannot show, and for one reason above all: a fold
    of the checker sees what the kernel DID, and the filter is
    a statement about what the kernel COULD HAVE DONE instead — whether
    a refusal was avoidable — which is not an observation of any one
    run (reason 4, and reason 3 where a fixture's budget or ledger is
    named).

    ** What is pinned, family by family

    - fs, never forced: [getcwd]'s -ENOMEM is spurious under forced-only
      and kept under may-fail; its -ERANGE, the answer the state
      determines, is kept under both.  At the STEP level this is the
      subset lemma's negative twin — [Run.sstep] admits the -ENOMEM
      step and [Run.sstep_cfg Run.forced_only_cfg] refuses it — with
      the -ERANGE step admitted on both sides as the positive twin.
    - cred, keyed on state: [setsid]'s -EPERM is spurious before a
      success and FORCED after one, because [Kernel.Sys.setsid_spec]
      answers it deterministically once [State.m_setsid_succeeded] is
      set.
    - alloc, keyed on the budget: an anonymous [mmap] within budget has
      its -ENOMEM removed; one beyond the budget keeps it, because the
      grant's [choose] has no witness there.  And an -ENOMEM the ARGUMENT
      gate determines — the overflowing MAP_FIXED length of
      [Checks.Cases.Mm.Mmap.mmap_fixed_overflowing_len_is_enomem] — is
      kept although it is in [Mmap.mmap_errnos], which is the exactness
      argument of [Run.v]'s spurious-failure header made concrete: the
      filter never removes an answer the state determines, whatever the
      list says.
    - the table itself: sorted, and every number in it dispatches.
    - run level: the exit-0 image must-exits under forced-only exactly
      as it does under may-fail, and the undecodable image refutes the
      predicate under forced-only as it does under may-fail — the two
      witnesses [MustExit]'s header points at, at the other reading. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   PART 1 — the table
   ========================================================================= *)

Fixpoint strictly_ascending (l : list Z) : bool :=
  match l with
  | a :: ((b :: _) as r) => Z.ltb a b && strictly_ascending r
  | _ => true
  end.

(** Sorted by number, like [Sys.SyscallTable.spec_table], and so with no
    number twice — the property [Run.lookup_injected]'s first-match
    lookup needs to be unambiguous. *)
Example injected_table_sorted :
  strictly_ascending (map ia_no injected_table) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every injecting arm names a syscall the dispatcher answers: a number
    here with no arm in [Sys.SyscallTable.spec_table] would be a filter
    on nothing. *)
Example injected_table_dispatches :
  forallb (fun a => existsb (Z.eqb (ia_no a)) (arm_numbers spec_table))
          injected_table = true.
Proof. vm_compute. reflexivity. Qed.

(** An effect that answers errno [e] and does nothing else. *)
Definition errno_eff (e : Z) : SyscallEffect := mkEffect (errno_ret e) [] [].

(** The model every check below starts from: the demo process with an
    empty file system and end of input. *)
Definition m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(* =========================================================================
   PART 2 — which families a configuration turns off
   ========================================================================= *)

(** A machine state at a [getcwd] ecall: syscall number 17 pending, every
    register 0 — so [size] is 0, inside the band [DPath.getcwd_spec]
    answers — and no memory at all, which that spec never reads. *)
Definition getcwd_ms : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 0x100;
  ms_svc_pending := Some (Z_to_bv 64 17);
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None; ms_rom := fun _ => None; ms_ro := [] |}.

Definition getcwd_i : SyscallInput := sys_input [] getcwd_ms (Z_to_bv 64 17).

Example getcwd_off_under_forced_only :
  injected_family_off forced_only_cfg getcwd_i = true.
Proof. vm_compute. reflexivity. Qed.

Example getcwd_on_under_may_fail :
  injected_family_off may_fail_cfg getcwd_i = false.
Proof. vm_compute. reflexivity. Qed.

(** The one-switch form [alloc_only_cfg] touches the allocation family
    and nothing else. *)
Example getcwd_on_under_alloc_only :
  injected_family_off (alloc_only_cfg false) getcwd_i = false.
Proof. vm_compute. reflexivity. Qed.

Example mmap_off_under_alloc_only :
  injected_family_off (alloc_only_cfg false) (mmap_in 4096) = true.
Proof. vm_compute. reflexivity. Qed.

(** A syscall with no injecting arm belongs to no family, whatever the
    configuration: [exit] is never filtered. *)
Example exit_has_no_family : forall cfg,
  injected_family_off cfg
    (mkInput 93 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None)) = false.
Proof. intros cfg. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 3 — fs: getcwd, never forced
   ========================================================================= *)

Lemma getcwd_dispatch : forall m o,
  syscall_spec getcwd_i m o <-> getcwd_spec (in_arg getcwd_i 1) getcwd_i m o.
Proof.
  intros m o. unfold syscall_spec, dispatch.
  assert (E : bv_unsigned (in_sysno getcwd_i) = 17%Z) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

Lemma getcwd_size_in_band : (1 <? bv_unsigned (in_arg getcwd_i 1))%Z = false.
Proof. vm_compute. reflexivity. Qed.

(** Every answer [getcwd] admits here: -ERANGE, or one of the injected
    three; the model is untouched and nothing is emitted. *)
Lemma getcwd_admits : forall m e,
  In e (ERANGE :: getcwd_errnos) ->
  syscall_spec getcwd_i m (Ok (errno_eff e) m []).
Proof.
  intros m e Hin. apply getcwd_dispatch. unfold getcwd_spec.
  rewrite getcwd_size_in_band.
  destruct Hin as [<- | Hin].
  - apply alt_r. reflexivity.
  - apply alt_l. unfold errno_from, bind, choose.
    exists e, m, [], [].
    split; [exists e; split; [exact Hin | reflexivity] |].
    split; reflexivity.
Qed.

Lemma getcwd_only : forall m eff m' evs,
  syscall_spec getcwd_i m (Ok eff m' evs) ->
  m' = m /\ evs = [] /\ exists e, In e (ERANGE :: getcwd_errnos) /\ eff = errno_eff e.
Proof.
  intros m eff m' evs H. apply (proj1 (getcwd_dispatch m _)) in H. unfold getcwd_spec in H.
  rewrite getcwd_size_in_band in H.
  unfold alt, errno_from, bind, choose, err_ret, ret_only, pure in H.
  sys_destruct;
    (split; [reflexivity | split; [reflexivity |]]);
    first [ match goal with
            | [ Hin : In ?e getcwd_errnos |- _ ] =>
                exists e; split; [right; exact Hin | reflexivity]
            end
          | exists ERANGE; split; [left; reflexivity | reflexivity] ].
Qed.

(** The -ENOMEM is spurious under forced-only: -ERANGE was available. *)
Example getcwd_enomem_spurious_under_forced_only :
  spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ENOMEM).
Proof.
  split; [exact getcwd_off_under_forced_only |].
  split; [vm_compute; reflexivity |].
  exists (errno_eff ERANGE), m0, []. split.
  - apply getcwd_admits. left. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** ... and kept under may-fail, and under a configuration that turns
    only the allocation family off. *)
Example getcwd_enomem_kept_under_may_fail :
  ~ spurious_refusal_cfg may_fail_cfg getcwd_i m0 (errno_eff ENOMEM).
Proof. apply spurious_refusal_may_fail. Qed.

Example getcwd_enomem_kept_under_alloc_only :
  ~ spurious_refusal_cfg (alloc_only_cfg false) getcwd_i m0 (errno_eff ENOMEM).
Proof. apply spurious_refusal_family_on. exact getcwd_on_under_alloc_only. Qed.

(** The answer the state determines is never spurious. *)
Example getcwd_erange_kept_under_forced_only :
  ~ spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ERANGE).
Proof. apply spurious_refusal_not_refusal. vm_compute. reflexivity. Qed.

(** The filter's question is answered here, in the affirmative. *)
Example getcwd_decided :
  refusal_decided forced_only_cfg getcwd_i m0.
Proof.
  intros _. left. exists (errno_eff ERANGE), m0, [].
  split; [apply getcwd_admits; left; reflexivity | vm_compute; reflexivity].
Qed.

(* -------------------------------------------------------------------------
   The step level: the subset lemma's negative twin
   ------------------------------------------------------------------------- *)

Lemma getcwd_step_from : forall e,
  In e (ERANGE :: getcwd_errnos) ->
  sstep [] (mkCfg getcwd_ms m0) []
    (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff e))) m0)).
Proof.
  intros e Hin.
  apply (sstep_syscall [] getcwd_ms m0 (Z_to_bv 64 17) (errno_eff e) m0 m0 []).
  - reflexivity.
  - reflexivity.
  - apply getcwd_admits. exact Hin.
  - reflexivity.
  - apply materialize_model_accesses_no_lazy. reflexivity.
Qed.

(** [Run.sstep] admits the -ENOMEM step. *)
Example getcwd_enomem_step_admitted :
  sstep [] (mkCfg getcwd_ms m0) []
    (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))) m0)).
Proof. apply getcwd_step_from. right. left. reflexivity. Qed.

(** ... [Run.sstep_cfg Run.forced_only_cfg] refuses it.  Any step into
    that configuration is a syscall step whose outcome set a0 to
    -ENOMEM, and [getcwd_only] says such an outcome is one of the
    injected three — spurious, since -ERANGE was available — while the
    one non-spurious outcome, -ERANGE, lands in a different
    configuration. *)
Example getcwd_enomem_step_refused :
  ~ sstep_cfg [] forced_only_cfg (mkCfg getcwd_ms m0) []
      (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM))) m0)).
Proof.
  intros H.
  (* the exit step is refuted by [inversion] itself: it emits an exit
     event and this step emits nothing *)
  inversion H; subst;
    repeat match goal with
           | [ Hsvc : ms_svc_pending getcwd_ms = _ |- _ ] =>
               change (ms_svc_pending getcwd_ms) with (Some (Z_to_bv 64 17)) in Hsvc
           end.
  - (* an instruction step: a syscall is pending here *)
    discriminate.
  - (* a syscall step *)
    match goal with
    | [ Hsvc : Some _ = Some ?x8 |- _ ] => injection Hsvc as Hx8; subst x8
    end.
    match goal with
    | [ Hspec : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        destruct (getcwd_only _ _ _ _ Hspec) as (Hm & Hevs & e & Hin & Heff); subst
    end.
    destruct Hin as [<- | Hin].
    + (* -ERANGE lands elsewhere: a0 differs *)
      match goal with
      | [ Hret : eff_ret _ = errno_ret _ |- _ ] =>
          apply (f_equal bv_unsigned) in Hret; vm_compute in Hret; discriminate Hret
      end.
    + (* an injected errno: spurious, which the step's premise refutes *)
      match goal with
      | [ Hns : ~ spurious_refusal_cfg _ _ _ _ |- _ ] => apply Hns
      end.
      split; [exact getcwd_off_under_forced_only |].
      split.
      * destruct Hin as [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
      * exists (errno_eff ERANGE), m0, []. split.
        { apply getcwd_admits. left. reflexivity. }
        { vm_compute. reflexivity. }
Qed.

(** The positive twin: the filtered relation still steps here, on the
    answer the state determines. *)
Example getcwd_erange_step_admitted_under_forced_only :
  sstep_cfg [] forced_only_cfg (mkCfg getcwd_ms m0) []
    (SNext (mkCfg (advance_past_svc (apply_effect getcwd_ms (errno_eff ERANGE))) m0)).
Proof.
  apply (sstep_cfg_syscall [] forced_only_cfg getcwd_ms m0 (Z_to_bv 64 17)
           (errno_eff ERANGE) m0 m0 []).
  - reflexivity.
  - reflexivity.
  - apply getcwd_admits. left. reflexivity.
  - exact getcwd_erange_kept_under_forced_only.
  - reflexivity.
  - apply materialize_model_accesses_no_lazy. reflexivity.
Qed.

(* =========================================================================
   PART 4 — cred: setsid, forced by state
   ========================================================================= *)

Definition setsid_i : SyscallInput :=
  mkInput 157 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

Lemma setsid_dispatch : forall m o,
  syscall_spec setsid_i m o <-> setsid_spec setsid_i m o.
Proof.
  intros m o. unfold syscall_spec, dispatch.
  assert (E : bv_unsigned (in_sysno setsid_i) = 157%Z) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

(** Before any success, -EPERM is spurious: the session can be made. *)
Example setsid_eperm_spurious_before_success :
  spurious_refusal_cfg forced_only_cfg setsid_i m0 (errno_eff EPERM).
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exists (mkEffect 1 [] []), (with_setsid_succeeded (with_tid 1 m0)), [].
  split; [| vm_compute; reflexivity].
  apply check_syscall_sound_ok. check_eq.
Qed.

(** After one, -EPERM is the only answer and is kept: the state forces
    it. *)
Example setsid_eperm_forced_after_success :
  ~ spurious_refusal_cfg forced_only_cfg setsid_i (with_setsid_succeeded m0) (errno_eff EPERM).
Proof.
  intros (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  apply (proj1 (setsid_dispatch _ _)) in Hspec.
  unfold setsid_spec, bind, get_model in Hspec. sys_destruct.
  assert (Hs : m_setsid_succeeded (with_setsid_succeeded m0) = true) by reflexivity.
  rewrite Hs in *.
  unfold err_ret, ret_only, pure in *. sys_destruct.
  vm_compute in Hnr. discriminate Hnr.
Qed.

(* =========================================================================
   PART 5 — alloc: mmap, forced by the budget; and the argument gate
   ========================================================================= *)

Lemma mmap_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec i m o
  <-> mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
                (in_arg i 5) i m o.
Proof.
  intros i m o E. unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

(** Within budget the -ENOMEM is spurious: the grant
    [Checks.Cases.Mm.Mmap.mmap_within_budget_grants] admits is the
    non-refusal answer. *)
Example mmap_enomem_spurious_within_budget :
  spurious_refusal_cfg forced_only_cfg (mmap_in 4096) tight_model (errno_eff ENOMEM).
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exists (mkEffect 131072 [] [(131072, 4096)]),
    (with_vmmaps (mkVmMaps [] [(131072, 4096); (65536, 4096)] 0 0 8192) tight_model), [].
  split; [| vm_compute; reflexivity].
  apply check_syscall_sound_ok. exact mmap_within_budget_grants.
Qed.

(** Beyond it the -ENOMEM is FORCED and kept: the grant's [choose]
    carries the budget test in its predicate, and that test is false, so
    the errno arm is the only one with an inhabitant. *)
Example mmap_enomem_forced_beyond_budget :
  ~ spurious_refusal_cfg forced_only_cfg (mmap_in 8192) tight_model (errno_eff ENOMEM).
Proof.
  intros (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  apply (proj1 (mmap_dispatch (mmap_in 8192) _ _ ltac:(vm_compute; reflexivity))) in Hspec.
  unfold mmap_spec in Hspec.
  revert Hspec.
  destruct (negb (mmap_off_aligned_b (in_arg (mmap_in 8192) 5))) eqn:E0a;
    [vm_compute in E0a; discriminate E0a |].
  destruct (negb (mmap_anon_b (in_arg (mmap_in 8192) 3))) eqn:E0b;
    [vm_compute in E0b; discriminate E0b |].
  destruct (w_is0 (in_arg (mmap_in 8192) 1)) eqn:E1; [vm_compute in E1; discriminate E1 |].
  destruct (mmap_modeled_b (in_arg (mmap_in 8192) 2) (in_arg (mmap_in 8192) 3)
              (in_arg (mmap_in 8192) 5)) eqn:E2;
    [| vm_compute in E2; discriminate E2].
  intros Hspec.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify in Hspec.
  cbv beta zeta in Hspec.
  sys_destruct.
  - (* the errno arm: a refusal, which [Hnr] denies *)
    match goal with
    | [ Hin : In ?e mmap_errnos |- _ ] =>
        destruct Hin as [<- | []]
    end.
    vm_compute in Hnr. discriminate Hnr.
  - (* the grant: its budget conjunct is false here *)
    match goal with
    | [ Hb : mmap_noreserve_backed_ok _ _ _ = true |- _ ] =>
        vm_compute in Hb; discriminate Hb
    end.
Qed.

(** An -ENOMEM the ARGUMENT GATE determines is kept although -ENOMEM is
    the one member of [Mmap.mmap_errnos]: at this input the gate's
    [err_ret ENOMEM] is the whole spec, so no non-refusal outcome
    exists and the filter has nothing to remove.  This is the exactness
    claim of [Run.v]'s spurious-failure header at the one place a
    list-driven filter would have got it wrong. *)
Definition mmap_overflow_i : SyscallInput :=
  mkInput 222 [4097; 18446744073709551615; 0; 50; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).

Example mmap_gate_enomem_kept_under_forced_only :
  ~ spurious_refusal_cfg forced_only_cfg mmap_overflow_i noaccess_base (errno_eff ENOMEM).
Proof.
  intros (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  apply (proj1 (mmap_dispatch mmap_overflow_i _ _ ltac:(vm_compute; reflexivity))) in Hspec.
  unfold mmap_spec in Hspec.
  revert Hspec.
  destruct (negb (mmap_off_aligned_b (in_arg mmap_overflow_i 5))) eqn:E0a;
    [vm_compute in E0a; discriminate E0a |].
  destruct (negb (mmap_anon_b (in_arg mmap_overflow_i 3))) eqn:E0b;
    [vm_compute in E0b; discriminate E0b |].
  destruct (w_is0 (in_arg mmap_overflow_i 1)) eqn:E1; [vm_compute in E1; discriminate E1 |].
  destruct (mmap_modeled_b (in_arg mmap_overflow_i 2) (in_arg mmap_overflow_i 3)
              (in_arg mmap_overflow_i 5)) eqn:E2;
    [vm_compute in E2; discriminate E2 |].
  destruct (mmap_noaccess_b (in_arg mmap_overflow_i 2) (in_arg mmap_overflow_i 3)
              (in_arg mmap_overflow_i 5)) eqn:E3;
    [vm_compute in E3; discriminate E3 |].
  destruct (mmap_fixed_noaccess_b (in_arg mmap_overflow_i 2) (in_arg mmap_overflow_i 3)
              (in_arg mmap_overflow_i 5)) eqn:E4;
    [| vm_compute in E4; discriminate E4].
  cbv zeta.
  destruct (two_pow_64 <=? bv_unsigned (in_arg mmap_overflow_i 0)
              + page_round_up_Z (bv_unsigned (in_arg mmap_overflow_i 1)))%Z eqn:E5;
    [| vm_compute in E5; discriminate E5].
  intros Hspec.
  unfold err_ret, ret_only, pure in Hspec. sys_destruct.
  vm_compute in Hnr. discriminate Hnr.
Qed.

(* =========================================================================
   PART 6 — run level: the two witnesses, at the other reading
   ========================================================================= *)

(** [Checks.Examples.exits_c] is sound for the filtered predicate too,
    under every configuration — the same proof as
    [Checks.Examples.exits_c_must_exit_at], over [Run.sstep_cfg]: the
    instruction steps and the exit step carry no filter premise, and the
    two syscall shapes the filter does touch are ruled out at an exit
    ecall by the exit-dispatch lemmas exactly as before. *)
Lemma exits_c_must_exit_at_cfg : forall cfg segs code fuel ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  exits_c segs code fuel ms = true ->
  must_exit_at_cfg cfg segs code (mkCfg ms model).
Proof.
  intros cfg segs code fuel. induction fuel as [|fuel IH]; intros ms model Hh Hlazy Hc;
    [discriminate|].
  cbn [exits_c] in Hc.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - (* the terminating ecall *)
    apply andb_true_iff in Hc as [Hx8 Hcode].
    apply bv_eqb_eq in Hcode.
    assert (Hno : exit_sysno (in_sysno (sys_input segs ms x8))).
    { cbn [in_sysno sys_input].
      apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
        [left|right]; exact H. }
    assert (Harg : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0) by reflexivity.
    set (m' := with_halted (bv_and (in_arg (sys_input segs ms x8) 0)
                                   (Z_to_bv 64 255)) model).
    apply must_exit_at_cfg_running.
    + cbn [cfg_model]. exact Hh.
    + exists ([] ++ [ExitEv (bv_and (in_arg (sys_input segs ms x8) 0)
                                    (Z_to_bv 64 255)) (m_fs m')]),
        (SNext (mkCfg ms m')).
      eapply sstep_cfg_exit; [exact Hh | exact Hsvc | | | ].
      * subst m'. exact (exit_dispatch_admits _ model Hno).
      * subst m'. reflexivity.
      * subst m'. apply m_killed_with_halted.
    + intros evs Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * match goal with
        | [ H : syscall_spec _ _ Unmodeled |- _ ] =>
            exact (exit_dispatch_modeled _ _ Hno H)
        end.
    + intros evs c' Hss. inversion Hss; subst; try congruence; unify_svc x8.
      * match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        congruence.
      * match goal with
        | [ H : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
            pose proof (exit_dispatch_halts _ _ _ _ _ Hno H) as Hhalts
        end.
        apply must_exit_at_cfg_halted; cbn [cfg_model].
        -- rewrite Hhalts, Harg. reflexivity.
        -- match goal with
           | [ H : m_killed ?m' = None |- m_killed ?m' = None ] => exact H
           end.
      * (* the kill transition: an exit's post-model is not a killed one *)
        exfalso.
        match goal with
        | [ H : syscall_spec _ _ (Ok _ ?m' _), Hk : m_killed ?m' = Some _ |- _ ] =>
            rewrite (exit_dispatch_not_killed _ _ _ _ _ Hno H) in Hk;
            discriminate
        end.
  - (* an ordinary instruction *)
    destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
    { rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity. }
    apply must_exit_at_cfg_running.
    + cbn [cfg_model]. exact Hh.
    + exists [], (SNext (mkCfg ms' model)).
      eapply sstep_cfg_instr; eassumption.
    + intros evs Hss. inversion Hss; subst; congruence.
    + intros evs c' Hss. inversion Hss; subst; try congruence.
      match goal with
      | [ H : mi_account_step _ _ _ = MachineOk (?a, ?b) |- _ ] =>
          rewrite Hacc in H; injection H as -> ->
      end.
      apply IH; assumption.
Qed.

(** The exit-0 image must-exits under forced-only: the positive witness
    [MustExit]'s header points at, at the pinned reading. *)
Example exit0_image_must_exit_zero_under_forced_only :
  must_exit_with_scfg forced_only_cfg verdict_accept exit0_image demo_limit demo_entry
    (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  cbn [must_exit_with_scfg exit0_image demo_entry]. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** ... and the undecodable image refutes it there too, at every code:
    the fetch that leaves the modeled surface is an instruction step, and
    the filter touches no instruction step. *)
Example undecodable_image_refutes_must_exit_under_forced_only :
  ~ must_exit_with_scfg forced_only_cfg verdict_accept undecodable_image demo_limit
      (mkEntry (Z_to_bv 64 65536) (Z_to_bv 64 1048576)
         (Z_to_bv 64 mmap_base_max) demo_draw)
      (mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
                       default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48).
Proof.
  apply must_exit_with_scfg_refuted_by_error, run_scfg_unmodeled_errors.
  cbn [run_scfg bh_unmodeled undecodable_image]. unfold init_config.
  match goal with
  | |- reaches_unmodeled_cfg _ _ ?c => exists [], c
  end.
  split; [apply star_cfg_refl |].
  split; [reflexivity |]. left. split; [reflexivity |].
  cbn [cfg_ms cfg_model].
  match goal with
  | |- mi_account_step ?segs ?ms ?model = _ =>
      rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
  end.
  cbn [mkProcInput in_argv in_envp in_uid in_hwcap].
  rewrite undecodable_step_unmodeled. reflexivity.
Qed.
