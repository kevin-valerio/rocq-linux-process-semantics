(* Written by the OSS-Fuzz proof collaborators. *)
(** * SymStepR — per-instruction step lemmas over a machine state with an
      ARBITRARY LR/SC reservation ([mkstR]), including the RV64A
      instructions [lr.w/d], [sc.w/d] (success path) and the AMOs.

    Written for the reservation-tracking extension of the
    reflective symbolic executor [AxSymExec3] (soundness in [AxSymExec3Sound]).

    [PropExec.mkst regs pc mem rom] PINS [ms_resv := None]; it is, by
    definition, CONVERTIBLE with [mkstR regs pc mem rom None] (both unfold
    to the same record), so every lemma below specialises to the
    [mkst]-lemma of the same name in [PropExec]/[SeqExec].
    Nothing here changes [PropExec].

    Reservation behaviour (transcribed from [Sem.exec], proved by
    computation through [RiscvSemantics.step], never assumed):
      - integer ALU / branches / jumps / fences / loads: reservation unchanged;
      - [Store]: [resv_inval_w rv a] — a store to EXACTLY the reserved
        address kills the reservation ([Sem.inval_resv]);
      - [Lr]: reservation := [Some a];
      - [Sc] with reservation [Some a] on its own address: store, [rd := 0],
        reservation := [None] (the failing [Sc] is not covered: the
        symbolic executor never needs it);
      - [Amo]: load, store [amo_val], [rd := old], reservation as for a store.
    All three atomics FAULT on a misaligned address ([Sem.amo_aligned]);
    the lemmas take the alignment as a hypothesis. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Common Require Import PropExec CatExec SeqExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(** The state shape: [mkst] with the reservation exposed. *)
Definition mkstR (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := rv; ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem; ms_rom := rom; ms_ro := [] |}.

Lemma mkstR_None : forall regs pc mem rom, mkstR regs pc mem rom None = mkst regs pc mem rom.
Proof. reflexivity. Qed.

Lemma mkstR_svc : forall regs pc mem rom rv, ms_svc_pending (mkstR regs pc mem rom rv) = None.
Proof. reflexivity. Qed.

Lemma b_npc_size : forall (p : word) (isz : Z),
  p + Z_to_bv 64 isz = v_addi p isz.
Proof.
  intros. apply bv_eq. unfold v_addi.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

(** What a store / AMO to address [a] does to the reservation. *)
Definition resv_inval_w (rv : option word) (a : word) : option word :=
  match rv with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else rv
  | None => None
  end.

(** The value a load writes back, per width/sign, as a function of the bytes read. *)
Definition load_result (sz : msize) (sx : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs))
           else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

Definition eff_sx (sz : msize) (sx : bool) : bool :=
  match sz with SZ8 => false | _ => sx end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(** Atomic widths as load/store widths. *)
Definition amo_msize (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition amo_nbytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.

(** The bytes an AMO writes: [amo_val] at the operand width. *)
Definition amo_store_bytes (op : amoop) (wd : awidth) (bs : list byte) (src : word) : list byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
  | AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))
  end.

Ltac stepR_pipeline Hfetch Hecall Hdecode :=
  unfold mkstR;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* ================================================================= *)
(** ** Integer instructions: the reservation passes through            *)
(* ================================================================= *)

Lemma stepR_opimm_gen : forall segs regs pc mem rom rv w op rd rs (imm : bv 12) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs imm isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_shiftimm_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 6) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_op_gen : forall segs regs pc mem rom rv w op rd rs1 rs2 {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_opimm32_gen : forall segs regs pc mem rom rv w rd rs (imm : bv 12) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs imm isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_shiftimm32_gen : forall segs regs pc mem rom rv w op rd rs (sh : bv 5) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs sh isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_op32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2 {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_mul_gen : forall segs regs pc mem rom rv w op rd rs1 rs2 {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_mul32_gen : forall segs regs pc mem rom rv w op rd rs1 rs2 {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs
                    else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w op rd rs1 rs2 isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size; reflexivity.
Qed.

Lemma stepR_lui : forall segs regs pc mem rom rv w rd (imm : bv 20) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size, ?b_lui; reflexivity.
Qed.

Lemma stepR_auipc : forall segs regs pc mem rom rv w rd (imm : bv 20) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size, ?b_auipc; reflexivity.
Qed.

Lemma stepR_jal_link : forall segs regs pc mem rom rv w rd (imm : bv 21) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc isz))
                   (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd imm isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. unfold regupd.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size, ?b_addsext;
    reflexivity.
Qed.

Lemma stepR_jalr : forall segs regs pc mem rom rv w rd rs1 (imm : bv 12) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc isz))
                   (v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w rd rs1 imm isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd, v_jalr.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc_size, ?b_jalr; reflexivity.
Qed.

Lemma stepR_branch_tk_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, isz) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (btgt pc (bv_signed imm)) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm isz Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma stepR_branch_ft_gen : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, isz) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w c rs1 rs2 imm isz Hfetch Hecall Hdecode Hc.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc_size; reflexivity.
Qed.

Lemma stepR_fence : forall segs regs pc mem rom rv w a b c d e {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c d e isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc_size. reflexivity.
Qed.

Lemma stepR_fencei : forall segs regs pc mem rom rv w a b c {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI a b c, isz) ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w a b c isz Hfetch Hecall Hdecode.
  stepR_pipeline Hfetch Hecall Hdecode. rewrite b_npc_size. reflexivity.
Qed.

(* ================================================================= *)
(** ** Loads and stores                                                 *)
(* ================================================================= *)

Lemma stepR_load : forall segs regs pc mem rom rv w sz sx rd rs (imm : bv 12) bs {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, isz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs))
                   (v_addi pc isz) mem rom rv).
Proof.
  intros segs regs pc mem rom rv w sz sx rd rs imm bs isz Hfetch Hecall Hdecode Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  destruct sz; cbn [msize_bytes] in Hread; cbv beta iota delta [load_val];
    rewrite ov_rdn, b_addsext, Hread; cbv beta iota; rewrite b_npc_size;
    destruct sx; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(** Store of any width, value exposed, reservation invalidated on an
    exact address match. *)
Lemma stepR_store : forall segs regs pc mem rom rv w sz (rs1 rs2 : reg) (imm : bv 12) {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, isz) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR regs (v_addi pc isz)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom
    (resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))).
Proof.
  intros segs regs pc mem rom rv w sz rs1 rs2 imm isz Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  stepR_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite !b_addsext.
  destruct sz; cbn [msize_bytes] in Hok |- *; cbv beta iota delta [store_val];
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?Hsb, ?store_bytes_low16, ?store_bytes_low32, b_npc_size;
    (destruct rv as [r|]; cbv beta iota; [|reflexivity]);
    unfold resv_inval_w;
    match goal with |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y); cbv beta iota; reflexivity end.
Qed.

(* ================================================================= *)
(** ** A extension                                                      *)
(* ================================================================= *)

(** LR: load (like [lw]/[ld]) and reserve the address. *)
Lemma stepR_lr : forall segs regs pc mem rom rv w wd aq rl rd rs bs {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs, isz) ->
  (bv_unsigned (getr regs rs) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc isz) mem rom (Some (getr regs rs))).
Proof.
  intros segs regs pc mem rom rv w wd aq rl rd rs bs isz Hfetch Hecall Hdecode Hal Hread.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite b_npc_size; unfold regupd;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(** SC, success path: the reservation is on the SC's own address. *)
Lemma stepR_sc_ok : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, isz) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom (Some r)) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc isz)
                   (wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom None).
Proof.
  intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r isz Hfetch Hecall Hdecode Hal Hr Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    subst r; rewrite Z.eqb_refl; cbv beta iota;
    cbn [amo_nbytes] in Hok |- *; rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, ?store_bytes_low32, b_npc_size;
    unfold regupd, word_to_le_bytes;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(** AMO: load the old value, store [amo_val op old src], [rd := old]
    (sign-extended for .w); reservation invalidated like a store. *)
Lemma stepR_amo : forall segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs {isz : Z},
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op wd aq rl rd rs1 rs2, isz) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  rdn segs mem (getr regs rs1) (amo_nbytes wd) = Some bs ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true ->
  RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
  MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
                   (v_addi pc isz)
                   (wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
                   rom (resv_inval_w rv (getr regs rs1))).
Proof.
  intros segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs isz Hfetch Hecall Hdecode Hal Hread Hok.
  stepR_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  unfold amo_bytes in Hal.
  destruct wd; rewrite Hal; change (negb (0 =? 0)%Z) with false; cbv beta iota;
    cbn [amo_nbytes] in Hread, Hok |- *; rewrite ov_rdn, Hread; cbv beta iota;
    rewrite Hok; cbv beta iota;
    rewrite write_to_mem_wbytes, b_npc_size; unfold regupd, amo_store_bytes;
    (destruct rv as [r|]; cbv beta iota);
    unfold resv_inval_w;
    try match goal with |- context [Z.eqb (bv_unsigned r) ?y] =>
          destruct (Z.eqb (bv_unsigned r) y); cbv beta iota end;
    destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
