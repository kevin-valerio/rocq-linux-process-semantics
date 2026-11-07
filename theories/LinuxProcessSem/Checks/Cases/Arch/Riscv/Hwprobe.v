(** Worked cases for the two-key RISC-V hardware probe. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.

Definition hwprobe_input_bytes : list byte :=
  word_le8 4 ++ repeat 0 8 ++ word_le8 5 ++ repeat 0 8.

Definition hwprobe_input : SyscallInput :=
  let mem := fun a =>
    if ((4096 <=? bv_unsigned a)%Z && (bv_unsigned a <? 4128)%Z)%bool
    then nth_error hwprobe_input_bytes (Z.to_nat (bv_unsigned a - 4096))
    else None in
  mkInput 258 [4096; 2; 0; 0; 0; 0] mem mem.

Definition hwprobe_model : Model :=
  with_hwprobe (Some (3, 2))
    (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] None None None).

Example hwprobe_scalar_rv64gc_result :
  check_syscall hwprobe_input
    (with_copyins (hwprobe_key_reads 4096)
      (mkEffect 0 [(4096, hwprobe_bytes 3 2)] [])) hwprobe_model
  = CheckOk hwprobe_model [].
Proof. vm_compute. reflexivity. Qed.

Example hwprobe_optional_extension_outside_scope :
  check_syscall hwprobe_input
    (with_copyins (hwprobe_key_reads 4096)
      (mkEffect 0 [(4096, hwprobe_bytes 4 2)] []))
    (with_hwprobe (Some (4, 2))
      (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] None None None))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.
