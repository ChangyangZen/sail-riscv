import LeanCV32E40PRV32IMC.Flow
import LeanCV32E40PRV32IMC.Mapping
import LeanCV32E40PRV32IMC.HexBits
import LeanCV32E40PRV32IMC.HexBitsSigned
import LeanCV32E40PRV32IMC.Prelude
import LeanCV32E40PRV32IMC.Errors
import LeanCV32E40PRV32IMC.Xlen
import LeanCV32E40PRV32IMC.Flen
import LeanCV32E40PRV32IMC.Extensions
import LeanCV32E40PRV32IMC.TypesExt

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

noncomputable section

namespace LeanCV32E40PRV32IMC.Functions

open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open uop
open sopw
open sop
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extension
open exception
open ctl_result
open csrop
open cregidx
open cfregidx
open bop
open barrier_kind
open agtype
open WaitReason
open TrapVectorMode
open Step
open Software_Check_Code
open SWCheckCodes
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open ISA_Format
open HartState
open FetchResult
open Ext_DataAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def pagesize_bits := 12

def base_E_enabled := false

def regidx_bit_width := 5

def regidx_bits (app_0 : regidx) : (BitVec (if ( false  : Bool) then 4 else 5)) :=
  let .Regidx b := app_0
  b

def creg2reg_idx (app_0 : cregidx) : regidx :=
  let .Cregidx i := app_0
  (Regidx (zero_extend (m := 5) (1#1 ++ i)))

def zreg : regidx := (Regidx (zero_extend (m := 5) 0b00#2))

def ra : regidx := (Regidx (zero_extend (m := 5) 0b01#2))

def sp : regidx := (Regidx (zero_extend (m := 5) 0b10#2))

def undefined_Architecture (_ : Unit) : SailM Architecture := do
  (internal_pick [RV32, RV64, RV128])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Architecture_of_num (arg_ : Nat) : Architecture :=
  match arg_ with
  | 0 => RV32
  | 1 => RV64
  | _ => RV128

def num_of_Architecture (arg_ : Architecture) : Int :=
  match arg_ with
  | RV32 => 0
  | RV64 => 1
  | RV128 => 2

def architecture_bits_forwards (arg_ : Architecture) : (BitVec 2) :=
  match arg_ with
  | RV32 => 0b01#2
  | RV64 => 0b10#2
  | RV128 => 0b11#2

def architecture_bits_backwards (arg_ : (BitVec 2)) : SailM Architecture := do
  match arg_ with
  | 0b01 => (pure RV32)
  | 0b10 => (pure RV64)
  | 0b11 => (pure RV128)
  | _ => (internal_error "model/core/types.sail" 61 "architecture(0b00) is invalid")

def architecture_bits_forwards_matches (arg_ : Architecture) : Bool :=
  match arg_ with
  | RV32 => true
  | RV64 => true
  | RV128 => true

def architecture_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | 0b00 => true
  | _ => false

def undefined_Privilege (_ : Unit) : SailM Privilege := do
  (internal_pick [User, VirtualUser, Supervisor, VirtualSupervisor, Machine])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Privilege_of_num (arg_ : Nat) : Privilege :=
  match arg_ with
  | 0 => User
  | 1 => VirtualUser
  | 2 => Supervisor
  | 3 => VirtualSupervisor
  | _ => Machine

def num_of_Privilege (arg_ : Privilege) : Int :=
  match arg_ with
  | User => 0
  | VirtualUser => 1
  | Supervisor => 2
  | VirtualSupervisor => 3
  | Machine => 4

def privLevel_bits_forwards (arg_ : ((BitVec 2) × (BitVec 1))) : SailM Privilege := do
  match arg_ with
  | (0b00, 0) => (pure User)
  | (0b00, 1) => (pure VirtualUser)
  | (0b01, 0) => (pure Supervisor)
  | (0b01, 1) => (pure VirtualSupervisor)
  | (0b11, 0) => (pure Machine)
  | _ => (internal_error "model/core/types.sail" 78 "Invalid privilege level or virtual mode")

def privLevel_bits_backwards (arg_ : Privilege) : ((BitVec 2) × (BitVec 1)) :=
  match arg_ with
  | User => (0b00#2, 0#1)
  | VirtualUser => (0b00#2, 1#1)
  | Supervisor => (0b01#2, 0#1)
  | VirtualSupervisor => (0b01#2, 1#1)
  | Machine => (0b11#2, 0#1)

def privLevel_bits_forwards_matches (arg_ : ((BitVec 2) × (BitVec 1))) : Bool :=
  match arg_ with
  | (0b00, 0) => true
  | (0b00, 1) => true
  | (0b01, 0) => true
  | (0b01, 1) => true
  | (0b11, 0) => true
  | _ => true

def privLevel_bits_backwards_matches (arg_ : Privilege) : Bool :=
  match arg_ with
  | User => true
  | VirtualUser => true
  | Supervisor => true
  | VirtualSupervisor => true
  | Machine => true

def privLevel_to_bits (p : Privilege) : (BitVec 2) :=
  let (p, _) := (privLevel_bits_backwards p)
  p

def Mk_Misa (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_Misa_MXL (v : (BitVec 32)) (x : (BitVec (32 - 1 - (32 - 2) + 1))) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) (32 -i 2) x)

def Mk_Mstatus (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_Mstatus_SXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_Mstatus_UXL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _get_Misa_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_Misa_D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_Misa_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_Misa_M (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_Misa_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_Misa_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_Misa_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_Mstatus_FS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 14 13)

def _get_Mstatus_VS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 10 9)

def Mk_MEnvcfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MEnvcfg_CBCFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_MEnvcfg_CBIE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_MEnvcfg_CBZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_MEnvcfg_FIOM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_MEnvcfg_LPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_MEnvcfg_STCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_MEnvcfg_CBCFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MEnvcfg_CBIE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_MEnvcfg_CBZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_MEnvcfg_FIOM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MEnvcfg_LPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_MEnvcfg_STCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def sys_enable_writable_fiom : Bool := true

def Mk_Seccfg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_Seccfg_MLPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_Seccfg_SSEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_Seccfg_USEED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_Seccfg_MLPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_Seccfg_SSEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_Seccfg_USEED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def Mk_SEnvcfg (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_SEnvcfg_CBCFE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SEnvcfg_CBIE (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SEnvcfg_CBZE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SEnvcfg_FIOM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SEnvcfg_LPE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_SEnvcfg_CBCFE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SEnvcfg_CBIE (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SEnvcfg_CBZE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SEnvcfg_FIOM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SEnvcfg_LPE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


mutual
partial def currentlyEnabled (merge_var : extension) : SailM Bool := do
  match merge_var with
  | Ext_Zkt => (pure (hartSupports Ext_Zkt))
  | Ext_Zvkt => (pure (hartSupports Ext_Zvkt))
  | Ext_Zvkn => (pure (hartSupports Ext_Zvkn))
  | Ext_Zvknc => (pure (hartSupports Ext_Zvknc))
  | Ext_Zvkng => (pure (hartSupports Ext_Zvkng))
  | Ext_Zvks => (pure (hartSupports Ext_Zvks))
  | Ext_Zvksc => (pure (hartSupports Ext_Zvksc))
  | Ext_Zvksg => (pure (hartSupports Ext_Zvksg))
  | Ext_Sstc => (pure (hartSupports Ext_Sstc))
  | Ext_U =>
    (pure ((hartSupports Ext_U) && (((_get_Misa_U (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zicsr)))))
  | Ext_S =>
    (pure ((hartSupports Ext_S) && (((_get_Misa_S (← readReg misa)) == 1#1) && (← (currentlyEnabled
              Ext_Zicsr)))))
  | Ext_Svbare => (currentlyEnabled Ext_S)
  | Ext_Sv32 => (pure ((hartSupports Ext_Sv32) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv39 => (pure ((hartSupports Ext_Sv39) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv48 => (pure ((hartSupports Ext_Sv48) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv57 => (pure ((hartSupports Ext_Sv57) && (← (currentlyEnabled Ext_S))))
  | Ext_F =>
    (pure ((hartSupports Ext_F) && (((_get_Misa_F (← readReg misa)) == 1#1) && (((_get_Mstatus_FS
                (← readReg mstatus)) != 0b00#2) && (← (currentlyEnabled Ext_Zicsr))))))
  | Ext_D =>
    (pure ((hartSupports Ext_D) && (((_get_Misa_D (← readReg misa)) == 1#1) && (((_get_Mstatus_FS
                (← readReg mstatus)) != 0b00#2) && ((flen ≥b 64) && (← (currentlyEnabled
                  Ext_Zicsr)))))))
  | Ext_Zfinx => (pure ((hartSupports Ext_Zfinx) && (← (currentlyEnabled Ext_Zicsr))))
  | Ext_V =>
    (pure ((hartSupports Ext_V) && (((_get_Misa_V (← readReg misa)) == 1#1) && (((_get_Mstatus_VS
                (← readReg mstatus)) != 0b00#2) && (← (currentlyEnabled Ext_Zicsr))))))
  | Ext_Smcntrpmf => (pure ((hartSupports Ext_Smcntrpmf) && (← (currentlyEnabled Ext_Zicntr))))
  | Ext_Zicfilp =>
    (pure ((← (currentlyEnabled Ext_Zicsr)) && ((hartSupports Ext_Zicfilp) && (← (get_xLPE
              (← readReg cur_privilege))))))
  | Ext_Svnapot => (pure false)
  | Ext_Svpbmt => (pure false)
  | Ext_Svrsw60t59b => (pure ((hartSupports Ext_Svrsw60t59b) && (← (currentlyEnabled Ext_Sv39))))
  | Ext_C => (pure ((hartSupports Ext_C) && ((_get_Misa_C (← readReg misa)) == 1#1)))
  | Ext_Zca =>
    (pure ((hartSupports Ext_Zca) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | Ext_M => (pure ((hartSupports Ext_M) && ((_get_Misa_M (← readReg misa)) == 1#1)))
  | Ext_Zmmul => (pure ((hartSupports Ext_Zmmul) || (← (currentlyEnabled Ext_M))))
  | Ext_Zicsr => (pure (hartSupports Ext_Zicsr))
  | Ext_Zicntr => (pure ((hartSupports Ext_Zicntr) && (← (currentlyEnabled Ext_Zicsr))))
  | Ext_Zifencei => (pure (hartSupports Ext_Zifencei))
  | _ =>
    (do
      assert false "Pattern match failure at model/extensions/Zifenci/zifencei_insts.sail:14.0-14.75"
      throw Error.Exit)
partial def get_xLPE (p : Privilege) : SailM Bool := do
  match p with
  | Machine => (pure (bool_bits_backwards (_get_Seccfg_MLPE (← readReg mseccfg))))
  | Supervisor => (pure (bool_bits_backwards (_get_MEnvcfg_LPE (← readReg menvcfg))))
  | User =>
    (do
      if ((← (currentlyEnabled Ext_S)) : Bool)
      then (pure (bool_bits_backwards (_get_SEnvcfg_LPE (← readReg senvcfg))))
      else (pure (bool_bits_backwards (_get_MEnvcfg_LPE (← readReg menvcfg)))))
  | VirtualSupervisor =>
    (internal_error "model/extensions/cfi/zicfilp_regs.sail" 31 "Hypervisor extension not supported")
  | VirtualUser =>
    (internal_error "model/extensions/cfi/zicfilp_regs.sail" 32 "Hypervisor extension not supported")
end

def legalize_menvcfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_MEnvcfg v)
  (pure (_update_MEnvcfg_STCE
      (_update_MEnvcfg_CBIE
        (_update_MEnvcfg_CBCFE
          (_update_MEnvcfg_CBZE
            (_update_MEnvcfg_LPE
              (_update_MEnvcfg_FIOM o
                (if (sys_enable_writable_fiom : Bool)
                then (_get_MEnvcfg_FIOM v)
                else 0#1))
              (if ((hartSupports Ext_Zicfilp) : Bool)
              then (_get_MEnvcfg_LPE v)
              else 0#1))
            (← do
              if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
              then (pure (_get_MEnvcfg_CBZE v))
              else (pure 0#1)))
          (← do
            if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
            then (pure (_get_MEnvcfg_CBCFE v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
          then
            (if (((_get_MEnvcfg_CBIE v) != 0b10#2) : Bool)
            then (pure (_get_MEnvcfg_CBIE v))
            else (pure 0b00#2))
          else (pure 0b00#2)))
      (← do
        if ((← (currentlyEnabled Ext_Sstc)) : Bool)
        then (pure (_get_MEnvcfg_STCE v))
        else (pure 0#1))))

def legalize_mseccfg (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let sseed_read_only_zero ← do
    (pure ((false : Bool) || ((not (← (currentlyEnabled Ext_S))) || (not
            (← (currentlyEnabled Ext_Zkr))))))
  let useed_read_only_zero ← do
    (pure ((false : Bool) || ((not (← (currentlyEnabled Ext_U))) || (not
            (← (currentlyEnabled Ext_Zkr))))))
  let v := (Mk_Seccfg v)
  (pure (_update_Seccfg_USEED
      (_update_Seccfg_SSEED
        (_update_Seccfg_MLPE o
          (if ((hartSupports Ext_Zicfilp) : Bool)
          then (_get_Seccfg_MLPE v)
          else 0#1))
        (if (sseed_read_only_zero : Bool)
        then 0#1
        else (_get_Seccfg_SSEED v)))
      (if (useed_read_only_zero : Bool)
      then 0#1
      else (_get_Seccfg_USEED v))))

def legalize_senvcfg (o : (BitVec 32)) (v : (BitVec 32)) : SailM (BitVec 32) := do
  let v := (Mk_SEnvcfg v)
  (pure (_update_SEnvcfg_CBIE
      (_update_SEnvcfg_CBCFE
        (_update_SEnvcfg_CBZE
          (_update_SEnvcfg_LPE
            (_update_SEnvcfg_FIOM o
              (if (sys_enable_writable_fiom : Bool)
              then (_get_SEnvcfg_FIOM v)
              else 0#1))
            (if ((hartSupports Ext_Zicfilp) : Bool)
            then (_get_SEnvcfg_LPE v)
            else 0#1))
          (← do
            if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
            then (pure (_get_SEnvcfg_CBZE v))
            else (pure 0#1)))
        (← do
          if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
          then (pure (_get_SEnvcfg_CBCFE v))
          else (pure 0#1)))
      (← do
        if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
        then
          (if (((_get_SEnvcfg_CBIE v) != 0b10#2) : Bool)
          then (pure (_get_SEnvcfg_CBIE v))
          else (pure 0b00#2))
        else (pure 0b00#2))))

def privLevel_to_str (p : Privilege) : SailM String := do
  match p with
  | User => (pure "U")
  | VirtualUser => (pure "VU")
  | Supervisor =>
    (do
      if ((← (currentlyEnabled Ext_H)) : Bool)
      then (pure "HS")
      else (pure "S"))
  | VirtualSupervisor => (pure "VS")
  | Machine => (pure "M")

def accessType_to_str (a : (AccessType Unit)) : String :=
  match a with
  | .Read _ => "R"
  | .Write _ => "W"
  | .ReadWrite (_, _) => "RW"
  | .InstructionFetch () => "X"

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match arg_ with
  | 0x301 => (pure "misa")
  | 0x300 => (pure "mstatus")
  | 0x310 => (pure "mstatush")
  | 0x747 => (pure "mseccfg")
  | 0x757 => (pure "mseccfgh")
  | 0x30A => (pure "menvcfg")
  | 0x31A => (pure "menvcfgh")
  | 0x10A => (pure "senvcfg")
  | 0x304 => (pure "mie")
  | 0x344 => (pure "mip")
  | 0x302 => (pure "medeleg")
  | 0x312 => (pure "medelegh")
  | 0x303 => (pure "mideleg")
  | 0x342 => (pure "mcause")
  | 0x343 => (pure "mtval")
  | 0x340 => (pure "mscratch")
  | 0x106 => (pure "scounteren")
  | 0x306 => (pure "mcounteren")
  | 0x320 => (pure "mcountinhibit")
  | 0xF11 => (pure "mvendorid")
  | 0xF12 => (pure "marchid")
  | 0xF13 => (pure "mimpid")
  | 0xF14 => (pure "mhartid")
  | 0xF15 => (pure "mconfigptr")
  | 0x100 => (pure "sstatus")
  | 0x144 => (pure "sip")
  | 0x104 => (pure "sie")
  | 0x140 => (pure "sscratch")
  | 0x142 => (pure "scause")
  | 0x143 => (pure "stval")
  | 0x7A0 => (pure "tselect")
  | 0x7A1 => (pure "tdata1")
  | 0x7A2 => (pure "tdata2")
  | 0x7A3 => (pure "tdata3")
  | 0x105 => (pure "stvec")
  | 0x141 => (pure "sepc")
  | 0x305 => (pure "mtvec")
  | 0x341 => (pure "mepc")
  | 0x3A0 => (pure "pmpcfg0")
  | 0x3A1 => (pure "pmpcfg1")
  | 0x3A2 => (pure "pmpcfg2")
  | 0x3A3 => (pure "pmpcfg3")
  | 0x3A4 => (pure "pmpcfg4")
  | 0x3A5 => (pure "pmpcfg5")
  | 0x3A6 => (pure "pmpcfg6")
  | 0x3A7 => (pure "pmpcfg7")
  | 0x3A8 => (pure "pmpcfg8")
  | 0x3A9 => (pure "pmpcfg9")
  | 0x3AA => (pure "pmpcfg10")
  | 0x3AB => (pure "pmpcfg11")
  | 0x3AC => (pure "pmpcfg12")
  | 0x3AD => (pure "pmpcfg13")
  | 0x3AE => (pure "pmpcfg14")
  | 0x3AF => (pure "pmpcfg15")
  | 0x3B0 => (pure "pmpaddr0")
  | 0x3B1 => (pure "pmpaddr1")
  | 0x3B2 => (pure "pmpaddr2")
  | 0x3B3 => (pure "pmpaddr3")
  | 0x3B4 => (pure "pmpaddr4")
  | 0x3B5 => (pure "pmpaddr5")
  | 0x3B6 => (pure "pmpaddr6")
  | 0x3B7 => (pure "pmpaddr7")
  | 0x3B8 => (pure "pmpaddr8")
  | 0x3B9 => (pure "pmpaddr9")
  | 0x3BA => (pure "pmpaddr10")
  | 0x3BB => (pure "pmpaddr11")
  | 0x3BC => (pure "pmpaddr12")
  | 0x3BD => (pure "pmpaddr13")
  | 0x3BE => (pure "pmpaddr14")
  | 0x3BF => (pure "pmpaddr15")
  | 0x3C0 => (pure "pmpaddr16")
  | 0x3C1 => (pure "pmpaddr17")
  | 0x3C2 => (pure "pmpaddr18")
  | 0x3C3 => (pure "pmpaddr19")
  | 0x3C4 => (pure "pmpaddr20")
  | 0x3C5 => (pure "pmpaddr21")
  | 0x3C6 => (pure "pmpaddr22")
  | 0x3C7 => (pure "pmpaddr23")
  | 0x3C8 => (pure "pmpaddr24")
  | 0x3C9 => (pure "pmpaddr25")
  | 0x3CA => (pure "pmpaddr26")
  | 0x3CB => (pure "pmpaddr27")
  | 0x3CC => (pure "pmpaddr28")
  | 0x3CD => (pure "pmpaddr29")
  | 0x3CE => (pure "pmpaddr30")
  | 0x3CF => (pure "pmpaddr31")
  | 0x3D0 => (pure "pmpaddr32")
  | 0x3D1 => (pure "pmpaddr33")
  | 0x3D2 => (pure "pmpaddr34")
  | 0x3D3 => (pure "pmpaddr35")
  | 0x3D4 => (pure "pmpaddr36")
  | 0x3D5 => (pure "pmpaddr37")
  | 0x3D6 => (pure "pmpaddr38")
  | 0x3D7 => (pure "pmpaddr39")
  | 0x3D8 => (pure "pmpaddr40")
  | 0x3D9 => (pure "pmpaddr41")
  | 0x3DA => (pure "pmpaddr42")
  | 0x3DB => (pure "pmpaddr43")
  | 0x3DC => (pure "pmpaddr44")
  | 0x3DD => (pure "pmpaddr45")
  | 0x3DE => (pure "pmpaddr46")
  | 0x3DF => (pure "pmpaddr47")
  | 0x3E0 => (pure "pmpaddr48")
  | 0x3E1 => (pure "pmpaddr49")
  | 0x3E2 => (pure "pmpaddr50")
  | 0x3E3 => (pure "pmpaddr51")
  | 0x3E4 => (pure "pmpaddr52")
  | 0x3E5 => (pure "pmpaddr53")
  | 0x3E6 => (pure "pmpaddr54")
  | 0x3E7 => (pure "pmpaddr55")
  | 0x3E8 => (pure "pmpaddr56")
  | 0x3E9 => (pure "pmpaddr57")
  | 0x3EA => (pure "pmpaddr58")
  | 0x3EB => (pure "pmpaddr59")
  | 0x3EC => (pure "pmpaddr60")
  | 0x3ED => (pure "pmpaddr61")
  | 0x3EE => (pure "pmpaddr62")
  | 0x3EF => (pure "pmpaddr63")
  | 0x001 => (pure "fflags")
  | 0x002 => (pure "frm")
  | 0x003 => (pure "fcsr")
  | 0x008 => (pure "vstart")
  | 0x009 => (pure "vxsat")
  | 0x00A => (pure "vxrm")
  | 0x00F => (pure "vcsr")
  | 0xC20 => (pure "vl")
  | 0xC21 => (pure "vtype")
  | 0xC22 => (pure "vlenb")
  | 0x321 => (pure "mcyclecfg")
  | 0x721 => (pure "mcyclecfgh")
  | 0x322 => (pure "minstretcfg")
  | 0x722 => (pure "minstretcfgh")
  | 0x180 => (pure "satp")
  | 0xC00 => (pure "cycle")
  | 0xC01 => (pure "time")
  | 0xC02 => (pure "instret")
  | 0xC80 => (pure "cycleh")
  | 0xC81 => (pure "timeh")
  | 0xC82 => (pure "instreth")
  | 0xB00 => (pure "mcycle")
  | 0xB02 => (pure "minstret")
  | 0xB80 => (pure "mcycleh")
  | 0xB82 => (pure "minstreth")
  | reg => (hex_bits_12_forwards reg)

def csr_name (csr : (BitVec 12)) : SailM String := do
  (csr_name_map_forwards csr)

def exceptionType_to_str (e : ExceptionType) : String :=
  match e with
  | .E_Fetch_Addr_Align () => "misaligned-fetch"
  | .E_Fetch_Access_Fault () => "fetch-access-fault"
  | .E_Illegal_Instr () => "illegal-instruction"
  | .E_Breakpoint () => "breakpoint"
  | .E_Load_Addr_Align () => "misaligned-load"
  | .E_Load_Access_Fault () => "load-access-fault"
  | .E_SAMO_Addr_Align () => "misaligned-store/amo"
  | .E_SAMO_Access_Fault () => "store/amo-access-fault"
  | .E_U_EnvCall () => "u-call"
  | .E_S_EnvCall () => "s-call"
  | .E_Reserved_10 () => "reserved-0"
  | .E_M_EnvCall () => "m-call"
  | .E_Fetch_Page_Fault () => "fetch-page-fault"
  | .E_Load_Page_Fault () => "load-page-fault"
  | .E_Reserved_14 () => "reserved-1"
  | .E_SAMO_Page_Fault () => "store/amo-page-fault"
  | .E_Reserved_16 () => "reserved-2"
  | .E_Reserved_17 () => "reserved-3"
  | .E_Software_Check () => "software-check-fault"
  | .E_Extension e => (ext_exc_type_to_str e)

def btype_mnemonic_forwards (arg_ : bop) : String :=
  match arg_ with
  | BEQ => "beq"
  | BNE => "bne"
  | BLT => "blt"
  | BGE => "bge"
  | BLTU => "bltu"
  | BGEU => "bgeu"

def encdec_reg_backwards (arg_ : (BitVec 5)) : SailM regidx := do
  let r := arg_
  if (((not base_E_enabled) || ((BitVec.access r 4) == 0#1)) : Bool)
  then (pure (Regidx (Sail.BitVec.extractLsb r (regidx_bit_width -i 1) 0)))
  else
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_reg_forwards (arg_ : regidx) : (BitVec 5) :=
  match arg_ with
  | .Regidx r => (zero_extend (m := 5) r)

def encdec_reg_forwards_matches (arg_ : regidx) : Bool :=
  match arg_ with
  | .Regidx r => true

def reg_abi_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "zero"
  | 0b00001 => "ra"
  | 0b00010 => "sp"
  | 0b00011 => "gp"
  | 0b00100 => "tp"
  | 0b00101 => "t0"
  | 0b00110 => "t1"
  | 0b00111 => "t2"
  | 0b01000 => "s0"
  | 0b01000 => "fp"
  | 0b01001 => "s1"
  | 0b01010 => "a0"
  | 0b01011 => "a1"
  | 0b01100 => "a2"
  | 0b01101 => "a3"
  | 0b01110 => "a4"
  | 0b01111 => "a5"
  | 0b10000 => "a6"
  | 0b10001 => "a7"
  | 0b10010 => "s2"
  | 0b10011 => "s3"
  | 0b10100 => "s4"
  | 0b10101 => "s5"
  | 0b10110 => "s6"
  | 0b10111 => "s7"
  | 0b11000 => "s8"
  | 0b11001 => "s9"
  | 0b11010 => "s10"
  | 0b11011 => "s11"
  | 0b11100 => "t3"
  | 0b11101 => "t4"
  | 0b11110 => "t5"
  | _ => "t6"

def reg_arch_name_raw_forwards (arg_ : (BitVec 5)) : String :=
  match arg_ with
  | 0b00000 => "x0"
  | 0b00001 => "x1"
  | 0b00010 => "x2"
  | 0b00011 => "x3"
  | 0b00100 => "x4"
  | 0b00101 => "x5"
  | 0b00110 => "x6"
  | 0b00111 => "x7"
  | 0b01000 => "x8"
  | 0b01001 => "x9"
  | 0b01010 => "x10"
  | 0b01011 => "x11"
  | 0b01100 => "x12"
  | 0b01101 => "x13"
  | 0b01110 => "x14"
  | 0b01111 => "x15"
  | 0b10000 => "x16"
  | 0b10001 => "x17"
  | 0b10010 => "x18"
  | 0b10011 => "x19"
  | 0b10100 => "x20"
  | 0b10101 => "x21"
  | 0b10110 => "x22"
  | 0b10111 => "x23"
  | 0b11000 => "x24"
  | 0b11001 => "x25"
  | 0b11010 => "x26"
  | 0b11011 => "x27"
  | 0b11100 => "x28"
  | 0b11101 => "x29"
  | 0b11110 => "x30"
  | _ => "x31"

def reg_name_forwards (arg_ : regidx) : SailM String := do
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((encdec_reg_forwards_matches mapping0_) : Bool)
  then
    (let i := (encdec_reg_forwards mapping0_)
    if ((get_config_use_abi_names ()) : Bool)
    then (some (reg_abi_name_raw_forwards i))
    else none)
  else none) with
  | .some result => (pure result)
  | none =>
    (do
      match (let mapping1_ := head_exp_
      if ((encdec_reg_forwards_matches mapping1_) : Bool)
      then
        (let i := (encdec_reg_forwards mapping1_)
        if ((not (get_config_use_abi_names ())) : Bool)
        then (some (reg_arch_name_raw_forwards i))
        else none)
      else none) with
      | .some result => (pure result)
      | _ =>
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))

def creg_name_forwards (arg_ : cregidx) : SailM String := do
  match arg_ with
  | .Cregidx i => (reg_name_forwards (← (encdec_reg_backwards (0b01#2 ++ (i : (BitVec 3))))))

def csr_mnemonic_forwards (arg_ : csrop) : String :=
  match arg_ with
  | CSRRW => "csrrw"
  | CSRRS => "csrrs"
  | CSRRC => "csrrc"

def bit_maybe_i_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "i"
  | _ => ""

def bit_maybe_o_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "o"
  | _ => ""

def bit_maybe_r_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "r"
  | _ => ""

def bit_maybe_w_forwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "w"
  | _ => ""

def fence_bits_forwards (arg_ : (BitVec 4)) : String :=
  match arg_ with
  | 0b0000 => "0"
  | v__8 =>
    (let i : (BitVec 1) := (Sail.BitVec.extractLsb v__8 3 3)
    let w : (BitVec 1) := (Sail.BitVec.extractLsb v__8 0 0)
    let r : (BitVec 1) := (Sail.BitVec.extractLsb v__8 1 1)
    let o : (BitVec 1) := (Sail.BitVec.extractLsb v__8 2 2)
    let i : (BitVec 1) := (Sail.BitVec.extractLsb v__8 3 3)
    (String.append (bit_maybe_i_forwards i)
      (String.append (bit_maybe_o_forwards o)
        (String.append (bit_maybe_r_forwards r) (String.append (bit_maybe_w_forwards w) "")))))

def itype_mnemonic_forwards (arg_ : iop) : String :=
  match arg_ with
  | ADDI => "addi"
  | SLTI => "slti"
  | SLTIU => "sltiu"
  | XORI => "xori"
  | ORI => "ori"
  | ANDI => "andi"

/-- Type quantifiers: k_ex150792_ : Bool -/
def maybe_u_forwards (arg_ : Bool) : String :=
  match arg_ with
  | true => "u"
  | false => ""

def mul_mnemonic_forwards (arg_ : mul_op) : SailM String := do
  match arg_ with
  | { high := false, signed_rs1 := true, signed_rs2 := true } => (pure "mul")
  | { high := true, signed_rs1 := true, signed_rs2 := true } => (pure "mulh")
  | { high := true, signed_rs1 := true, signed_rs2 := false } => (pure "mulhsu")
  | { high := true, signed_rs1 := false, signed_rs2 := false } => (pure "mulhu")
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rtype_mnemonic_forwards (arg_ : rop) : String :=
  match arg_ with
  | ADD => "add"
  | SLT => "slt"
  | SLTU => "sltu"
  | AND => "and"
  | OR => "or"
  | XOR => "xor"
  | SLL => "sll"
  | SRL => "srl"
  | SUB => "sub"
  | SRA => "sra"

def rtypew_mnemonic_forwards (arg_ : ropw) : String :=
  match arg_ with
  | ADDW => "addw"
  | SUBW => "subw"
  | SLLW => "sllw"
  | SRLW => "srlw"
  | SRAW => "sraw"

def shiftiop_mnemonic_forwards (arg_ : sop) : String :=
  match arg_ with
  | SLLI => "slli"
  | SRLI => "srli"
  | SRAI => "srai"

def shiftiwop_mnemonic_forwards (arg_ : sopw) : String :=
  match arg_ with
  | SLLIW => "slliw"
  | SRLIW => "srliw"
  | SRAIW => "sraiw"

def sp_reg_name_forwards (arg_ : Unit) : SailM String := do
  match arg_ with
  | () =>
    (do
      if ((get_config_use_abi_names ()) : Bool)
      then (pure "sp")
      else
        (do
          if ((not (get_config_use_abi_names ())) : Bool)
          then (pure "x2")
          else
            (do
              assert false "Pattern match failure at unknown location"
              throw Error.Exit)))

def utype_mnemonic_forwards (arg_ : uop) : String :=
  match arg_ with
  | LUI => "lui"
  | AUIPC => "auipc"

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def width_mnemonic_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | _ => "d"

def assembly_forwards (arg_ : instruction) : SailM String := do
  match arg_ with
  | .LPAD lpl =>
    (pure (String.append "lpad"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_20_forwards lpl)) ""))))
  | .UTYPE (imm, rd, op) =>
    (pure (String.append (utype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_20_forwards imm)) ""))))))
  | .JAL (imm, rd) =>
    (pure (String.append "jal"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_21_forwards imm)) ""))))))
  | .JALR (imm, rs1, rd) =>
    (pure (String.append "jalr"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_12_forwards imm))
                (String.append "("
                  (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))
  | .BTYPE (imm, rs2, rs1, op) =>
    (pure (String.append (btype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_13_forwards imm)) ""))))))))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure (String.append (itype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
  | .SHIFTIOP (shamt, rs1, rd, op) =>
    (pure (String.append (shiftiop_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_6_forwards shamt)) ""))))))))
  | .RTYPE (rs2, rs1, rd, op) =>
    (pure (String.append (rtype_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (pure (String.append "l"
        (String.append (width_mnemonic_forwards width)
          (String.append (maybe_u_forwards is_unsigned)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_12_forwards imm))
                    (String.append "("
                      (String.append (← (reg_name_forwards rs1)) (String.append ")" "")))))))))))
  | .STORE (imm, rs2, rs1, width) =>
    (pure (String.append "s"
        (String.append (width_mnemonic_forwards width)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rs2))
              (String.append (sep_forwards ())
                (String.append (← (hex_bits_signed_12_forwards imm))
                  (String.append (opt_spc_forwards ())
                    (String.append "("
                      (String.append (opt_spc_forwards ())
                        (String.append (← (reg_name_forwards rs1))
                          (String.append (opt_spc_forwards ()) (String.append ")" "")))))))))))))
  | .ADDIW (imm, rs1, rd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "addiw"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_signed_12_forwards imm)) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, op) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append (rtypew_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append (shiftiwop_mnemonic_forwards op)
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_5_forwards shamt)) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE (pred, succ) =>
    (pure (String.append "fence"
        (String.append (spc_forwards ())
          (String.append (fence_bits_forwards pred)
            (String.append (sep_forwards ()) (String.append (fence_bits_forwards succ) ""))))))
  | .FENCE_TSO () => (pure "fence.tso")
  | .ECALL () => (pure "ecall")
  | .MRET () => (pure "mret")
  | .SRET () => (pure "sret")
  | .EBREAK () => (pure "ebreak")
  | .WFI () => (pure "wfi")
  | .SFENCE_VMA (rs1, rs2) =>
    (pure (String.append "sfence.vma"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs1))
            (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
  | .FENCE_RESERVED (fm, pred, succ, rs, rd) =>
    (do
      if ((((fm != 0b0000#4) && (fm != 0b1000#4)) || ((bne rs zreg) || (bne rd zreg))) : Bool)
      then
        (pure (String.append "fence.reserved."
            (String.append (fence_bits_forwards pred)
              (String.append "."
                (String.append (fence_bits_forwards succ)
                  (String.append "."
                    (String.append (← (reg_name_forwards rs))
                      (String.append "."
                        (String.append (← (reg_name_forwards rd))
                          (String.append "." (String.append (← (hex_bits_4_forwards fm)) "")))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCEI_RESERVED (imm, rs, rd) =>
    (do
      if (((imm != 0b000000000000#12) || ((bne rs zreg) || (bne rd zreg))) : Bool)
      then
        (pure (String.append "fence.i.reserved."
            (String.append (← (reg_name_forwards rd))
              (String.append "."
                (String.append (← (reg_name_forwards rs))
                  (String.append "." (String.append (← (hex_bits_12_forwards imm)) "")))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (pure (String.append (← (mul_mnemonic_forwards mul_op))
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (reg_name_forwards rs1))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "div"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (pure (String.append "rem"
        (String.append (maybe_u_forwards is_unsigned)
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (reg_name_forwards rs1))
                  (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) "")))))))))
  | .MULW (rs2, rs1, rd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "mulw"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (reg_name_forwards rs1))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs2)) ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "div"
            (String.append (maybe_u_forwards is_unsigned)
              (String.append "w"
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs1))
                        (String.append (sep_forwards ())
                          (String.append (← (reg_name_forwards rs2)) ""))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "rem"
            (String.append (maybe_u_forwards is_unsigned)
              (String.append "w"
                (String.append (spc_forwards ())
                  (String.append (← (reg_name_forwards rd))
                    (String.append (sep_forwards ())
                      (String.append (← (reg_name_forwards rs1))
                        (String.append (sep_forwards ())
                          (String.append (← (reg_name_forwards rs2)) ""))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_NOP 0b000000 => (pure "c.nop")
  | .C_NOP imm =>
    (do
      if ((imm != (zeros (n := 6))) : Bool)
      then
        (pure (String.append "c.nop"
            (String.append (spc_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI4SPN (rdc, nzimm) =>
    (do
      if ((nzimm != 0b00000000#8) : Bool)
      then
        (pure (String.append "c.addi4spn"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rdc))
                (String.append (sep_forwards ())
                  (String.append (← (sp_reg_name_forwards ()))
                    (String.append (sep_forwards ())
                      (String.append (← (hex_bits_10_forwards ((nzimm : (BitVec 8)) ++ 0b00#2)))
                        ""))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LW (uimm, rsc, rdc) =>
    (pure (String.append "c.lw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rdc))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) ++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
  | .C_LD (uimm, rsc, rdc) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.ld"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rdc))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) ++ 0b000#3)))
                    (String.append "("
                      (String.append (← (creg_name_forwards rsc)) (String.append ")" "")))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SW (uimm, rsc1, rsc2) =>
    (pure (String.append "c.sw"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsc2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_7_forwards ((uimm : (BitVec 5)) ++ 0b00#2)))
                (String.append "("
                  (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
  | .C_SD (uimm, rsc1, rsc2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.sd"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rsc2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 5)) ++ 0b000#3)))
                    (String.append "("
                      (String.append (← (creg_name_forwards rsc1)) (String.append ")" "")))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI (imm, rsd) =>
    (do
      if ((bne rsd zreg) : Bool)
      then
        (pure (String.append "c.addi"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JAL imm =>
    (pure (String.append "c.jal"
        (String.append (spc_forwards ())
          (String.append (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) ++ 0#1))) ""))))
  | .C_ADDIW (imm, rsd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.addiw"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LI (imm, rd) =>
    (pure (String.append "c.li"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_ADDI16SP imm =>
    (do
      if ((imm != 0b000000#6) : Bool)
      then
        (pure (String.append "c.addi16sp"
            (String.append (spc_forwards ())
              (String.append (← (sp_reg_name_forwards ()))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_10_forwards ((imm : (BitVec 6)) ++ 0x0#4)))
                    ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LUI (imm, rd) =>
    (do
      if (((bne rd sp) && (imm != 0b000000#6)) : Bool)
      then
        (pure (String.append "c.lui"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI (shamt, rsd) =>
    (pure (String.append "c.srli"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_SRAI (shamt, rsd) =>
    (pure (String.append "c.srai"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_ANDI (imm, rsd) =>
    (pure (String.append "c.andi"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_6_forwards imm)) ""))))))
  | .C_SUB (rsd, rs2) =>
    (pure (String.append "c.sub"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_XOR (rsd, rs2) =>
    (pure (String.append "c.xor"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_OR (rsd, rs2) =>
    (pure (String.append "c.or"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_AND (rsd, rs2) =>
    (pure (String.append "c.and"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
  | .C_SUBW (rsd, rs2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.subw"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDW (rsd, rs2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.addw"
            (String.append (spc_forwards ())
              (String.append (← (creg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (creg_name_forwards rs2)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_J imm =>
    (pure (String.append "c.j"
        (String.append (spc_forwards ())
          (String.append (← (hex_bits_signed_12_forwards ((imm : (BitVec 11)) ++ 0#1))) ""))))
  | .C_BEQZ (imm, rs) =>
    (pure (String.append "c.beqz"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rs))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_9_forwards ((imm : (BitVec 8)) ++ 0#1))) ""))))))
  | .C_BNEZ (imm, rs) =>
    (pure (String.append "c.bnez"
        (String.append (spc_forwards ())
          (String.append (← (creg_name_forwards rs))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_signed_9_forwards ((imm : (BitVec 8)) ++ 0#1))) ""))))))
  | .C_SLLI (shamt, rsd) =>
    (pure (String.append "c.slli"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rsd))
            (String.append (sep_forwards ()) (String.append (← (hex_bits_6_forwards shamt)) ""))))))
  | .C_LWSP (uimm, rd) =>
    (do
      if ((bne rd zreg) : Bool)
      then
        (pure (String.append "c.lwsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) ++ 0b00#2)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LDSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && (xlen == 64)) : Bool)
      then
        (pure (String.append "c.ldsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) ++ 0b000#3)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SWSP (uimm, rs2) =>
    (pure (String.append "c.swsp"
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rs2))
            (String.append (sep_forwards ())
              (String.append (← (hex_bits_8_forwards ((uimm : (BitVec 6)) ++ 0b00#2)))
                (String.append "("
                  (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
  | .C_SDSP (uimm, rs2) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (String.append "c.sdsp"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rs2))
                (String.append (sep_forwards ())
                  (String.append (← (hex_bits_9_forwards ((uimm : (BitVec 6)) ++ 0b000#3)))
                    (String.append "("
                      (String.append (← (sp_reg_name_forwards ())) (String.append ")" "")))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JR rs1 =>
    (do
      if ((bne rs1 zreg) : Bool)
      then
        (pure (String.append "c.jr"
            (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JALR rs1 =>
    (do
      if ((bne rs1 zreg) : Bool)
      then
        (pure (String.append "c.jalr"
            (String.append (spc_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV (rd, rs2) =>
    (do
      if ((bne rs2 zreg) : Bool)
      then
        (pure (String.append "c.mv"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rd))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_EBREAK () => (pure "c.ebreak")
  | .C_ADD (rsd, rs2) =>
    (do
      if ((bne rs2 zreg) : Bool)
      then
        (pure (String.append "c.add"
            (String.append (spc_forwards ())
              (String.append (← (reg_name_forwards rsd))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs2)) ""))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRImm (csr, imm, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append "i"
          (String.append (spc_forwards ())
            (String.append (← (reg_name_forwards rd))
              (String.append (sep_forwards ())
                (String.append (← (csr_name_map_forwards csr))
                  (String.append (sep_forwards ())
                    (String.append (← (hex_bits_5_forwards imm)) "")))))))))
  | .CSRReg (csr, rs1, rd, op) =>
    (pure (String.append (csr_mnemonic_forwards op)
        (String.append (spc_forwards ())
          (String.append (← (reg_name_forwards rd))
            (String.append (sep_forwards ())
              (String.append (← (csr_name_map_forwards csr))
                (String.append (sep_forwards ()) (String.append (← (reg_name_forwards rs1)) ""))))))))
  | .FENCEI () => (pure "fence.i")
  | .ILLEGAL s =>
    (pure (String.append "illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_32_forwards s)) ""))))
  | .C_ILLEGAL s =>
    (pure (String.append "c.illegal"
        (String.append (spc_forwards ()) (String.append (← (hex_bits_16_forwards s)) ""))))

def print_insn (insn : instruction) : SailM String := do
  (assembly_forwards insn)

def ptw_error_to_str (e : PTW_Error) : String :=
  match e with
  | .PTW_Invalid_Addr () => "invalid-source-addr"
  | .PTW_Access () => "mem-access-error"
  | .PTW_Invalid_PTE () => "invalid-pte"
  | .PTW_No_Permission () => "no-permission"
  | .PTW_Misaligned () => "misaligned-superpage"
  | .PTW_PTE_Update () => "pte-update-needed"
  | .PTW_Ext_Error e => "extension-error"

def wait_name_backwards (arg_ : String) : SailM WaitReason := do
  match arg_ with
  | "WAIT-WFI" => (pure WAIT_WFI)
  | "WAIT-WRS-STO" => (pure WAIT_WRS_STO)
  | "WAIT-WRS-NTO" => (pure WAIT_WRS_NTO)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def wait_name_forwards (arg_ : WaitReason) : String :=
  match arg_ with
  | WAIT_WFI => "WAIT-WFI"
  | WAIT_WRS_STO => "WAIT-WRS-STO"
  | WAIT_WRS_NTO => "WAIT-WRS-NTO"

/-- Type quantifiers: k_a : Type -/
def is_load_store (ac : (AccessType k_a)) : Bool :=
  match ac with
  | .Read _ => true
  | .Write _ => true
  | .ReadWrite _ => true
  | .InstructionFetch _ => false

def undefined_InterruptType (_ : Unit) : SailM InterruptType := do
  (internal_pick
    [I_U_Software, I_S_Software, I_M_Software, I_U_Timer, I_S_Timer, I_M_Timer, I_U_External, I_S_External, I_M_External])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def InterruptType_of_num (arg_ : Nat) : InterruptType :=
  match arg_ with
  | 0 => I_U_Software
  | 1 => I_S_Software
  | 2 => I_M_Software
  | 3 => I_U_Timer
  | 4 => I_S_Timer
  | 5 => I_M_Timer
  | 6 => I_U_External
  | 7 => I_S_External
  | _ => I_M_External

def num_of_InterruptType (arg_ : InterruptType) : Int :=
  match arg_ with
  | I_U_Software => 0
  | I_S_Software => 1
  | I_M_Software => 2
  | I_U_Timer => 3
  | I_S_Timer => 4
  | I_M_Timer => 5
  | I_U_External => 6
  | I_S_External => 7
  | I_M_External => 8

def interruptType_bits_forwards (arg_ : InterruptType) : (BitVec 6) :=
  match arg_ with
  | I_U_Software => 0b000000#6
  | I_S_Software => 0b000001#6
  | I_M_Software => 0b000011#6
  | I_U_Timer => 0b000100#6
  | I_S_Timer => 0b000101#6
  | I_M_Timer => 0b000111#6
  | I_U_External => 0b001000#6
  | I_S_External => 0b001001#6
  | I_M_External => 0b001011#6

def interruptType_bits_backwards (arg_ : (BitVec 6)) : SailM InterruptType := do
  match arg_ with
  | 0b000000 => (pure I_U_Software)
  | 0b000001 => (pure I_S_Software)
  | 0b000011 => (pure I_M_Software)
  | 0b000100 => (pure I_U_Timer)
  | 0b000101 => (pure I_S_Timer)
  | 0b000111 => (pure I_M_Timer)
  | 0b001000 => (pure I_U_External)
  | 0b001001 => (pure I_S_External)
  | 0b001011 => (pure I_M_External)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def interruptType_bits_forwards_matches (arg_ : InterruptType) : Bool :=
  match arg_ with
  | I_U_Software => true
  | I_S_Software => true
  | I_M_Software => true
  | I_U_Timer => true
  | I_S_Timer => true
  | I_M_Timer => true
  | I_U_External => true
  | I_S_External => true
  | I_M_External => true

def interruptType_bits_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000000 => true
  | 0b000001 => true
  | 0b000011 => true
  | 0b000100 => true
  | 0b000101 => true
  | 0b000111 => true
  | 0b001000 => true
  | 0b001001 => true
  | 0b001011 => true
  | _ => false

def exceptionType_bits_forwards (arg_ : ExceptionType) : (BitVec 6) :=
  match arg_ with
  | .E_Fetch_Addr_Align () => 0b000000#6
  | .E_Fetch_Access_Fault () => 0b000001#6
  | .E_Illegal_Instr () => 0b000010#6
  | .E_Breakpoint () => 0b000011#6
  | .E_Load_Addr_Align () => 0b000100#6
  | .E_Load_Access_Fault () => 0b000101#6
  | .E_SAMO_Addr_Align () => 0b000110#6
  | .E_SAMO_Access_Fault () => 0b000111#6
  | .E_U_EnvCall () => 0b001000#6
  | .E_S_EnvCall () => 0b001001#6
  | .E_Reserved_10 () => 0b001010#6
  | .E_M_EnvCall () => 0b001011#6
  | .E_Fetch_Page_Fault () => 0b001100#6
  | .E_Load_Page_Fault () => 0b001101#6
  | .E_Reserved_14 () => 0b001110#6
  | .E_SAMO_Page_Fault () => 0b001111#6
  | .E_Reserved_16 () => 0b010000#6
  | .E_Reserved_17 () => 0b010001#6
  | .E_Software_Check () => 0b010010#6
  | .E_Extension e => (ext_exc_type_bits_forwards e)

def exceptionType_bits_backwards (arg_ : (BitVec 6)) : SailM ExceptionType := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | 0b000000 => (pure (some (E_Fetch_Addr_Align ())))
    | 0b000001 => (pure (some (E_Fetch_Access_Fault ())))
    | 0b000010 => (pure (some (E_Illegal_Instr ())))
    | 0b000011 => (pure (some (E_Breakpoint ())))
    | 0b000100 => (pure (some (E_Load_Addr_Align ())))
    | 0b000101 => (pure (some (E_Load_Access_Fault ())))
    | 0b000110 => (pure (some (E_SAMO_Addr_Align ())))
    | 0b000111 => (pure (some (E_SAMO_Access_Fault ())))
    | 0b001000 => (pure (some (E_U_EnvCall ())))
    | 0b001001 => (pure (some (E_S_EnvCall ())))
    | 0b001010 => (pure (some (E_Reserved_10 ())))
    | 0b001011 => (pure (some (E_M_EnvCall ())))
    | 0b001100 => (pure (some (E_Fetch_Page_Fault ())))
    | 0b001101 => (pure (some (E_Load_Page_Fault ())))
    | 0b001110 => (pure (some (E_Reserved_14 ())))
    | 0b001111 => (pure (some (E_SAMO_Page_Fault ())))
    | 0b010000 => (pure (some (E_Reserved_16 ())))
    | 0b010001 => (pure (some (E_Reserved_17 ())))
    | 0b010010 => (pure (some (E_Software_Check ())))
    | mapping0_ =>
      (do
        if ((ext_exc_type_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (ext_exc_type_bits_backwards mapping0_)) with
            | e => (pure (some (E_Extension e))))
        else (pure none))) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def exceptionType_bits_forwards_matches (arg_ : ExceptionType) : Bool :=
  match arg_ with
  | .E_Fetch_Addr_Align () => true
  | .E_Fetch_Access_Fault () => true
  | .E_Illegal_Instr () => true
  | .E_Breakpoint () => true
  | .E_Load_Addr_Align () => true
  | .E_Load_Access_Fault () => true
  | .E_SAMO_Addr_Align () => true
  | .E_SAMO_Access_Fault () => true
  | .E_U_EnvCall () => true
  | .E_S_EnvCall () => true
  | .E_Reserved_10 () => true
  | .E_M_EnvCall () => true
  | .E_Fetch_Page_Fault () => true
  | .E_Load_Page_Fault () => true
  | .E_Reserved_14 () => true
  | .E_SAMO_Page_Fault () => true
  | .E_Reserved_16 () => true
  | .E_Reserved_17 () => true
  | .E_Software_Check () => true
  | .E_Extension e => true

def exceptionType_bits_backwards_matches (arg_ : (BitVec 6)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    match head_exp_ with
    | 0b000000 => (pure (some true))
    | 0b000001 => (pure (some true))
    | 0b000010 => (pure (some true))
    | 0b000011 => (pure (some true))
    | 0b000100 => (pure (some true))
    | 0b000101 => (pure (some true))
    | 0b000110 => (pure (some true))
    | 0b000111 => (pure (some true))
    | 0b001000 => (pure (some true))
    | 0b001001 => (pure (some true))
    | 0b001010 => (pure (some true))
    | 0b001011 => (pure (some true))
    | 0b001100 => (pure (some true))
    | 0b001101 => (pure (some true))
    | 0b001110 => (pure (some true))
    | 0b001111 => (pure (some true))
    | 0b010000 => (pure (some true))
    | 0b010001 => (pure (some true))
    | 0b010010 => (pure (some true))
    | mapping0_ =>
      (do
        if ((ext_exc_type_bits_backwards_matches mapping0_) : Bool)
        then
          (do
            match (← (ext_exc_type_bits_backwards mapping0_)) with
            | e => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def undefined_SWCheckCodes (_ : Unit) : SailM SWCheckCodes := do
  (internal_pick [LANDING_PAD_FAULT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def SWCheckCodes_of_num (arg_ : Nat) : SWCheckCodes :=
  match arg_ with
  | _ => LANDING_PAD_FAULT

def num_of_SWCheckCodes (arg_ : SWCheckCodes) : Int :=
  match arg_ with
  | LANDING_PAD_FAULT => 0

def sw_check_code_to_bits (c : SWCheckCodes) : (BitVec 32) :=
  match c with
  | LANDING_PAD_FAULT => (zero_extend (m := 32) 0b010#3)

def undefined_TrapVectorMode (_ : Unit) : SailM TrapVectorMode := do
  (internal_pick [TV_Direct, TV_Vector, TV_Reserved])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TrapVectorMode_of_num (arg_ : Nat) : TrapVectorMode :=
  match arg_ with
  | 0 => TV_Direct
  | 1 => TV_Vector
  | _ => TV_Reserved

def num_of_TrapVectorMode (arg_ : TrapVectorMode) : Int :=
  match arg_ with
  | TV_Direct => 0
  | TV_Vector => 1
  | TV_Reserved => 2

def trapVectorMode_of_bits (m : (BitVec 2)) : TrapVectorMode :=
  match m with
  | 0b00 => TV_Direct
  | 0b01 => TV_Vector
  | _ => TV_Reserved

def undefined_xRET_type (_ : Unit) : SailM xRET_type := do
  (internal_pick [XRET_M, XRET_S])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def xRET_type_of_num (arg_ : Nat) : xRET_type :=
  match arg_ with
  | 0 => XRET_M
  | _ => XRET_S

def num_of_xRET_type (arg_ : xRET_type) : Int :=
  match arg_ with
  | XRET_M => 0
  | XRET_S => 1

def undefined_ExtStatus (_ : Unit) : SailM ExtStatus := do
  (internal_pick [Off, Initial, Clean, Dirty])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ExtStatus_of_num (arg_ : Nat) : ExtStatus :=
  match arg_ with
  | 0 => Off
  | 1 => Initial
  | 2 => Clean
  | _ => Dirty

def num_of_ExtStatus (arg_ : ExtStatus) : Int :=
  match arg_ with
  | Off => 0
  | Initial => 1
  | Clean => 2
  | Dirty => 3

def extStatus_bits_forwards (arg_ : ExtStatus) : (BitVec 2) :=
  match arg_ with
  | Off => 0b00#2
  | Initial => 0b01#2
  | Clean => 0b10#2
  | Dirty => 0b11#2

def extStatus_bits_backwards (arg_ : (BitVec 2)) : ExtStatus :=
  match arg_ with
  | 0b00 => Off
  | 0b01 => Initial
  | 0b10 => Clean
  | _ => Dirty

def extStatus_bits_forwards_matches (arg_ : ExtStatus) : Bool :=
  match arg_ with
  | Off => true
  | Initial => true
  | Clean => true
  | Dirty => true

def extStatus_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def extStatus_to_bits (e : ExtStatus) : (BitVec 2) :=
  (extStatus_bits_forwards e)

def extStatus_of_bits (b : (BitVec 2)) : ExtStatus :=
  (extStatus_bits_backwards b)

def undefined_SATPMode (_ : Unit) : SailM SATPMode := do
  (internal_pick [Bare, Sv32, Sv39, Sv48, Sv57])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SATPMode_of_num (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 0 => Bare
  | 1 => Sv32
  | 2 => Sv39
  | 3 => Sv48
  | _ => Sv57

def num_of_SATPMode (arg_ : SATPMode) : Int :=
  match arg_ with
  | Bare => 0
  | Sv32 => 1
  | Sv39 => 2
  | Sv48 => 3
  | Sv57 => 4

def satpMode_of_bits (a : Architecture) (m : (BitVec 4)) : (Option SATPMode) :=
  match (a, m) with
  | (_, 0x0) => (some Bare)
  | (RV32, 0x1) => (some Sv32)
  | (RV64, 0x8) => (some Sv39)
  | (RV64, 0x9) => (some Sv48)
  | (RV64, 0xA) => (some Sv57)
  | (_, _) => none

def undefined_WaitReason (_ : Unit) : SailM WaitReason := do
  (internal_pick [WAIT_WFI, WAIT_WRS_STO, WAIT_WRS_NTO])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def WaitReason_of_num (arg_ : Nat) : WaitReason :=
  match arg_ with
  | 0 => WAIT_WFI
  | 1 => WAIT_WRS_STO
  | _ => WAIT_WRS_NTO

def num_of_WaitReason (arg_ : WaitReason) : Int :=
  match arg_ with
  | WAIT_WFI => 0
  | WAIT_WRS_STO => 1
  | WAIT_WRS_NTO => 2

def wait_name_forwards_matches (arg_ : WaitReason) : Bool :=
  match arg_ with
  | WAIT_WFI => true
  | WAIT_WRS_STO => true
  | WAIT_WRS_NTO => true

def wait_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "WAIT-WFI" => true
  | "WAIT-WRS-STO" => true
  | "WAIT-WRS-NTO" => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def width_enc_forwards (arg_ : Nat) : (BitVec 2) :=
  match arg_ with
  | 1 => 0b00#2
  | 2 => 0b01#2
  | 4 => 0b10#2
  | _ => 0b11#2

def width_enc_backwards (arg_ : (BitVec 2)) : Int :=
  match arg_ with
  | 0b00 => 1
  | 0b01 => 2
  | 0b10 => 4
  | _ => 8

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def width_enc_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def width_enc_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def width_mnemonic_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "b" => (pure 1)
  | "h" => (pure 2)
  | "w" => (pure 4)
  | "d" => (pure 8)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8} -/
def width_mnemonic_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | _ => false

def width_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8, 16} -/
def width_enc_wide_forwards (arg_ : Nat) : (BitVec 3) :=
  match arg_ with
  | 1 => 0b000#3
  | 2 => 0b001#3
  | 4 => 0b010#3
  | 8 => 0b011#3
  | _ => 0b100#3

def width_enc_wide_backwards (arg_ : (BitVec 3)) : SailM Int := do
  match arg_ with
  | 0b000 => (pure 1)
  | 0b001 => (pure 2)
  | 0b010 => (pure 4)
  | 0b011 => (pure 8)
  | 0b100 => (pure 16)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8, 16} -/
def width_enc_wide_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 16 => true
  | _ => false

def width_enc_wide_backwards_matches (arg_ : (BitVec 3)) : Bool :=
  match arg_ with
  | 0b000 => true
  | 0b001 => true
  | 0b010 => true
  | 0b011 => true
  | 0b100 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8, 16} -/
def width_mnemonic_wide_forwards (arg_ : Nat) : String :=
  match arg_ with
  | 1 => "b"
  | 2 => "h"
  | 4 => "w"
  | 8 => "d"
  | _ => "q"

def width_mnemonic_wide_backwards (arg_ : String) : SailM Int := do
  match arg_ with
  | "b" => (pure 1)
  | "h" => (pure 2)
  | "w" => (pure 4)
  | "d" => (pure 8)
  | "q" => (pure 16)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {1, 2, 4, 8, 16} -/
def width_mnemonic_wide_forwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 1 => true
  | 2 => true
  | 4 => true
  | 8 => true
  | 16 => true
  | _ => false

def width_mnemonic_wide_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "b" => true
  | "h" => true
  | "w" => true
  | "d" => true
  | "q" => true
  | _ => false

