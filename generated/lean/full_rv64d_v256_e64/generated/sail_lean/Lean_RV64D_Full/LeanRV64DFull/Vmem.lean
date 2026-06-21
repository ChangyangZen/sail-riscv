import LeanRV64DFull.Flow
import LeanRV64DFull.Prelude
import LeanRV64DFull.Errors
import LeanRV64DFull.Xlen
import LeanRV64DFull.PreludeMemAddrtype
import LeanRV64DFull.TypesExt
import LeanRV64DFull.Types
import LeanRV64DFull.VmemTypes
import LeanRV64DFull.SysRegs
import LeanRV64DFull.SysControl
import LeanRV64DFull.Platform
import LeanRV64DFull.Mem
import LeanRV64DFull.VmemPte
import LeanRV64DFull.VmemPtw
import LeanRV64DFull.VmemTlb

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

noncomputable section

namespace LeanRV64DFull.Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
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
open seed_opst
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
open ntl_type
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
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open bop
open biop_zbs
open barrier_kind
open amoop
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

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, pte_size ∈ {4, 8} -/
def write_pte (paddr : physaddr) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result Bool ExceptionType) := do
  (mem_write_value_priv paddr pte_size pte Supervisor false false false)

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, pte_size ∈ {4, 8} -/
def read_pte (paddr : physaddr) (pte_size : Nat) : SailM (Result (BitVec (8 * pte_size)) ExceptionType) := do
  (mem_read_priv (Read Data) Supervisor paddr pte_size false false false)

/-- Type quantifiers: k_ex591081_ : Bool, level : Nat, k_ex591079_ : Bool, k_ex591078_ : Bool, sv_width
  : Nat, is_sv_mode(sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32  : Bool) then 1 else (if ( sv_width = 39  : Bool) then 2 else (if ( sv_width =
  48  : Bool) then 3 else 4))) -/
def pt_walk (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (level : Nat) (global : Bool) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let vpn_i_size :=
    if ((sv_width == 32) : Bool)
    then 10
    else 9
  let vpn_i := (Int.tmod (BitVec.toNatInt (shiftr vpn (level *i vpn_i_size))) (2 ^i vpn_i_size))
  let log_pte_size_bytes :=
    if ((sv_width == 32) : Bool)
    then 2
    else 3
  let pte_addr :=
    ((((BitVec.toNatInt pt_base) *i (2 ^i vpn_i_size)) +i vpn_i) *i (2 ^i log_pte_size_bytes))
  assert ((sv_width == 32) || (xlen == 64)) "sys/vmem.sail:103.36-103.37"
  let pte_addr := (Physaddr (to_bits_truncate (l := physaddrbits_len) pte_addr))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ => (pure (Err ((PTW_Access ()), ext_ptw)))
  | .Ok pte =>
    (do
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let pte_ext := (ext_bits_of_PTE pte)
      if ((← (pte_is_invalid pte_flags pte_ext)) : Bool)
      then (pure (Err ((PTW_Invalid_PTE ()), ext_ptw)))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let global := (global || ((_get_PTE_Flags_G pte_flags) == 1#1))
          if ((pte_is_non_leaf pte_flags) : Bool)
          then
            (do
              if ((level >b 0) : Bool)
              then (pt_walk sv_width vpn ac priv mxr do_sum ppn (level -i 1) global ext_ptw)
              else (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
          else
            (do
              let ppn_size_bits :=
                if ((sv_width == 32) : Bool)
                then 10
                else 9
              if ((level >b 0) : Bool)
              then
                (do
                  let low_bits := (ppn_size_bits *i level)
                  if (((Int.tmod (BitVec.toNatInt ppn) (2 ^i low_bits)) != 0) : Bool)
                  then
                    SailME.throw ((Err ((PTW_Misaligned ()), ext_ptw)) : (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)))
                  else (pure ()))
              else (pure ())
              match (← (check_PTE_permission ac priv mxr do_sum pte_flags pte_ext ext_ptw)) with
              | .PTE_Check_Failure (ext_ptw, ext_ptw_fail) =>
                (pure (Err ((ext_get_ptw_error ext_ptw_fail), ext_ptw)))
              | .PTE_Check_Success ext_ptw =>
                (let ppn :=
                  if ((level >b 0) : Bool)
                  then
                    (let low_bits := (ppn_size_bits *i level)
                    let ppn_low := (2 ^i low_bits)
                    let ppn_int :=
                      (((Int.tdiv (BitVec.toNatInt ppn) ppn_low) *i ppn_low) +i (Int.tmod
                          (BitVec.toNatInt vpn) ppn_low))
                    (to_bits_truncate (l := (Sail.BitVec.length ppn)) ppn_int))
                  else ppn
                (pure (Ok
                    ({ ppn := ppn
                       pte := pte
                       pteAddr := pte_addr
                       level := level
                       global := global }, ext_ptw)))))))
termination_by (level).toNat
decreasing_by
  all_goals
    simp_wf
    try unfold Nat.toNat at *
    try simp at *
    try omega

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {32, 64} -/
def satp_to_asid (satp_val : (BitVec k_n)) : (BitVec (if ( k_n = 32  : Bool) then 9 else 16)) :=
  let asid_width :=
    if (((Sail.BitVec.length satp_val) == 32) : Bool)
    then 9
    else 16
  let asid :=
    if (((Sail.BitVec.length satp_val) == 32) : Bool)
    then (BitVec.toNatInt (_get_Satp32_Asid (Mk_Satp32 satp_val)))
    else (BitVec.toNatInt (_get_Satp64_Asid (Mk_Satp64 satp_val)))
  (to_bits_truncate (l := asid_width) asid)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {32, 64} -/
def satp_to_ppn (satp_val : (BitVec k_n)) : (BitVec (if ( k_n = 32  : Bool) then 22 else 44)) :=
  let ppn_width :=
    if (((Sail.BitVec.length satp_val) == 32) : Bool)
    then 22
    else 44
  let ppn :=
    if (((Sail.BitVec.length satp_val) == 32) : Bool)
    then (BitVec.toNatInt (_get_Satp32_PPN (Mk_Satp32 satp_val)))
    else (BitVec.toNatInt (_get_Satp64_PPN (Mk_Satp64 satp_val)))
  (to_bits_truncate (l := ppn_width) ppn)

def translationMode (priv : Privilege) : SailM SATPMode := do
  if ((priv == Machine) : Bool)
  then (pure Bare)
  else
    (do
      let arch ← do (architecture Supervisor)
      let mbits ← (( do
        match arch with
        | RV64 =>
          (do
            assert (xlen ≥b 64) "sys/vmem.sail:200.25-200.26"
            (pure (_get_Satp64_Mode (Mk_Satp64 (← readReg satp)))))
        | RV32 =>
          (pure (0b000#3 ++ (_get_Satp32_Mode
                (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg satp) 31 0)))))
        | RV128 => (internal_error "sys/vmem.sail" 204 "RV128 not supported") ) : SailM satp_mode )
      match (satpMode_of_bits arch mbits) with
      | .some m => (pure m)
      | none => (internal_error "sys/vmem.sail" 209 "invalid translation mode in satp"))

/-- Type quantifiers: k_ex591144_ : Bool, k_ex591143_ : Bool, sv_width : Nat, pte_size : Nat, pte_size
  ≥ 0, is_sv_mode(sv_width) ∧ pte_size ∈ {4, 8} -/
def translate_TLB_hit_pte (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) (ent : TLB_Entry) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × Unit) (PTW_Error × Unit)) := do
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do (check_PTE_permission ac priv mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, ext_ptw_fail) =>
    (pure (Err ((ext_get_ptw_error ext_ptw_fail), ext_ptw)))
  | .PTE_Check_Success ext_ptw =>
    (do
      match (update_PTE_Bits pte ac) with
      | none => (pure (Ok ((tlb_get_ppn sv_width ent vpn), ext_ptw)))
      | .some pte' =>
        (do
          if ((not plat_enable_dirty_update) : Bool)
          then (pure (Err ((PTW_PTE_Update ()), ext_ptw)))
          else
            (do
              (write_TLB (tlb_hash sv_width vpn) (tlb_set_pte ent pte'))
              match (← (write_pte ent.pteAddr pte_size pte')) with
              | .Ok _ => (pure ())
              | .Err e => (internal_error "sys/vmem.sail" 259 "invalid physical address in TLB")
              (pure (Ok ((tlb_get_ppn sv_width ent vpn), ext_ptw))))))

/-- Type quantifiers: sv_width : Nat, k_p : Nat, k_p ≥ 0, is_sv_mode(sv_width) ∧ k_p ≥ 0 -/
def normalize_TLB_ppn_result (sv_width : Nat) (result : (Result ((BitVec k_p) × Unit) (PTW_Error × Unit))) : (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × Unit) (PTW_Error × Unit)) :=
  let ppn_width :=
    if ((sv_width == 32) : Bool)
    then 22
    else 44
  match result with
  | .Ok (ppn, ext_ptw) => (Ok ((to_bits_truncate (l := ppn_width) (BitVec.toNatInt ppn)), ext_ptw))
  | .Err (err, ext_ptw) => (Err (err, ext_ptw))

/-- Type quantifiers: k_ex591191_ : Bool, k_ex591190_ : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate_TLB_hit (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) (ent : TLB_Entry) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × Unit) (PTW_Error × Unit)) := do
  let pte_size :=
    if ((sv_width == 32) : Bool)
    then 4
    else 8
  if ((pte_size == 4) : Bool)
  then
    (do
      let pte : (BitVec 32) := (tlb_get_pte 4 ent)
      (pure (normalize_TLB_ppn_result sv_width
          (← (translate_TLB_hit_pte sv_width asid vpn ac priv mxr do_sum ext_ptw ent 4 pte)))))
  else
    (do
      let pte : (BitVec 64) := (tlb_get_pte 8 ent)
      (pure (normalize_TLB_ppn_result sv_width
          (← (translate_TLB_hit_pte sv_width asid vpn ac priv mxr do_sum ext_ptw ent 8 pte)))))

/-- Type quantifiers: k_ex591235_ : Bool, k_ex591234_ : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate_TLB_miss (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (base_ppn : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × Unit) (PTW_Error × Unit)) := do
  let initial_level :=
    if ((sv_width == 32) : Bool)
    then 1
    else
      (if ((sv_width == 39) : Bool)
      then 2
      else
        (if ((sv_width == 48) : Bool)
        then 3
        else 4))
  let pte_size :=
    if ((sv_width == 32) : Bool)
    then 4
    else 8
  let ptw_result ← do
    (pt_walk sv_width vpn ac priv mxr do_sum base_ppn initial_level false ext_ptw)
  match ptw_result with
  | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw)))
  | .Ok ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, global := global }, ext_ptw) =>
    (do
      let ext_pte := (ext_bits_of_PTE pte)
      match (update_PTE_Bits pte ac) with
      | none =>
        (do
          (add_to_TLB sv_width asid vpn ppn pte pteAddr level global)
          (pure (Ok (ppn, ext_ptw))))
      | .some pte =>
        (do
          if ((not plat_enable_dirty_update) : Bool)
          then (pure (Err ((PTW_PTE_Update ()), ext_ptw)))
          else
            (do
              match (← (write_pte pteAddr pte_size pte)) with
              | .Ok _ =>
                (do
                  (add_to_TLB sv_width asid vpn ppn pte pteAddr level global)
                  (pure (Ok (ppn, ext_ptw))))
              | .Err e => (pure (Err ((PTW_Access ()), ext_ptw))))))

def satp_mode_width_forwards (arg_ : SATPMode) : SailM Int := do
  match arg_ with
  | Sv32 => (pure 32)
  | Sv39 => (pure 39)
  | Sv48 => (pure 48)
  | Sv57 => (pure 57)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {32, 39, 48, 57} -/
def satp_mode_width_backwards (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 32 => Sv32
  | 39 => Sv39
  | 48 => Sv48
  | _ => Sv57

def satp_mode_width_forwards_matches (arg_ : SATPMode) : Bool :=
  match arg_ with
  | Sv32 => true
  | Sv39 => true
  | Sv48 => true
  | Sv57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, arg_ ∈ {32, 39, 48, 57} -/
def satp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 32 => true
  | 39 => true
  | 48 => true
  | 57 => true
  | _ => false

/-- Type quantifiers: k_ex591271_ : Bool, k_ex591270_ : Bool, sv_width : Nat, is_sv_mode(sv_width) -/
def translate (sv_width : Nat) (asid : (BitVec (if ( 64 = 32  : Bool) then 9 else 16))) (base_ppn : (BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (ac : (AccessType Unit)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32  : Bool) then 22 else 44)) × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vpn)) with
  | .some ent => (translate_TLB_hit sv_width asid vpn ac priv mxr do_sum ext_ptw ent)
  | none => (translate_TLB_miss sv_width asid base_ppn vpn ac priv mxr do_sum ext_ptw)

/-- Type quantifiers: sv_width : Nat, is_sv_mode(sv_width) -/
def get_satp (sv_width : Nat) : SailM (BitVec (if ( sv_width = 32  : Bool) then 32 else 64)) := do
  assert ((sv_width == 32) || (xlen == 64)) "sys/vmem.sail:391.30-391.31"
  let satp_width :=
    if ((sv_width == 32) : Bool)
    then 32
    else 64
  let satp_value ← do
    if ((sv_width == 32) : Bool)
    then (pure (BitVec.toNatInt (Sail.BitVec.extractLsb (← readReg satp) 31 0)))
    else (pure (BitVec.toNatInt (← readReg satp)))
  (pure (to_bits_truncate (l := satp_width) satp_value))

def translateAddr (vAddr : virtaddr) (ac : (AccessType Unit)) : SailM (Result (physaddr × Unit) (ExceptionType × Unit)) := do
  let effPriv ← do (effectivePrivilege ac (← readReg mstatus) (← readReg cur_privilege))
  let mode ← do (translationMode effPriv)
  if ((mode == Bare) : Bool)
  then (pure (Ok ((Physaddr (zero_extend (m := 64) (bits_of_virtaddr vAddr))), init_ext_ptw)))
  else
    (do
      let sv_width ← do (satp_mode_width_forwards mode)
      let satp_sxlen ← do (get_satp sv_width)
      assert ((sv_width == 32) || (xlen == 64)) "sys/vmem.sail:419.36-419.37"
      let svAddr := (Sail.BitVec.extractLsb (bits_of_virtaddr vAddr) (sv_width -i 1) 0)
      if (((bits_of_virtaddr vAddr) != (sign_extend (m := 64) svAddr)) : Bool)
      then (pure (Err ((translationException ac (PTW_Invalid_Addr ())), init_ext_ptw)))
      else
        (do
          let mxr ← do (pure ((_get_Mstatus_MXR (← readReg mstatus)) == 1#1))
          let do_sum ← do (pure ((_get_Mstatus_SUM (← readReg mstatus)) == 1#1))
          let asid := (satp_to_asid satp_sxlen)
          let base_ppn := (satp_to_ppn satp_sxlen)
          let res ← do
            (translate sv_width (zero_extend (m := 16) asid) base_ppn
              (Sail.BitVec.extractLsb svAddr (sv_width -i 1) pagesize_bits) ac effPriv mxr do_sum
              init_ext_ptw)
          match res with
          | .Ok (ppn, ext_ptw) =>
            (let paddr :=
              (ppn ++ (Sail.BitVec.extractLsb (bits_of_virtaddr vAddr) (pagesize_bits -i 1) 0))
            (pure (Ok ((Physaddr (zero_extend (m := 64) paddr)), ext_ptw))))
          | .Err (f, ext_ptw) => (pure (Err ((translationException ac f), ext_ptw)))))

def reset_vmem (_ : Unit) : SailM Unit := do
  (reset_TLB ())

