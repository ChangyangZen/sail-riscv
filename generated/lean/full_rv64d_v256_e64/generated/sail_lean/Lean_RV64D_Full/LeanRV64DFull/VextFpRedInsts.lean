import LeanRV64DFull.Flow
import LeanRV64DFull.Prelude
import LeanRV64DFull.Errors
import LeanRV64DFull.FdextRegs
import LeanRV64DFull.VextRegs
import LeanRV64DFull.VextControl
import LeanRV64DFull.InstRetire
import LeanRV64DFull.VextUtilsInsts
import LeanRV64DFull.VextFpUtilsInsts

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

def encdec_rfvvfunct6_forwards (arg_ : rfvvfunct6) : (BitVec 6) :=
  match arg_ with
  | FVV_VFREDOSUM => 0b000011#6
  | FVV_VFREDUSUM => 0b000001#6
  | FVV_VFREDMAX => 0b000111#6
  | FVV_VFREDMIN => 0b000101#6
  | FVV_VFWREDOSUM => 0b110011#6
  | FVV_VFWREDUSUM => 0b110001#6

def encdec_rfvvfunct6_backwards (arg_ : (BitVec 6)) : SailM rfvvfunct6 := do
  match arg_ with
  | 0b000011 => (pure FVV_VFREDOSUM)
  | 0b000001 => (pure FVV_VFREDUSUM)
  | 0b000111 => (pure FVV_VFREDMAX)
  | 0b000101 => (pure FVV_VFREDMIN)
  | 0b110011 => (pure FVV_VFWREDOSUM)
  | 0b110001 => (pure FVV_VFWREDUSUM)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_rfvvfunct6_forwards_matches (arg_ : rfvvfunct6) : Bool :=
  match arg_ with
  | FVV_VFREDOSUM => true
  | FVV_VFREDUSUM => true
  | FVV_VFREDMAX => true
  | FVV_VFREDMIN => true
  | FVV_VFWREDOSUM => true
  | FVV_VFWREDUSUM => true

def encdec_rfvvfunct6_backwards_matches (arg_ : (BitVec 6)) : Bool :=
  match arg_ with
  | 0b000011 => true
  | 0b000001 => true
  | 0b000111 => true
  | 0b000101 => true
  | 0b110011 => true
  | 0b110001 => true
  | _ => false

/-- Type quantifiers: LMUL_pow : Int, SEW : Nat, num_elem_vs : Nat, num_elem_vs > 0, SEW ∈
  {8, 16, 32, 64}, ((- 3)) ≤ LMUL_pow ∧ LMUL_pow ≤ 3 -/
def process_rfvv_single (funct6 : rfvvfunct6) (vm : (BitVec 1)) (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) (num_elem_vs : Nat) (SEW : Nat) (LMUL_pow : Int) : SailM ExecutionResult := SailME.run do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let num_elem_vd ← do (get_num_elem 0 SEW)
  if ((← (illegal_fp_reduction SEW rm_3b)) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      assert (SEW != 8) "extensions/V/vext_fp_red_insts.sail:36.17-36.18"
      if (((BitVec.toNatInt (← readReg vl)) == 0) : Bool)
      then (pure RETIRE_SUCCESS)
      else
        (do
          if ((SEW == 16) : Bool)
          then
            (do
              let sum ← (( do (read_single_element 16 0 vs1) ) : SailME ExecutionResult
                (BitVec 16) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := (num_elem_vs -i 1)
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let active ← (( do
                      match (← (is_active_vector_element num_elem_vs LMUL_pow vm i)) with
                      | .Ok v => (pure v)
                      | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) :
                      SailME ExecutionResult Bool )
                    if (active : Bool)
                    then
                      (do
                        let elem ← (( do (read_single_element 16 i vs2) ) : SailME ExecutionResult
                          (BitVec 16) )
                        match funct6 with
                        | FVV_VFREDOSUM => (fp_add rm_3b sum elem)
                        | FVV_VFREDUSUM => (fp_add rm_3b sum elem)
                        | FVV_VFREDMAX => (fp_max sum elem)
                        | FVV_VFREDMIN => (fp_min sum elem)
                        | _ =>
                          (internal_error "extensions/V/vext_fp_red_insts.sail" 55
                            "Widening op unexpected"))
                    else (pure sum)
                (pure loop_vars_2) ) : SailME ExecutionResult (BitVec 16) )
              (write_single_element 16 0 vd sum))
          else
            (do
              if ((SEW == 32) : Bool)
              then
                (do
                  let sum ← (( do (read_single_element 32 0 vs1) ) : SailME ExecutionResult
                    (BitVec 32) )
                  let sum ← (( do
                    let loop_i_lower := 0
                    let loop_i_upper := (num_elem_vs -i 1)
                    let mut loop_vars_1 := sum
                    for i in [loop_i_lower:loop_i_upper:1]i do
                      let sum := loop_vars_1
                      loop_vars_1 ← do
                        let active ← (( do
                          match (← (is_active_vector_element num_elem_vs LMUL_pow vm i)) with
                          | .Ok v => (pure v)
                          | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) :
                          SailME ExecutionResult Bool )
                        if (active : Bool)
                        then
                          (do
                            let elem ← (( do (read_single_element 32 i vs2) ) : SailME
                              ExecutionResult (BitVec 32) )
                            match funct6 with
                            | FVV_VFREDOSUM => (fp_add rm_3b sum elem)
                            | FVV_VFREDUSUM => (fp_add rm_3b sum elem)
                            | FVV_VFREDMAX => (fp_max sum elem)
                            | FVV_VFREDMIN => (fp_min sum elem)
                            | _ =>
                              (internal_error "extensions/V/vext_fp_red_insts.sail" 75
                                "Widening op unexpected"))
                        else (pure sum)
                    (pure loop_vars_1) ) : SailME ExecutionResult (BitVec 32) )
                  (write_single_element 32 0 vd sum))
              else
                (do
                  let sum ← (( do (read_single_element 64 0 vs1) ) : SailME ExecutionResult
                    (BitVec 64) )
                  let sum ← (( do
                    let loop_i_lower := 0
                    let loop_i_upper := (num_elem_vs -i 1)
                    let mut loop_vars := sum
                    for i in [loop_i_lower:loop_i_upper:1]i do
                      let sum := loop_vars
                      loop_vars ← do
                        let active ← (( do
                          match (← (is_active_vector_element num_elem_vs LMUL_pow vm i)) with
                          | .Ok v => (pure v)
                          | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) :
                          SailME ExecutionResult Bool )
                        if (active : Bool)
                        then
                          (do
                            let elem ← (( do (read_single_element 64 i vs2) ) : SailME
                              ExecutionResult (BitVec 64) )
                            match funct6 with
                            | FVV_VFREDOSUM => (fp_add rm_3b sum elem)
                            | FVV_VFREDUSUM => (fp_add rm_3b sum elem)
                            | FVV_VFREDMAX => (fp_max sum elem)
                            | FVV_VFREDMIN => (fp_min sum elem)
                            | _ =>
                              (internal_error "extensions/V/vext_fp_red_insts.sail" 95
                                "Widening op unexpected"))
                        else (pure sum)
                    (pure loop_vars) ) : SailME ExecutionResult (BitVec 64) )
                  (write_single_element 64 0 vd sum)))
          (set_vstart (zeros (n := 16)))
          (pure RETIRE_SUCCESS)))

/-- Type quantifiers: LMUL_pow : Int, SEW : Nat, num_elem_vs : Nat, num_elem_vs > 0, SEW ∈
  {8, 16, 32, 64}, ((- 3)) ≤ LMUL_pow ∧ LMUL_pow ≤ 3 -/
def process_rfvv_widening_reduction (funct6 : rfvvfunct6) (vm : (BitVec 1)) (vs2 : vregidx) (vs1 : vregidx) (vd : vregidx) (num_elem_vs : Nat) (SEW : Nat) (LMUL_pow : Int) : SailM ExecutionResult := SailME.run do
  let rm_3b ← do (pure (_get_Fcsr_FRM (← readReg fcsr)))
  let SEW_widen := (SEW *i 2)
  if ((← (illegal_fp_widening_reduction SEW rm_3b SEW_widen)) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      assert ((SEW ≥b 16) && (SEW_widen ≤b 64)) "extensions/V/vext_fp_red_insts.sail:113.36-113.37"
      let num_elem_vd ← do (get_num_elem 0 SEW_widen)
      if (((BitVec.toNatInt (← readReg vl)) == 0) : Bool)
      then (pure RETIRE_SUCCESS)
      else
        (do
          if ((SEW == 16) : Bool)
          then
            (do
              let sum ← (( do (read_single_element 32 0 vs1) ) : SailME ExecutionResult
                (BitVec 32) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := (num_elem_vs -i 1)
                let mut loop_vars_1 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_1
                  loop_vars_1 ← do
                    let active ← (( do
                      match (← (is_active_vector_element num_elem_vs LMUL_pow vm i)) with
                      | .Ok v => (pure v)
                      | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) :
                      SailME ExecutionResult Bool )
                    if (active : Bool)
                    then
                      (do
                        let elem ← (( do (read_single_element 16 i vs2) ) : SailME ExecutionResult
                          (BitVec 16) )
                        (fp_add rm_3b sum (← (fp_widen elem))))
                    else (pure sum)
                (pure loop_vars_1) ) : SailME ExecutionResult (BitVec 32) )
              (write_single_element 32 0 vd sum))
          else
            (do
              let sum ← (( do (read_single_element 64 0 vs1) ) : SailME ExecutionResult
                (BitVec 64) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := (num_elem_vs -i 1)
                let mut loop_vars := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars
                  loop_vars ← do
                    let active ← (( do
                      match (← (is_active_vector_element num_elem_vs LMUL_pow vm i)) with
                      | .Ok v => (pure v)
                      | .Err () => SailME.throw ((Illegal_Instruction ()) : ExecutionResult) ) :
                      SailME ExecutionResult Bool )
                    if (active : Bool)
                    then
                      (do
                        let elem ← (( do (read_single_element 32 i vs2) ) : SailME ExecutionResult
                          (BitVec 32) )
                        (fp_add rm_3b sum (← (fp_widen elem))))
                    else (pure sum)
                (pure loop_vars) ) : SailME ExecutionResult (BitVec 64) )
              (write_single_element 64 0 vd sum))
          (set_vstart (zeros (n := 16)))
          (pure RETIRE_SUCCESS)))

def rfvvtype_mnemonic_backwards (arg_ : String) : SailM rfvvfunct6 := do
  match arg_ with
  | "vfredosum.vs" => (pure FVV_VFREDOSUM)
  | "vfredusum.vs" => (pure FVV_VFREDUSUM)
  | "vfredmax.vs" => (pure FVV_VFREDMAX)
  | "vfredmin.vs" => (pure FVV_VFREDMIN)
  | "vfwredosum.vs" => (pure FVV_VFWREDOSUM)
  | "vfwredusum.vs" => (pure FVV_VFWREDUSUM)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def rfvvtype_mnemonic_forwards_matches (arg_ : rfvvfunct6) : Bool :=
  match arg_ with
  | FVV_VFREDOSUM => true
  | FVV_VFREDUSUM => true
  | FVV_VFREDMAX => true
  | FVV_VFREDMIN => true
  | FVV_VFWREDOSUM => true
  | FVV_VFWREDUSUM => true

def rfvvtype_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "vfredosum.vs" => true
  | "vfredusum.vs" => true
  | "vfredmax.vs" => true
  | "vfredmin.vs" => true
  | "vfwredosum.vs" => true
  | "vfwredusum.vs" => true
  | _ => false

