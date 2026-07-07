import LeanCV32E40PRV32IMC.Prelude
import LeanCV32E40PRV32IMC.Types
import LeanCV32E40PRV32IMC.SysRegs
import LeanCV32E40PRV32IMC.SysControl
import LeanCV32E40PRV32IMC.Platform
import LeanCV32E40PRV32IMC.VmemTlb
import LeanCV32E40PRV32IMC.Step
import LeanCV32E40PRV32IMC.Main

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

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : SailM Unit := do
  writeReg misa (_update_Misa_MXL (Mk_Misa (zeros (n := 32))) (architecture_bits_forwards RV32))
  writeReg mstatus (let mxl := (architecture_bits_forwards RV32)
  (_update_Mstatus_UXL (_update_Mstatus_SXL (Mk_Mstatus (zeros (n := 64))) (zeros (n := 2)))
    (zeros (n := 2))))
  writeReg senvcfg (← (legalize_senvcfg (Mk_SEnvcfg (zeros (n := 32))) (zeros (n := 32))))
  writeReg mseccfg (← (legalize_mseccfg (Mk_Seccfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg menvcfg (← (legalize_menvcfg (Mk_MEnvcfg (zeros (n := 64))) (zeros (n := 64))))
  writeReg mvendorid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mimpid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg marchid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mhartid (← (to_bits_checked (l := 32) (0 : Int)))
  writeReg mconfigptr (zeros (n := 32))
  writeReg pc_reset_address (zeros (n := 32))
  writeReg plat_ram_base (← (to_bits_checked (l := 34) (2147483648 : Int)))
  writeReg plat_ram_size (← (to_bits_checked (l := 34) (2147483648 : Int)))
  writeReg plat_rom_base (← (to_bits_checked (l := 34) (4096 : Int)))
  writeReg plat_rom_size (← (to_bits_checked (l := 34) (4096 : Int)))
  writeReg plat_clint_base (← (to_bits_checked (l := 34) (33554432 : Int)))
  writeReg plat_clint_size (← (to_bits_checked (l := 34) (786432 : Int)))
  writeReg htif_tohost_base none
  writeReg tlb (vectorInit none)
  writeReg hart_state (HART_ACTIVE ())
  (pure (initialize_registers ()))

end LeanCV32E40PRV32IMC.Functions

open LeanCV32E40PRV32IMC.Functions

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default, default⟩ (sail_model_init >=> sail_main)
