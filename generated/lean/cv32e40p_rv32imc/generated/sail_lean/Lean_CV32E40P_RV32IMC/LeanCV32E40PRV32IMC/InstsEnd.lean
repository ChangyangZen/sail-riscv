import LeanCV32E40PRV32IMC.Flow
import LeanCV32E40PRV32IMC.Prelude
import LeanCV32E40PRV32IMC.Errors
import LeanCV32E40PRV32IMC.Xlen
import LeanCV32E40PRV32IMC.Types
import LeanCV32E40PRV32IMC.VmemTypes
import LeanCV32E40PRV32IMC.Regs
import LeanCV32E40PRV32IMC.PcAccess
import LeanCV32E40PRV32IMC.SysRegs
import LeanCV32E40PRV32IMC.SysExceptions
import LeanCV32E40PRV32IMC.ZicfilpRegs
import LeanCV32E40PRV32IMC.SysControl
import LeanCV32E40PRV32IMC.InstRetire
import LeanCV32E40PRV32IMC.VmemTlb
import LeanCV32E40PRV32IMC.VmemUtils
import LeanCV32E40PRV32IMC.ZicfilpInsts
import LeanCV32E40PRV32IMC.BaseInsts
import LeanCV32E40PRV32IMC.MextInsts
import LeanCV32E40PRV32IMC.ZicsrInsts

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

noncomputable def encdec_forwards (arg_ : instruction) : SailM (BitVec 32) := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure ((lpl : (BitVec 20)) ++ (0b00000#5 ++ 0b0010111#7)))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .UTYPE (imm, rd, op) =>
    (pure ((imm : (BitVec 20)) ++ ((encdec_reg_forwards rd) ++ (encdec_uop_forwards op))))
  | .JAL (v__10, rd) =>
    (do
      if (((Sail.BitVec.extractLsb v__10 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__10 20 20)
        let imm_8 : (BitVec 1) := (Sail.BitVec.extractLsb v__10 11 11)
        let imm_7_0 : (BitVec 8) := (Sail.BitVec.extractLsb v__10 19 12)
        let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__10 20 20)
        let imm_18_13 : (BitVec 6) := (Sail.BitVec.extractLsb v__10 10 5)
        let imm_12_9 : (BitVec 4) := (Sail.BitVec.extractLsb v__10 4 1)
        (pure ((imm_19 : (BitVec 1)) ++ ((imm_18_13 : (BitVec 6)) ++ ((imm_12_9 : (BitVec 4)) ++ ((imm_8 : (BitVec 1)) ++ ((imm_7_0 : (BitVec 8)) ++ ((encdec_reg_forwards
                        rd) ++ 0b1101111#7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .JALR (imm, rs1, rd) =>
    (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards rd) ++ 0b1100111#7)))))
  | .BTYPE (v__12, rs2, rs1, op) =>
    (do
      if (((Sail.BitVec.extractLsb v__12 0 0) == (0#1 : (BitVec 1))) : Bool)
      then
        (let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__12 12 12)
        let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__12 12 12)
        let imm7_5_0 : (BitVec 6) := (Sail.BitVec.extractLsb v__12 10 5)
        let imm5_4_1 : (BitVec 4) := (Sail.BitVec.extractLsb v__12 4 1)
        let imm5_0 : (BitVec 1) := (Sail.BitVec.extractLsb v__12 11 11)
        (pure ((imm7_6 : (BitVec 1)) ++ ((imm7_5_0 : (BitVec 6)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards
                    rs1) ++ ((encdec_bop_forwards op) ++ ((imm5_4_1 : (BitVec 4)) ++ ((imm5_0 : (BitVec 1)) ++ 0b1100011#7)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ITYPE (imm, rs1, rd, op) =>
    (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((encdec_iop_forwards op) ++ ((encdec_reg_forwards
                rd) ++ 0b0010011#7)))))
  | .SHIFTIOP (shamt, rs1, rd, SLLI) =>
    (do
      if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
      then
        (pure (0b000000#6 ++ ((shamt : (BitVec 6)) ++ ((encdec_reg_forwards rs1) ++ (0b001#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0010011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIOP (shamt, rs1, rd, SRLI) =>
    (do
      if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
      then
        (pure (0b000000#6 ++ ((shamt : (BitVec 6)) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0010011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIOP (shamt, rs1, rd, SRAI) =>
    (do
      if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
      then
        (pure (0b010000#6 ++ ((shamt : (BitVec 6)) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0010011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPE (rs2, rs1, rd, ADD) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, SLT) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b010#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, SLTU) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b011#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, AND) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b111#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, OR) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b110#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, XOR) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b100#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, SLL) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b001#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, SRL) =>
    (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, SUB) =>
    (pure (0b0100000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .RTYPE (rs2, rs1, rd, SRA) =>
    (pure (0b0100000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                  rd) ++ 0b0110011#7))))))
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (do
      if ((valid_load_encdec width is_unsigned) : Bool)
      then
        (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ ((bool_bits_forwards is_unsigned) ++ ((width_enc_forwards
                    width) ++ ((encdec_reg_forwards rd) ++ 0b0000011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .STORE (v__14, rs2, rs1, width) =>
    (do
      if ((width ≤b xlen_bytes) : Bool)
      then
        (let imm7 : (BitVec 7) := (Sail.BitVec.extractLsb v__14 11 5)
        let imm7 : (BitVec 7) := (Sail.BitVec.extractLsb v__14 11 5)
        let imm5 : (BitVec 5) := (Sail.BitVec.extractLsb v__14 4 0)
        (pure ((imm7 : (BitVec 7)) ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0#1 ++ ((width_enc_forwards
                      width) ++ ((imm5 : (BitVec 5)) ++ 0b0100011#7))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ADDIW (imm, rs1, rd) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards
                    rd) ++ 0b0011011#7)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, ADDW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SUBW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0100000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SLLW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b001#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SRLW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .RTYPEW (rs2, rs1, rd, SRAW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0100000#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, SLLIW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 ++ ((shamt : (BitVec 5)) ++ ((encdec_reg_forwards rs1) ++ (0b001#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0011011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, SRLIW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0000000#7 ++ ((shamt : (BitVec 5)) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0011011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .SHIFTIWOP (shamt, rs1, rd, SRAIW) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (pure (0b0100000#7 ++ ((shamt : (BitVec 5)) ++ ((encdec_reg_forwards rs1) ++ (0b101#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0011011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE (pred, succ) =>
    (pure (0b0000#4 ++ ((pred : (BitVec 4)) ++ ((succ : (BitVec 4)) ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b0001111#7)))))))
  | .FENCE_TSO () =>
    (pure (0b1000#4 ++ (0b0011#4 ++ (0b0011#4 ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b0001111#7)))))))
  | .ECALL () =>
    (pure (0b000000000000#12 ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b1110011#7)))))
  | .MRET () =>
    (pure (0b0011000#7 ++ (0b00010#5 ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b1110011#7))))))
  | .SRET () =>
    (pure (0b0001000#7 ++ (0b00010#5 ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b1110011#7))))))
  | .EBREAK () =>
    (pure (0b000000000001#12 ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b1110011#7)))))
  | .WFI () => (pure (0b000100000101#12 ++ (0b00000#5 ++ (0b000#3 ++ (0b00000#5 ++ 0b1110011#7)))))
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then
        (pure (0b0001001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ (0b00000#5 ++ 0b1110011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCE_RESERVED (fm, pred, succ, rs, rd) =>
    (do
      if ((((fm != 0b0000#4) && (fm != 0b1000#4)) || ((bne rs zreg) || (bne rd zreg))) : Bool)
      then
        (pure ((fm : (BitVec 4)) ++ ((pred : (BitVec 4)) ++ ((succ : (BitVec 4)) ++ ((encdec_reg_forwards
                    rs) ++ (0b000#3 ++ ((encdec_reg_forwards rd) ++ 0b0001111#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCEI_RESERVED (imm, rs, rd) =>
    (do
      if (((imm != 0b000000000000#12) || ((bne rs zreg) || (bne rd zreg))) : Bool)
      then
        (pure ((imm : (BitVec 12)) ++ ((encdec_reg_forwards rs) ++ (0b001#3 ++ ((encdec_reg_forwards
                    rd) ++ 0b0001111#7)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      if (((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))) : Bool)
      then
        (pure (0b0000001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ ((← (encdec_mul_op_forwards
                      mul_op)) ++ ((encdec_reg_forwards rd) ++ 0b0110011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b10#2 ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ 0b0110011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then
        (pure (0b0000001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b11#2 ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ 0b0110011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .MULW (rs2, rs1, rd) =>
    (do
      if (((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))) : Bool)
      then
        (pure (0b0000001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b000#3 ++ ((encdec_reg_forwards
                      rd) ++ 0b0111011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then
        (pure (0b0000001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b10#2 ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ 0b0111011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then
        (pure (0b0000001#7 ++ ((encdec_reg_forwards rs2) ++ ((encdec_reg_forwards rs1) ++ (0b11#2 ++ ((bool_bits_forwards
                      is_unsigned) ++ ((encdec_reg_forwards rd) ++ 0b0111011#7)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then
        (pure ((csr : (BitVec 12)) ++ ((encdec_reg_forwards rs1) ++ (0#1 ++ ((encdec_csrop_forwards
                    op) ++ ((encdec_reg_forwards rd) ++ 0b1110011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then
        (pure ((csr : (BitVec 12)) ++ ((imm : (BitVec 5)) ++ (1#1 ++ ((encdec_csrop_forwards op) ++ ((encdec_reg_forwards
                      rd) ++ 0b1110011#7))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .FENCEI () =>
    (do
      if ((← (currentlyEnabled Ext_Zifencei)) : Bool)
      then (pure (0b000000000000#12 ++ (0b00000#5 ++ (0b001#3 ++ (0b00000#5 ++ 0b0001111#7)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

noncomputable def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__208 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__208 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then
      (let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__208 31 12)
      let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__208 31 12)
      (pure (some (LPAD lpl))))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__208 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__208 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__208 31 12)
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__208 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__208 11 7)
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__208 31 12)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__206 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__206 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__206 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__206 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__206 11 7)
            let imm_8 : (BitVec 1) := (Sail.BitVec.extractLsb v__206 20 20)
            let imm_7_0 : (BitVec 8) := (Sail.BitVec.extractLsb v__206 19 12)
            let imm_19 : (BitVec 1) := (Sail.BitVec.extractLsb v__206 31 31)
            let imm_18_13 : (BitVec 6) := (Sail.BitVec.extractLsb v__206 30 25)
            let imm_12_9 : (BitVec 4) := (Sail.BitVec.extractLsb v__206 24 21)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (JAL
                    (((imm_19 : (BitVec 1)) ++ ((imm_7_0 : (BitVec 8)) ++ ((imm_8 : (BitVec 1)) ++ ((imm_18_13 : (BitVec 6)) ++ ((imm_12_9 : (BitVec 4)) ++ 0#1))))), rd)))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__203 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__203 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__203 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__203 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__203 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__203 31 20)
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__203 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__203 19 15)
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__203 31 20)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some (JALR (imm, rs1, rd)))))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__201 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__201 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__201 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__201 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__201 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__201 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__201 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__201 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__201 24 20)
                    let imm7_6 : (BitVec 1) := (Sail.BitVec.extractLsb v__201 31 31)
                    let imm7_5_0 : (BitVec 6) := (Sail.BitVec.extractLsb v__201 30 25)
                    let imm5_4_1 : (BitVec 4) := (Sail.BitVec.extractLsb v__201 11 8)
                    let imm5_0 : (BitVec 1) := (Sail.BitVec.extractLsb v__201 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (BTYPE
                            (((imm7_6 : (BitVec 1)) ++ ((imm5_0 : (BitVec 1)) ++ ((imm7_5_0 : (BitVec 6)) ++ ((imm5_4_1 : (BitVec 4)) ++ 0#1)))), rs2, rs1, op)))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__199 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__199 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__199 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__199 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__199 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__199 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__199 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__199 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__199 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__199 31 20)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__195 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__195 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__195 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__195 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__195 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__195 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__195 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__195 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__195 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some (SHIFTIOP (shamt, rs1, rd, SLLI))))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__191 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__191 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__191 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__191 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__191 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__191 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__191 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__191 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__191 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some (SHIFTIOP (shamt, rs1, rd, SRLI))))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__187 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__187 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__187 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__187 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__187 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__187 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__187 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__187 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__187 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some (SHIFTIOP (shamt, rs1, rd, SRAI))))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__183 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__183 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__183 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__183 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__183 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__183 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__183 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__183 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__183 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__183 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) =>
                                          (pure (some (RTYPE (rs2, rs1, rd, ADD)))))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__179 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__179 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__179 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__179 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__179 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__179 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__179 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__179 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__179 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__179 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) =>
                                              (pure (some (RTYPE (rs2, rs1, rd, SLT)))))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__175 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__175 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__175 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__175 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__175 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__175 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__175 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__175 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__175 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__175 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) =>
                                                  (pure (some (RTYPE (rs2, rs1, rd, SLTU)))))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__171 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__171 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__171 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__171 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__171 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__171 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__171 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__171 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__171 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__171 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) =>
                                                      (pure (some (RTYPE (rs2, rs1, rd, AND)))))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__167 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__167 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__167 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__167 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__167 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__167 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__167 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__167 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__167 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__167 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) =>
                                                          (pure (some (RTYPE (rs2, rs1, rd, OR)))))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__163 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__163 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__163 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__163 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__163 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__163 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__163 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__163 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__163 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__163 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) =>
                                                              (pure (some
                                                                  (RTYPE (rs2, rs1, rd, XOR)))))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__159 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__159 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__159 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__159 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__159 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__159 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__159 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__159 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__159 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__159 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some
                                                                      (RTYPE (rs2, rs1, rd, SLL)))))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__155 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__155 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__155 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__155 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__155 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__155 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__155 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__155
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__155
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__155
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some
                                                                          (RTYPE (rs2, rs1, rd, SRL)))))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__151 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__151 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__151 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__151 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__151 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__151 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__151 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__151 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__151 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__151 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some
                                                                              (RTYPE
                                                                                (rs2, rs1, rd, SUB)))))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__147 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__147 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__147 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__147 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__147 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__147 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__147 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__147 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__147 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__147 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some
                                                                                  (RTYPE
                                                                                    (rs2, rs1, rd, SRA)))))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__145 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__145 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__145 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__145 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__145 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bits_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__145 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__145 31 20)
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__145 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__145 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__145 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__145 19 15)
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__145 31 20)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bits_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some
                                                                                        (LOAD
                                                                                          (imm, rs1, rd, is_unsigned, width))))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__142 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__142 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__142 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__142 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__142 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__142 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm7 : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__142 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__142 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__142 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__142 24 20)
                                                                                    let imm7 : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__142 31 25)
                                                                                    let imm5 : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__142 11 7)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((width ≤b xlen_bytes) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (STORE
                                                                                              (((imm7 : (BitVec 7)) ++ (imm5 : (BitVec 5))), rs2, rs1, width))))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__139 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__139
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__139
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__139
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__139
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__139
                                                                                            31 20)
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__139
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__139
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__139
                                                                                            31 20)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                (ADDIW
                                                                                                  (imm, rs1, rd))))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__135 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__135
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__135
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__135
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__135
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__135
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__135
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__135
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__135
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__135
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    (RTYPEW
                                                                                                      (rs2, rs1, rd, ADDW))))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__131 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__131
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__131
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__131
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__131
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__131
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__131
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__131
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__131
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__131
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        (RTYPEW
                                                                                                          (rs2, rs1, rd, SUBW))))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__127 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__127
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__127
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__127
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__127
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__127
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__127
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__127
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__127
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__127
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            (RTYPEW
                                                                                                              (rs2, rs1, rd, SLLW))))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__123 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__123
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__123
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__123
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__123
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__123
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__123
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__123
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__123
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__123
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                (RTYPEW
                                                                                                                  (rs2, rs1, rd, SRLW))))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__119 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__119
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__119
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__119
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__119
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__119
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__119
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__119
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__119
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__119
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    (RTYPEW
                                                                                                                      (rs2, rs1, rd, SRAW))))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__115 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__115
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__115
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__115
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__115
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__115
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__115
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__115
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__115
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        (SHIFTIWOP
                                                                                                                          (shamt, rs1, rd, SLLIW))))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__111 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__111
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__111
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__111
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__111
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__111
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__111
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__111
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__111
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            (SHIFTIWOP
                                                                                                                              (shamt, rs1, rd, SRLIW))))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__107 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__107
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__107
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__107
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__107
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__107
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__107
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__107
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__107
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                (SHIFTIWOP
                                                                                                                                  (shamt, rs1, rd, SRAIW))))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__56 :=
                                                                                                                          head_exp_
                                                                                                                        if ((((Sail.BitVec.extractLsb
                                                                                                                                 v__56
                                                                                                                                 31
                                                                                                                                 28) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__56
                                                                                                                                 19
                                                                                                                                 0) == (0x0000F#20 : (BitVec 20)))) : Bool)
                                                                                                                        then
                                                                                                                          (let succ : (BitVec 4) :=
                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                              v__56
                                                                                                                              23
                                                                                                                              20)
                                                                                                                          let pred : (BitVec 4) :=
                                                                                                                            (Sail.BitVec.extractLsb
                                                                                                                              v__56
                                                                                                                              27
                                                                                                                              24)
                                                                                                                          (pure (some
                                                                                                                              (FENCE
                                                                                                                                (pred, succ)))))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if ((v__56 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  (FENCE_TSO
                                                                                                                                    ())))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__56 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (ECALL
                                                                                                                                        ())))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__56 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (MRET
                                                                                                                                            ())))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__56 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (SRET
                                                                                                                                                ())))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__56 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (EBREAK
                                                                                                                                                    ())))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if ((v__56 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (WFI
                                                                                                                                                        ())))
                                                                                                                                                else
                                                                                                                                                  (do
                                                                                                                                                    if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__56
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping77_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__56
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__56
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                               v__56
                                                                                                                                                               14
                                                                                                                                                               0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping78_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__56
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping77_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__56
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping77_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping78_))) with
                                                                                                                                                        | (rs2, rs1) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((← (virtual_memory_supported
                                                                                                                                                                     ())) || (not
                                                                                                                                                                   (true : Bool))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  (SFENCE_VMA
                                                                                                                                                                    (rs1, rs2))))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none))))))))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__53 :=
                                                                                                                              head_exp_
                                                                                                                            if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__53
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping79_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__53
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__53
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__53
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__53
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let succ : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__53
                                                                                                                                    23
                                                                                                                                    20)
                                                                                                                                let pred : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__53
                                                                                                                                    27
                                                                                                                                    24)
                                                                                                                                let mapping80_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__53
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping79_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__53
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__53
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping79_)), (← (encdec_reg_backwards
                                                                                                                                    mapping80_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (if ((((fm != 0b0000#4) && (fm != 0b1000#4)) || ((bne
                                                                                                                                           rs
                                                                                                                                           zreg) || (bne
                                                                                                                                           rd
                                                                                                                                           zreg))) : Bool)
                                                                                                                                  then
                                                                                                                                    (pure (some
                                                                                                                                        (FENCE_RESERVED
                                                                                                                                          (fm, pred, succ, rs, rd))))
                                                                                                                                  else
                                                                                                                                    (pure none)))
                                                                                                                            else
                                                                                                                              (pure none)) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__50 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__50
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__50
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && (encdec_reg_backwards_matches
                                                                                                                                         mapping82_))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__50
                                                                                                                                           14
                                                                                                                                           12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__50
                                                                                                                                           6
                                                                                                                                           0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let imm : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__50
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__50
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__50
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let imm : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__50
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_reg_backwards
                                                                                                                                        mapping82_))) with
                                                                                                                                    | (rs, rd) =>
                                                                                                                                      (if (((imm != 0b000000000000#12) || ((bne
                                                                                                                                               rs
                                                                                                                                               zreg) || (bne
                                                                                                                                               rd
                                                                                                                                               zreg))) : Bool)
                                                                                                                                      then
                                                                                                                                        (pure (some
                                                                                                                                            (FENCEI_RESERVED
                                                                                                                                              (imm, rs, rd))))
                                                                                                                                      else
                                                                                                                                        (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__47 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__47
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping85_ : (BitVec 3) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__47
                                                                                                                                             14
                                                                                                                                             12)
                                                                                                                                         let mapping84_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__47
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping83_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__47
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping83_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping84_) && ((encdec_mul_op_backwards_matches
                                                                                                                                                 mapping85_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping86_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__47
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                               v__47
                                                                                                                                               6
                                                                                                                                               0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__47
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping85_ : (BitVec 3) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__47
                                                                                                                                            14
                                                                                                                                            12)
                                                                                                                                        let mapping84_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__47
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping83_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__47
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                            mapping83_)), (← (encdec_reg_backwards
                                                                                                                                            mapping84_)), (← (encdec_mul_op_backwards
                                                                                                                                            mapping85_)), (← (encdec_reg_backwards
                                                                                                                                            mapping86_))) with
                                                                                                                                        | (rs2, rs1, mul_op, rd) =>
                                                                                                                                          (do
                                                                                                                                            if (((← (currentlyEnabled
                                                                                                                                                     Ext_M)) || (← (currentlyEnabled
                                                                                                                                                     Ext_Zmmul))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (MUL
                                                                                                                                                    (rs2, rs1, rd, mul_op))))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__43 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__43
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping89_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__43
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping88_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__43
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping87_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__43
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping87_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping88_) && ((bool_bits_backwards_matches
                                                                                                                                                     mapping89_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping90_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__43
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__43
                                                                                                                                                     14
                                                                                                                                                     13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__43
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__43
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping89_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__43
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping88_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__43
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping87_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__43
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                mapping87_)), (← (encdec_reg_backwards
                                                                                                                                                mapping88_)), (bool_bits_backwards
                                                                                                                                              mapping89_), (← (encdec_reg_backwards
                                                                                                                                                mapping90_))) with
                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_M)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (DIV
                                                                                                                                                        (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__39 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__39
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping93_ : (BitVec 1) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__39
                                                                                                                                                     12
                                                                                                                                                     12)
                                                                                                                                                 let mapping92_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__39
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping91_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__39
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping91_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping92_) && ((bool_bits_backwards_matches
                                                                                                                                                         mapping93_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping94_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__39
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__39
                                                                                                                                                         14
                                                                                                                                                         13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__39
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__39
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping93_ : (BitVec 1) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__39
                                                                                                                                                    12
                                                                                                                                                    12)
                                                                                                                                                let mapping92_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__39
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping91_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__39
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                    mapping91_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping92_)), (bool_bits_backwards
                                                                                                                                                  mapping93_), (← (encdec_reg_backwards
                                                                                                                                                    mapping94_))) with
                                                                                                                                                | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                           Ext_M)) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          (REM
                                                                                                                                                            (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__35 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__35
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__35
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping95_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__35
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping95_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping96_) && (encdec_reg_backwards_matches
                                                                                                                                                           mapping97_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__35
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__35
                                                                                                                                                             14
                                                                                                                                                             12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__35
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__35
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__35
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping95_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__35
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping95_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping96_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping97_))) with
                                                                                                                                                    | (rs2, rs1, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                                   Ext_M)) || (← (currentlyEnabled
                                                                                                                                                                   Ext_Zmmul)))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (MULW
                                                                                                                                                                (rs2, rs1, rd))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (do
                                                                                                                                                  match (← do
                                                                                                                                                    let v__31 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__31
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping98_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__31
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__31
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping100_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__31
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping98_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping99_) && ((bool_bits_backwards_matches
                                                                                                                                                                 mapping100_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping101_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__31
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__31
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__31
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping99_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__31
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping98_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__31
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__31
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping100_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__31
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping98_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping99_)), (bool_bits_backwards
                                                                                                                                                          mapping100_), (← (encdec_reg_backwards
                                                                                                                                                            mapping101_))) with
                                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                     Ext_M))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  (DIVW
                                                                                                                                                                    (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none)) with
                                                                                                                                                  | .some result =>
                                                                                                                                                    (pure result)
                                                                                                                                                  | none =>
                                                                                                                                                    (do
                                                                                                                                                      match (← do
                                                                                                                                                        let v__27 :=
                                                                                                                                                          head_exp_
                                                                                                                                                        if (((let mapping105_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__27
                                                                                                                                                                 11
                                                                                                                                                                 7)
                                                                                                                                                             let mapping104_ : (BitVec 1) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__27
                                                                                                                                                                 12
                                                                                                                                                                 12)
                                                                                                                                                             let mapping103_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__27
                                                                                                                                                                 19
                                                                                                                                                                 15)
                                                                                                                                                             let mapping102_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__27
                                                                                                                                                                 24
                                                                                                                                                                 20)
                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                 mapping102_) && ((encdec_reg_backwards_matches
                                                                                                                                                                   mapping103_) && ((bool_bits_backwards_matches
                                                                                                                                                                     mapping104_) && (encdec_reg_backwards_matches
                                                                                                                                                                     mapping105_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                   v__27
                                                                                                                                                                   31
                                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                     v__27
                                                                                                                                                                     14
                                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                     v__27
                                                                                                                                                                     6
                                                                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let mapping105_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__27
                                                                                                                                                                11
                                                                                                                                                                7)
                                                                                                                                                            let mapping104_ : (BitVec 1) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__27
                                                                                                                                                                12
                                                                                                                                                                12)
                                                                                                                                                            let mapping103_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__27
                                                                                                                                                                19
                                                                                                                                                                15)
                                                                                                                                                            let mapping102_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__27
                                                                                                                                                                24
                                                                                                                                                                20)
                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                mapping102_)), (← (encdec_reg_backwards
                                                                                                                                                                mapping103_)), (bool_bits_backwards
                                                                                                                                                              mapping104_), (← (encdec_reg_backwards
                                                                                                                                                                mapping105_))) with
                                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                              (do
                                                                                                                                                                if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                         Ext_M))) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (pure (some
                                                                                                                                                                      (REMW
                                                                                                                                                                        (rs2, rs1, rd, is_unsigned))))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)))
                                                                                                                                                        else
                                                                                                                                                          (pure none)) with
                                                                                                                                                      | .some result =>
                                                                                                                                                        (pure result)
                                                                                                                                                      | none =>
                                                                                                                                                        (do
                                                                                                                                                          match (← do
                                                                                                                                                            let v__24 :=
                                                                                                                                                              head_exp_
                                                                                                                                                            if (((let mapping108_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__24
                                                                                                                                                                     11
                                                                                                                                                                     7)
                                                                                                                                                                 let mapping107_ : (BitVec 2) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__24
                                                                                                                                                                     13
                                                                                                                                                                     12)
                                                                                                                                                                 let mapping106_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__24
                                                                                                                                                                     19
                                                                                                                                                                     15)
                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                     mapping106_) && ((encdec_csrop_backwards_matches
                                                                                                                                                                       mapping107_) && (encdec_reg_backwards_matches
                                                                                                                                                                       mapping108_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                       v__24
                                                                                                                                                                       14
                                                                                                                                                                       14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                       v__24
                                                                                                                                                                       6
                                                                                                                                                                       0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let csr : (BitVec 12) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__24
                                                                                                                                                                    31
                                                                                                                                                                    20)
                                                                                                                                                                let mapping108_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__24
                                                                                                                                                                    11
                                                                                                                                                                    7)
                                                                                                                                                                let mapping107_ : (BitVec 2) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__24
                                                                                                                                                                    13
                                                                                                                                                                    12)
                                                                                                                                                                let mapping106_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__24
                                                                                                                                                                    19
                                                                                                                                                                    15)
                                                                                                                                                                let csr : (BitVec 12) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__24
                                                                                                                                                                    31
                                                                                                                                                                    20)
                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                    mapping106_)), (← (encdec_csrop_backwards
                                                                                                                                                                    mapping107_)), (← (encdec_reg_backwards
                                                                                                                                                                    mapping108_))) with
                                                                                                                                                                | (rs1, op, rd) =>
                                                                                                                                                                  (do
                                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                                           Ext_Zicsr)) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (pure (some
                                                                                                                                                                          (CSRReg
                                                                                                                                                                            (csr, rs1, rd, op))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure none)))
                                                                                                                                                            else
                                                                                                                                                              (pure none)) with
                                                                                                                                                          | .some result =>
                                                                                                                                                            (pure result)
                                                                                                                                                          | none =>
                                                                                                                                                            (do
                                                                                                                                                              match (← do
                                                                                                                                                                let v__21 :=
                                                                                                                                                                  head_exp_
                                                                                                                                                                if (((let mapping110_ : (BitVec 5) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__21
                                                                                                                                                                         11
                                                                                                                                                                         7)
                                                                                                                                                                     let mapping109_ : (BitVec 2) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__21
                                                                                                                                                                         13
                                                                                                                                                                         12)
                                                                                                                                                                     ((encdec_csrop_backwards_matches
                                                                                                                                                                         mapping109_) && (encdec_reg_backwards_matches
                                                                                                                                                                         mapping110_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                           v__21
                                                                                                                                                                           14
                                                                                                                                                                           14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                           v__21
                                                                                                                                                                           6
                                                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__21
                                                                                                                                                                        31
                                                                                                                                                                        20)
                                                                                                                                                                    let mapping110_ : (BitVec 5) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__21
                                                                                                                                                                        11
                                                                                                                                                                        7)
                                                                                                                                                                    let mapping109_ : (BitVec 2) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__21
                                                                                                                                                                        13
                                                                                                                                                                        12)
                                                                                                                                                                    let imm : (BitVec 5) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__21
                                                                                                                                                                        19
                                                                                                                                                                        15)
                                                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__21
                                                                                                                                                                        31
                                                                                                                                                                        20)
                                                                                                                                                                    match ((← (encdec_csrop_backwards
                                                                                                                                                                        mapping109_)), (← (encdec_reg_backwards
                                                                                                                                                                        mapping110_))) with
                                                                                                                                                                    | (op, rd) =>
                                                                                                                                                                      (do
                                                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (pure (some
                                                                                                                                                                              (CSRImm
                                                                                                                                                                                (csr, imm, rd, op))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure none)))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)) with
                                                                                                                                                              | .some result =>
                                                                                                                                                                (pure result)
                                                                                                                                                              | none =>
                                                                                                                                                                (do
                                                                                                                                                                  let v__15 :=
                                                                                                                                                                    head_exp_
                                                                                                                                                                  if (((← (currentlyEnabled
                                                                                                                                                                           Ext_Zifencei)) && (v__15 == (0x0000100F#32 : (BitVec 32)))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (pure (FENCEI
                                                                                                                                                                        ()))
                                                                                                                                                                  else
                                                                                                                                                                    (pure (ILLEGAL
                                                                                                                                                                        v__15))))))))))))))))))))))))))))))))))))))))))

noncomputable def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure true)
      else (pure false))
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__212, rd) =>
    (if (((Sail.BitVec.extractLsb v__212 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__214, rs2, rs1, op) =>
    (if (((Sail.BitVec.extractLsb v__214 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .ITYPE (imm, rs1, rd, op) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, SLLI) =>
    (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
    then (pure true)
    else (pure false))
  | .SHIFTIOP (shamt, rs1, rd, SRLI) =>
    (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
    then (pure true)
    else (pure false))
  | .SHIFTIOP (shamt, rs1, rd, SRAI) =>
    (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
    then (pure true)
    else (pure false))
  | .RTYPE (rs2, rs1, rd, ADD) => (pure true)
  | .RTYPE (rs2, rs1, rd, SLT) => (pure true)
  | .RTYPE (rs2, rs1, rd, SLTU) => (pure true)
  | .RTYPE (rs2, rs1, rd, AND) => (pure true)
  | .RTYPE (rs2, rs1, rd, OR) => (pure true)
  | .RTYPE (rs2, rs1, rd, XOR) => (pure true)
  | .RTYPE (rs2, rs1, rd, SLL) => (pure true)
  | .RTYPE (rs2, rs1, rd, SRL) => (pure true)
  | .RTYPE (rs2, rs1, rd, SUB) => (pure true)
  | .RTYPE (rs2, rs1, rd, SRA) => (pure true)
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (if ((valid_load_encdec width is_unsigned) : Bool)
    then (pure true)
    else (pure false))
  | .STORE (v__216, rs2, rs1, width) =>
    (if ((width ≤b xlen_bytes) : Bool)
    then (pure true)
    else (pure false))
  | .ADDIW (imm, rs1, rd) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, ADDW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SUBW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SLLW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SRLW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .RTYPEW (rs2, rs1, rd, SRAW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .SHIFTIWOP (shamt, rs1, rd, SLLIW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .SHIFTIWOP (shamt, rs1, rd, SRLIW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .SHIFTIWOP (shamt, rs1, rd, SRAIW) =>
    (if ((xlen == 64) : Bool)
    then (pure true)
    else (pure false))
  | .FENCE (pred, succ) => (pure true)
  | .FENCE_TSO () => (pure true)
  | .ECALL () => (pure true)
  | .MRET () => (pure true)
  | .SRET () => (pure true)
  | .EBREAK () => (pure true)
  | .WFI () => (pure true)
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then (pure true)
      else (pure false))
  | .FENCE_RESERVED (fm, pred, succ, rs, rd) =>
    (if ((((fm != 0b0000#4) && (fm != 0b1000#4)) || ((bne rs zreg) || (bne rd zreg))) : Bool)
    then (pure true)
    else (pure false))
  | .FENCEI_RESERVED (imm, rs, rd) =>
    (if (((imm != 0b000000000000#12) || ((bne rs zreg) || (bne rd zreg))) : Bool)
    then (pure true)
    else (pure false))
  | .MUL (rs2, rs1, rd, mul_op) =>
    (do
      if (((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul))) : Bool)
      then (pure true)
      else (pure false))
  | .DIV (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then (pure true)
      else (pure false))
  | .REM (rs2, rs1, rd, is_unsigned) =>
    (do
      if ((← (currentlyEnabled Ext_M)) : Bool)
      then (pure true)
      else (pure false))
  | .MULW (rs2, rs1, rd) =>
    (do
      if (((xlen == 64) && ((← (currentlyEnabled Ext_M)) || (← (currentlyEnabled Ext_Zmmul)))) : Bool)
      then (pure true)
      else (pure false))
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then (pure true)
      else (pure false))
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_M))) : Bool)
      then (pure true)
      else (pure false))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .FENCEI () =>
    (do
      if ((← (currentlyEnabled Ext_Zifencei)) : Bool)
      then (pure true)
      else (pure false))
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

noncomputable def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__410 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__410 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then (pure (some true))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__410 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__410 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__410 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__410 11 7)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__408 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__408 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__408 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__408 11 7)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd => (pure (some true)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__405 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__405 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__405 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__405 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__405 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__405 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__405 19 15)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some true)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__403 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__403 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__403 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__403 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__403 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__403 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__403 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__403 24 20)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) => (pure (some true)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__401 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__401 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__401 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__401 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__401 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__401 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__401 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__401 11 7)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__397 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__397 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__397 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__397 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__397 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__397 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__397 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__397 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__397 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some true))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__393 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__393 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__393 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__393 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__393 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__393 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__393 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__393 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__393 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some true))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__389 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__389 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__389 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__389 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__389 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__389 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__389 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__389 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__389 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some true))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__385 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__385 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__385 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__385 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__385 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__385 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__385 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__385 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__385 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__385 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) => (pure (some true)))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__381 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__381 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__381 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__381 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__381 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__381 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__381 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__381 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__381 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__381 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) => (pure (some true)))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__377 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__377 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__377 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__377 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__377 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__377 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__377 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__377 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__377 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__377 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) => (pure (some true)))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__373 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__373 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__373 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__373 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__373 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__373 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__373 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__373 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__373 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__373 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) => (pure (some true)))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__369 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__369 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__369 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__369 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__369 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__369 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__369 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__369 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__369 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__369 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) => (pure (some true)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__365 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__365 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__365 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__365 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__365 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__365 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__365 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__365 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__365 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__365 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) => (pure (some true)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__361 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__361 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__361 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__361 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__361 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__361 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__361 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__361 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__361 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__361 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some true)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__357 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__357 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__357 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__357 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__357 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__357 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__357 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__357
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__357
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__357
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some true)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__353 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__353 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__353 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__353 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__353 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__353 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__353 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__353 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__353 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__353 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some true)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__349 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__349 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__349 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__349 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__349 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__349 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__349 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__349 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__349 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__349 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some true)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__347 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__347 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__347 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__347 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__347 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bits_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__347 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__347 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__347 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__347 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__347 19 15)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bits_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some true))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__344 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__344 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__344 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__344 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__344 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__344 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__344 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__344 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__344 24 20)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((width ≤b xlen_bytes) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            true))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__341 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__341
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__341
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__341
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__341
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__341
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__341
                                                                                            19 15)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                true))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__337 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__337
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__337
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__337
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__337
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__337
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__337
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__337
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__337
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__337
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    true))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__333 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__333
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__333
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__333
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__333
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__333
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__333
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__333
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__333
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__333
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        true))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__329 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__329
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__329
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__329
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__329
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__329
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__329
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__329
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__329
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__329
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            true))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__325 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__325
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__325
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__325
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__325
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__325
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__325
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__325
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__325
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__325
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                true))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__321 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__321
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__321
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__321
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__321
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__321
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__321
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__321
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__321
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__321
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    true))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__317 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__317
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__317
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__317
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__317
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__317
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__317
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__317
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        true))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__313 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__313
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__313
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__313
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__313
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__313
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__313
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__313
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            true))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__309 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__309
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__309
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__309
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__309
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__309
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__309
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__309
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                true))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__258 :=
                                                                                                                          head_exp_
                                                                                                                        if ((((Sail.BitVec.extractLsb
                                                                                                                                 v__258
                                                                                                                                 31
                                                                                                                                 28) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__258
                                                                                                                                 19
                                                                                                                                 0) == (0x0000F#20 : (BitVec 20)))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if ((v__258 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  true))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__258 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__258 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          true))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__258 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__258 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if ((v__258 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      true))
                                                                                                                                                else
                                                                                                                                                  (do
                                                                                                                                                    if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__258
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping77_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__258
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                                             mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__258
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                               v__258
                                                                                                                                                               14
                                                                                                                                                               0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping78_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__258
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping77_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__258
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping77_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping78_))) with
                                                                                                                                                        | (rs2, rs1) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((← (virtual_memory_supported
                                                                                                                                                                     ())) || (not
                                                                                                                                                                   (true : Bool))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  true))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none))))))))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__255 :=
                                                                                                                              head_exp_
                                                                                                                            if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__255
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping79_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__255
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__255
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__255
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__255
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let mapping80_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__255
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping79_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__255
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__255
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping79_)), (← (encdec_reg_backwards
                                                                                                                                    mapping80_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (if ((((fm != 0b0000#4) && (fm != 0b1000#4)) || ((bne
                                                                                                                                           rs
                                                                                                                                           zreg) || (bne
                                                                                                                                           rd
                                                                                                                                           zreg))) : Bool)
                                                                                                                                  then
                                                                                                                                    (pure (some
                                                                                                                                        true))
                                                                                                                                  else
                                                                                                                                    (pure none)))
                                                                                                                            else
                                                                                                                              (pure none)) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__252 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping82_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__252
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__252
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && (encdec_reg_backwards_matches
                                                                                                                                         mapping82_))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__252
                                                                                                                                           14
                                                                                                                                           12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__252
                                                                                                                                           6
                                                                                                                                           0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let imm : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__252
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    let mapping82_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__252
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__252
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let imm : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__252
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_reg_backwards
                                                                                                                                        mapping82_))) with
                                                                                                                                    | (rs, rd) =>
                                                                                                                                      (if (((imm != 0b000000000000#12) || ((bne
                                                                                                                                               rs
                                                                                                                                               zreg) || (bne
                                                                                                                                               rd
                                                                                                                                               zreg))) : Bool)
                                                                                                                                      then
                                                                                                                                        (pure (some
                                                                                                                                            true))
                                                                                                                                      else
                                                                                                                                        (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__249 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping86_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__249
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping85_ : (BitVec 3) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__249
                                                                                                                                             14
                                                                                                                                             12)
                                                                                                                                         let mapping84_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__249
                                                                                                                                             19
                                                                                                                                             15)
                                                                                                                                         let mapping83_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__249
                                                                                                                                             24
                                                                                                                                             20)
                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                             mapping83_) && ((encdec_reg_backwards_matches
                                                                                                                                               mapping84_) && ((encdec_mul_op_backwards_matches
                                                                                                                                                 mapping85_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping86_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__249
                                                                                                                                               31
                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                               v__249
                                                                                                                                               6
                                                                                                                                               0) == (0b0110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping86_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__249
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping85_ : (BitVec 3) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__249
                                                                                                                                            14
                                                                                                                                            12)
                                                                                                                                        let mapping84_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__249
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let mapping83_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__249
                                                                                                                                            24
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                            mapping83_)), (← (encdec_reg_backwards
                                                                                                                                            mapping84_)), (← (encdec_mul_op_backwards
                                                                                                                                            mapping85_)), (← (encdec_reg_backwards
                                                                                                                                            mapping86_))) with
                                                                                                                                        | (rs2, rs1, mul_op, rd) =>
                                                                                                                                          (do
                                                                                                                                            if (((← (currentlyEnabled
                                                                                                                                                     Ext_M)) || (← (currentlyEnabled
                                                                                                                                                     Ext_Zmmul))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__245 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping90_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__245
                                                                                                                                                 11
                                                                                                                                                 7)
                                                                                                                                             let mapping89_ : (BitVec 1) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__245
                                                                                                                                                 12
                                                                                                                                                 12)
                                                                                                                                             let mapping88_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__245
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping87_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__245
                                                                                                                                                 24
                                                                                                                                                 20)
                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                 mapping87_) && ((encdec_reg_backwards_matches
                                                                                                                                                   mapping88_) && ((bool_bits_backwards_matches
                                                                                                                                                     mapping89_) && (encdec_reg_backwards_matches
                                                                                                                                                     mapping90_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                   v__245
                                                                                                                                                   31
                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                     v__245
                                                                                                                                                     14
                                                                                                                                                     13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                     v__245
                                                                                                                                                     6
                                                                                                                                                     0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping90_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__245
                                                                                                                                                11
                                                                                                                                                7)
                                                                                                                                            let mapping89_ : (BitVec 1) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__245
                                                                                                                                                12
                                                                                                                                                12)
                                                                                                                                            let mapping88_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__245
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping87_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__245
                                                                                                                                                24
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                mapping87_)), (← (encdec_reg_backwards
                                                                                                                                                mapping88_)), (bool_bits_backwards
                                                                                                                                              mapping89_), (← (encdec_reg_backwards
                                                                                                                                                mapping90_))) with
                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_M)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      true))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__241 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping94_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__241
                                                                                                                                                     11
                                                                                                                                                     7)
                                                                                                                                                 let mapping93_ : (BitVec 1) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__241
                                                                                                                                                     12
                                                                                                                                                     12)
                                                                                                                                                 let mapping92_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__241
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 let mapping91_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__241
                                                                                                                                                     24
                                                                                                                                                     20)
                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                     mapping91_) && ((encdec_reg_backwards_matches
                                                                                                                                                       mapping92_) && ((bool_bits_backwards_matches
                                                                                                                                                         mapping93_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping94_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__241
                                                                                                                                                       31
                                                                                                                                                       25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                         v__241
                                                                                                                                                         14
                                                                                                                                                         13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                         v__241
                                                                                                                                                         6
                                                                                                                                                         0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping94_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__241
                                                                                                                                                    11
                                                                                                                                                    7)
                                                                                                                                                let mapping93_ : (BitVec 1) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__241
                                                                                                                                                    12
                                                                                                                                                    12)
                                                                                                                                                let mapping92_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__241
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let mapping91_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__241
                                                                                                                                                    24
                                                                                                                                                    20)
                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                    mapping91_)), (← (encdec_reg_backwards
                                                                                                                                                    mapping92_)), (bool_bits_backwards
                                                                                                                                                  mapping93_), (← (encdec_reg_backwards
                                                                                                                                                    mapping94_))) with
                                                                                                                                                | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                  (do
                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                           Ext_M)) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (pure (some
                                                                                                                                                          true))
                                                                                                                                                    else
                                                                                                                                                      (pure none)))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (do
                                                                                                                                              match (← do
                                                                                                                                                let v__237 :=
                                                                                                                                                  head_exp_
                                                                                                                                                if (((let mapping97_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__237
                                                                                                                                                         11
                                                                                                                                                         7)
                                                                                                                                                     let mapping96_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__237
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping95_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__237
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping95_) && ((encdec_reg_backwards_matches
                                                                                                                                                           mapping96_) && (encdec_reg_backwards_matches
                                                                                                                                                           mapping97_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__237
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                             v__237
                                                                                                                                                             14
                                                                                                                                                             12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                                             v__237
                                                                                                                                                             6
                                                                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping97_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__237
                                                                                                                                                        11
                                                                                                                                                        7)
                                                                                                                                                    let mapping96_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__237
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping95_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__237
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping95_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping96_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping97_))) with
                                                                                                                                                    | (rs2, rs1, rd) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((xlen == 64) && ((← (currentlyEnabled
                                                                                                                                                                   Ext_M)) || (← (currentlyEnabled
                                                                                                                                                                   Ext_Zmmul)))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              true))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none)) with
                                                                                                                                              | .some result =>
                                                                                                                                                (pure result)
                                                                                                                                              | none =>
                                                                                                                                                (do
                                                                                                                                                  match (← do
                                                                                                                                                    let v__233 :=
                                                                                                                                                      head_exp_
                                                                                                                                                    if (((let mapping99_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__233
                                                                                                                                                             19
                                                                                                                                                             15)
                                                                                                                                                         let mapping98_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__233
                                                                                                                                                             24
                                                                                                                                                             20)
                                                                                                                                                         let mapping101_ : (BitVec 5) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__233
                                                                                                                                                             11
                                                                                                                                                             7)
                                                                                                                                                         let mapping100_ : (BitVec 1) :=
                                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                                             v__233
                                                                                                                                                             12
                                                                                                                                                             12)
                                                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                                                             mapping98_) && ((encdec_reg_backwards_matches
                                                                                                                                                               mapping99_) && ((bool_bits_backwards_matches
                                                                                                                                                                 mapping100_) && (encdec_reg_backwards_matches
                                                                                                                                                                 mapping101_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                               v__233
                                                                                                                                                               31
                                                                                                                                                               25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                 v__233
                                                                                                                                                                 14
                                                                                                                                                                 13) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                 v__233
                                                                                                                                                                 6
                                                                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let mapping99_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__233
                                                                                                                                                            19
                                                                                                                                                            15)
                                                                                                                                                        let mapping98_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__233
                                                                                                                                                            24
                                                                                                                                                            20)
                                                                                                                                                        let mapping101_ : (BitVec 5) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__233
                                                                                                                                                            11
                                                                                                                                                            7)
                                                                                                                                                        let mapping100_ : (BitVec 1) :=
                                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                                            v__233
                                                                                                                                                            12
                                                                                                                                                            12)
                                                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                                                            mapping98_)), (← (encdec_reg_backwards
                                                                                                                                                            mapping99_)), (bool_bits_backwards
                                                                                                                                                          mapping100_), (← (encdec_reg_backwards
                                                                                                                                                            mapping101_))) with
                                                                                                                                                        | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                          (do
                                                                                                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                     Ext_M))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (pure (some
                                                                                                                                                                  true))
                                                                                                                                                            else
                                                                                                                                                              (pure none)))
                                                                                                                                                    else
                                                                                                                                                      (pure none)) with
                                                                                                                                                  | .some result =>
                                                                                                                                                    (pure result)
                                                                                                                                                  | none =>
                                                                                                                                                    (do
                                                                                                                                                      match (← do
                                                                                                                                                        let v__229 :=
                                                                                                                                                          head_exp_
                                                                                                                                                        if (((let mapping105_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__229
                                                                                                                                                                 11
                                                                                                                                                                 7)
                                                                                                                                                             let mapping104_ : (BitVec 1) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__229
                                                                                                                                                                 12
                                                                                                                                                                 12)
                                                                                                                                                             let mapping103_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__229
                                                                                                                                                                 19
                                                                                                                                                                 15)
                                                                                                                                                             let mapping102_ : (BitVec 5) :=
                                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                                 v__229
                                                                                                                                                                 24
                                                                                                                                                                 20)
                                                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                                                 mapping102_) && ((encdec_reg_backwards_matches
                                                                                                                                                                   mapping103_) && ((bool_bits_backwards_matches
                                                                                                                                                                     mapping104_) && (encdec_reg_backwards_matches
                                                                                                                                                                     mapping105_))))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                   v__229
                                                                                                                                                                   31
                                                                                                                                                                   25) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                     v__229
                                                                                                                                                                     14
                                                                                                                                                                     13) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                     v__229
                                                                                                                                                                     6
                                                                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let mapping105_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__229
                                                                                                                                                                11
                                                                                                                                                                7)
                                                                                                                                                            let mapping104_ : (BitVec 1) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__229
                                                                                                                                                                12
                                                                                                                                                                12)
                                                                                                                                                            let mapping103_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__229
                                                                                                                                                                19
                                                                                                                                                                15)
                                                                                                                                                            let mapping102_ : (BitVec 5) :=
                                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                                v__229
                                                                                                                                                                24
                                                                                                                                                                20)
                                                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                                                mapping102_)), (← (encdec_reg_backwards
                                                                                                                                                                mapping103_)), (bool_bits_backwards
                                                                                                                                                              mapping104_), (← (encdec_reg_backwards
                                                                                                                                                                mapping105_))) with
                                                                                                                                                            | (rs2, rs1, is_unsigned, rd) =>
                                                                                                                                                              (do
                                                                                                                                                                if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                                                                         Ext_M))) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (pure (some
                                                                                                                                                                      true))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)))
                                                                                                                                                        else
                                                                                                                                                          (pure none)) with
                                                                                                                                                      | .some result =>
                                                                                                                                                        (pure result)
                                                                                                                                                      | none =>
                                                                                                                                                        (do
                                                                                                                                                          match (← do
                                                                                                                                                            let v__226 :=
                                                                                                                                                              head_exp_
                                                                                                                                                            if (((let mapping108_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__226
                                                                                                                                                                     11
                                                                                                                                                                     7)
                                                                                                                                                                 let mapping107_ : (BitVec 2) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__226
                                                                                                                                                                     13
                                                                                                                                                                     12)
                                                                                                                                                                 let mapping106_ : (BitVec 5) :=
                                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                                     v__226
                                                                                                                                                                     19
                                                                                                                                                                     15)
                                                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                                                     mapping106_) && ((encdec_csrop_backwards_matches
                                                                                                                                                                       mapping107_) && (encdec_reg_backwards_matches
                                                                                                                                                                       mapping108_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                       v__226
                                                                                                                                                                       14
                                                                                                                                                                       14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                       v__226
                                                                                                                                                                       6
                                                                                                                                                                       0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let mapping108_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__226
                                                                                                                                                                    11
                                                                                                                                                                    7)
                                                                                                                                                                let mapping107_ : (BitVec 2) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__226
                                                                                                                                                                    13
                                                                                                                                                                    12)
                                                                                                                                                                let mapping106_ : (BitVec 5) :=
                                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                                    v__226
                                                                                                                                                                    19
                                                                                                                                                                    15)
                                                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                                                    mapping106_)), (← (encdec_csrop_backwards
                                                                                                                                                                    mapping107_)), (← (encdec_reg_backwards
                                                                                                                                                                    mapping108_))) with
                                                                                                                                                                | (rs1, op, rd) =>
                                                                                                                                                                  (do
                                                                                                                                                                    if ((← (currentlyEnabled
                                                                                                                                                                           Ext_Zicsr)) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (pure (some
                                                                                                                                                                          true))
                                                                                                                                                                    else
                                                                                                                                                                      (pure none)))
                                                                                                                                                            else
                                                                                                                                                              (pure none)) with
                                                                                                                                                          | .some result =>
                                                                                                                                                            (pure result)
                                                                                                                                                          | none =>
                                                                                                                                                            (do
                                                                                                                                                              match (← do
                                                                                                                                                                let v__223 :=
                                                                                                                                                                  head_exp_
                                                                                                                                                                if (((let mapping110_ : (BitVec 5) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__223
                                                                                                                                                                         11
                                                                                                                                                                         7)
                                                                                                                                                                     let mapping109_ : (BitVec 2) :=
                                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                                         v__223
                                                                                                                                                                         13
                                                                                                                                                                         12)
                                                                                                                                                                     ((encdec_csrop_backwards_matches
                                                                                                                                                                         mapping109_) && (encdec_reg_backwards_matches
                                                                                                                                                                         mapping110_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                                           v__223
                                                                                                                                                                           14
                                                                                                                                                                           14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                                                           v__223
                                                                                                                                                                           6
                                                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let mapping110_ : (BitVec 5) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__223
                                                                                                                                                                        11
                                                                                                                                                                        7)
                                                                                                                                                                    let mapping109_ : (BitVec 2) :=
                                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                                        v__223
                                                                                                                                                                        13
                                                                                                                                                                        12)
                                                                                                                                                                    match ((← (encdec_csrop_backwards
                                                                                                                                                                        mapping109_)), (← (encdec_reg_backwards
                                                                                                                                                                        mapping110_))) with
                                                                                                                                                                    | (op, rd) =>
                                                                                                                                                                      (do
                                                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (pure (some
                                                                                                                                                                              true))
                                                                                                                                                                        else
                                                                                                                                                                          (pure none)))
                                                                                                                                                                else
                                                                                                                                                                  (pure none)) with
                                                                                                                                                              | .some result =>
                                                                                                                                                                (pure result)
                                                                                                                                                              | none =>
                                                                                                                                                                (do
                                                                                                                                                                  let v__217 :=
                                                                                                                                                                    head_exp_
                                                                                                                                                                  if (((← (currentlyEnabled
                                                                                                                                                                           Ext_Zifencei)) && (v__217 == (0x0000100F#32 : (BitVec 32)))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (pure true)
                                                                                                                                                                  else
                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))

noncomputable def encdec_compressed_forwards (arg_ : instruction) : SailM (BitVec 16) := do
  match arg_ with
  | .C_NOP v__414 =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__414 5 5)
        let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__414 5 5)
        let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__414 4 0)
        (pure (0b000#3 ++ ((imm5 : (BitVec 1)) ++ (0b00000#5 ++ ((imm40 : (BitVec 5)) ++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI4SPN (rd, v__415) =>
    (do
      if ((← do
           let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__415 7 4)
           let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__415 7 4)
           let nz54 : (BitVec 2) := (Sail.BitVec.extractLsb v__415 3 2)
           let nz3 : (BitVec 1) := (Sail.BitVec.extractLsb v__415 1 1)
           let nz2 : (BitVec 1) := (Sail.BitVec.extractLsb v__415 0 0)
           (pure (((nz96 ++ (nz54 ++ (nz3 ++ nz2))) != 0b00000000#8) && (← (currentlyEnabled
                   Ext_Zca))))) : Bool)
      then
        (let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__415 7 4)
        let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__415 7 4)
        let nz54 : (BitVec 2) := (Sail.BitVec.extractLsb v__415 3 2)
        let nz3 : (BitVec 1) := (Sail.BitVec.extractLsb v__415 1 1)
        let nz2 : (BitVec 1) := (Sail.BitVec.extractLsb v__415 0 0)
        (pure (0b000#3 ++ ((nz54 : (BitVec 2)) ++ ((nz96 : (BitVec 4)) ++ ((nz2 : (BitVec 1)) ++ ((nz3 : (BitVec 1)) ++ ((encdec_creg_forwards
                        rd) ++ 0b00#2))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LW (v__416, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let ui6 : (BitVec 1) := (Sail.BitVec.extractLsb v__416 4 4)
        let ui6 : (BitVec 1) := (Sail.BitVec.extractLsb v__416 4 4)
        let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__416 3 1)
        let ui2 : (BitVec 1) := (Sail.BitVec.extractLsb v__416 0 0)
        (pure (0b010#3 ++ ((ui53 : (BitVec 3)) ++ ((encdec_creg_forwards rs1) ++ ((ui2 : (BitVec 1)) ++ ((ui6 : (BitVec 1)) ++ ((encdec_creg_forwards
                        rd) ++ 0b00#2))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LD (v__417, rs1, rd) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__417 4 3)
        let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__417 4 3)
        let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__417 2 0)
        (pure (0b011#3 ++ ((ui53 : (BitVec 3)) ++ ((encdec_creg_forwards rs1) ++ ((ui76 : (BitVec 2)) ++ ((encdec_creg_forwards
                      rd) ++ 0b00#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SW (v__418, rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let ui6 : (BitVec 1) := (Sail.BitVec.extractLsb v__418 4 4)
        let ui6 : (BitVec 1) := (Sail.BitVec.extractLsb v__418 4 4)
        let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__418 3 1)
        let ui2 : (BitVec 1) := (Sail.BitVec.extractLsb v__418 0 0)
        (pure (0b110#3 ++ ((ui53 : (BitVec 3)) ++ ((encdec_creg_forwards rs1) ++ ((ui2 : (BitVec 1)) ++ ((ui6 : (BitVec 1)) ++ ((encdec_creg_forwards
                        rs2) ++ 0b00#2))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SD (v__419, rs1, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__419 4 3)
        let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__419 4 3)
        let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__419 2 0)
        (pure (0b111#3 ++ ((ui53 : (BitVec 3)) ++ ((encdec_creg_forwards rs1) ++ ((ui76 : (BitVec 2)) ++ ((encdec_creg_forwards
                      rs2) ++ 0b00#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI (v__420, rsd) =>
    (do
      if (((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__420 5 5)
        let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__420 5 5)
        let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__420 4 0)
        (pure (0b000#3 ++ ((imm5 : (BitVec 1)) ++ ((encdec_reg_forwards rsd) ++ ((imm40 : (BitVec 5)) ++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JAL v__421 =>
    (do
      if (((xlen == 32) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (let i11 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 10 10)
        let i98 : (BitVec 2) := (Sail.BitVec.extractLsb v__421 8 7)
        let i7 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 6 6)
        let i6 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 5 5)
        let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 4 4)
        let i4 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 3 3)
        let i31 : (BitVec 3) := (Sail.BitVec.extractLsb v__421 2 0)
        let i11 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 10 10)
        let i10 : (BitVec 1) := (Sail.BitVec.extractLsb v__421 9 9)
        (pure (0b001#3 ++ ((i11 : (BitVec 1)) ++ ((i4 : (BitVec 1)) ++ ((i98 : (BitVec 2)) ++ ((i10 : (BitVec 1)) ++ ((i6 : (BitVec 1)) ++ ((i7 : (BitVec 1)) ++ ((i31 : (BitVec 3)) ++ ((i5 : (BitVec 1)) ++ 0b01#2)))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDIW (v__422, rsd) =>
    (do
      if (((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then
        (let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__422 5 5)
        let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__422 5 5)
        let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__422 4 0)
        (pure (0b001#3 ++ ((imm5 : (BitVec 1)) ++ ((encdec_reg_forwards rsd) ++ ((imm40 : (BitVec 5)) ++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LI (v__423, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__423 5 5)
        let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__423 5 5)
        let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__423 4 0)
        (pure (0b010#3 ++ ((imm5 : (BitVec 1)) ++ ((encdec_reg_forwards rd) ++ ((imm40 : (BitVec 5)) ++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI16SP v__424 =>
    (do
      if ((← do
           let nzi9 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 5 5)
           let nzi9 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 5 5)
           let nzi87 : (BitVec 2) := (Sail.BitVec.extractLsb v__424 4 3)
           let nzi6 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 2 2)
           let nzi5 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 1 1)
           let nzi4 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 0 0)
           (pure (((nzi9 ++ (nzi87 ++ (nzi6 ++ (nzi5 ++ nzi4)))) != 0b000000#6) && (← (currentlyEnabled
                   Ext_Zca))))) : Bool)
      then
        (let nzi9 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 5 5)
        let nzi9 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 5 5)
        let nzi87 : (BitVec 2) := (Sail.BitVec.extractLsb v__424 4 3)
        let nzi6 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 2 2)
        let nzi5 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 1 1)
        let nzi4 : (BitVec 1) := (Sail.BitVec.extractLsb v__424 0 0)
        (pure (0b011#3 ++ ((nzi9 : (BitVec 1)) ++ (0b00010#5 ++ ((nzi4 : (BitVec 1)) ++ ((nzi6 : (BitVec 1)) ++ ((nzi87 : (BitVec 2)) ++ ((nzi5 : (BitVec 1)) ++ 0b01#2)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LUI (v__425, rd) =>
    (do
      if ((← do
           let imm17 : (BitVec 1) := (Sail.BitVec.extractLsb v__425 5 5)
           let imm17 : (BitVec 1) := (Sail.BitVec.extractLsb v__425 5 5)
           let imm1612 : (BitVec 5) := (Sail.BitVec.extractLsb v__425 4 0)
           (pure ((bne rd sp) && (((imm17 ++ imm1612) != 0b000000#6) && (← (currentlyEnabled
                     Ext_Zca)))))) : Bool)
      then
        (let imm17 : (BitVec 1) := (Sail.BitVec.extractLsb v__425 5 5)
        let imm17 : (BitVec 1) := (Sail.BitVec.extractLsb v__425 5 5)
        let imm1612 : (BitVec 5) := (Sail.BitVec.extractLsb v__425 4 0)
        (pure (0b011#3 ++ ((imm17 : (BitVec 1)) ++ ((encdec_reg_forwards rd) ++ ((imm1612 : (BitVec 5)) ++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI (v__426, rsd) =>
    (do
      if ((← do
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__426 5 5)
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__426 5 5)
           (pure (((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled Ext_Zca))))) : Bool)
      then
        (let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__426 5 5)
        let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__426 5 5)
        let shamt40 : (BitVec 5) := (Sail.BitVec.extractLsb v__426 4 0)
        (pure (0b100#3 ++ ((shamt5 : (BitVec 1)) ++ (0b00#2 ++ ((encdec_creg_forwards rsd) ++ ((shamt40 : (BitVec 5)) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRAI (v__427, rsd) =>
    (do
      if ((← do
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__427 5 5)
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__427 5 5)
           (pure (((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled Ext_Zca))))) : Bool)
      then
        (let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__427 5 5)
        let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__427 5 5)
        let shamt40 : (BitVec 5) := (Sail.BitVec.extractLsb v__427 4 0)
        (pure (0b100#3 ++ ((shamt5 : (BitVec 1)) ++ (0b01#2 ++ ((encdec_creg_forwards rsd) ++ ((shamt40 : (BitVec 5)) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ANDI (v__428, rsd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__428 5 5)
        let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__428 5 5)
        let i40 : (BitVec 5) := (Sail.BitVec.extractLsb v__428 4 0)
        (pure (0b100#3 ++ ((i5 : (BitVec 1)) ++ (0b10#2 ++ ((encdec_creg_forwards rsd) ++ ((i40 : (BitVec 5)) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SUB (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 ++ (0#1 ++ (0b11#2 ++ ((encdec_creg_forwards rsd) ++ (0b00#2 ++ ((encdec_creg_forwards
                        rs2) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_XOR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 ++ (0#1 ++ (0b11#2 ++ ((encdec_creg_forwards rsd) ++ (0b01#2 ++ ((encdec_creg_forwards
                        rs2) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_OR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 ++ (0#1 ++ (0b11#2 ++ ((encdec_creg_forwards rsd) ++ (0b10#2 ++ ((encdec_creg_forwards
                        rs2) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_AND (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 ++ (0#1 ++ (0b11#2 ++ ((encdec_creg_forwards rsd) ++ (0b11#2 ++ ((encdec_creg_forwards
                        rs2) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SUBW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 ++ (1#1 ++ (0b11#2 ++ ((encdec_creg_forwards rsd) ++ (0b00#2 ++ ((encdec_creg_forwards
                        rs2) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 ++ (1#1 ++ (0b11#2 ++ ((encdec_creg_forwards rsd) ++ (0b01#2 ++ ((encdec_creg_forwards
                        rs2) ++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_J v__429 =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let i11 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 10 10)
        let i98 : (BitVec 2) := (Sail.BitVec.extractLsb v__429 8 7)
        let i7 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 6 6)
        let i6 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 5 5)
        let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 4 4)
        let i4 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 3 3)
        let i31 : (BitVec 3) := (Sail.BitVec.extractLsb v__429 2 0)
        let i11 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 10 10)
        let i10 : (BitVec 1) := (Sail.BitVec.extractLsb v__429 9 9)
        (pure (0b101#3 ++ ((i11 : (BitVec 1)) ++ ((i4 : (BitVec 1)) ++ ((i98 : (BitVec 2)) ++ ((i10 : (BitVec 1)) ++ ((i6 : (BitVec 1)) ++ ((i7 : (BitVec 1)) ++ ((i31 : (BitVec 3)) ++ ((i5 : (BitVec 1)) ++ 0b01#2)))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_BEQZ (v__430, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let i8 : (BitVec 1) := (Sail.BitVec.extractLsb v__430 7 7)
        let i8 : (BitVec 1) := (Sail.BitVec.extractLsb v__430 7 7)
        let i76 : (BitVec 2) := (Sail.BitVec.extractLsb v__430 6 5)
        let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__430 4 4)
        let i43 : (BitVec 2) := (Sail.BitVec.extractLsb v__430 3 2)
        let i21 : (BitVec 2) := (Sail.BitVec.extractLsb v__430 1 0)
        (pure (0b110#3 ++ ((i8 : (BitVec 1)) ++ ((i43 : (BitVec 2)) ++ ((encdec_creg_forwards rs) ++ ((i76 : (BitVec 2)) ++ ((i21 : (BitVec 2)) ++ ((i5 : (BitVec 1)) ++ 0b01#2)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_BNEZ (v__431, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let i8 : (BitVec 1) := (Sail.BitVec.extractLsb v__431 7 7)
        let i8 : (BitVec 1) := (Sail.BitVec.extractLsb v__431 7 7)
        let i76 : (BitVec 2) := (Sail.BitVec.extractLsb v__431 6 5)
        let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__431 4 4)
        let i43 : (BitVec 2) := (Sail.BitVec.extractLsb v__431 3 2)
        let i21 : (BitVec 2) := (Sail.BitVec.extractLsb v__431 1 0)
        (pure (0b111#3 ++ ((i8 : (BitVec 1)) ++ ((i43 : (BitVec 2)) ++ ((encdec_creg_forwards rs) ++ ((i76 : (BitVec 2)) ++ ((i21 : (BitVec 2)) ++ ((i5 : (BitVec 1)) ++ 0b01#2)))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SLLI (v__432, rsd) =>
    (do
      if ((← do
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__432 5 5)
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__432 5 5)
           (pure (((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled Ext_Zca))))) : Bool)
      then
        (let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__432 5 5)
        let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__432 5 5)
        let shamt40 : (BitVec 5) := (Sail.BitVec.extractLsb v__432 4 0)
        (pure (0b000#3 ++ ((shamt5 : (BitVec 1)) ++ ((encdec_reg_forwards rsd) ++ ((shamt40 : (BitVec 5)) ++ 0b10#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LWSP (v__433, rd) =>
    (do
      if (((bne rd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__433 5 4)
        let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__433 5 4)
        let ui5 : (BitVec 1) := (Sail.BitVec.extractLsb v__433 3 3)
        let ui42 : (BitVec 3) := (Sail.BitVec.extractLsb v__433 2 0)
        (pure (0b010#3 ++ ((ui5 : (BitVec 1)) ++ ((encdec_reg_forwards rd) ++ ((ui42 : (BitVec 3)) ++ ((ui76 : (BitVec 2)) ++ 0b10#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LDSP (v__434, rd) =>
    (do
      if (((bne rd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then
        (let ui86 : (BitVec 3) := (Sail.BitVec.extractLsb v__434 5 3)
        let ui86 : (BitVec 3) := (Sail.BitVec.extractLsb v__434 5 3)
        let ui5 : (BitVec 1) := (Sail.BitVec.extractLsb v__434 2 2)
        let ui43 : (BitVec 2) := (Sail.BitVec.extractLsb v__434 1 0)
        (pure (0b011#3 ++ ((ui5 : (BitVec 1)) ++ ((encdec_reg_forwards rd) ++ ((ui43 : (BitVec 2)) ++ ((ui86 : (BitVec 3)) ++ 0b10#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SWSP (v__435, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__435 5 4)
        let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__435 5 4)
        let ui52 : (BitVec 4) := (Sail.BitVec.extractLsb v__435 3 0)
        (pure (0b110#3 ++ ((ui52 : (BitVec 4)) ++ ((ui76 : (BitVec 2)) ++ ((encdec_reg_forwards rs2) ++ 0b10#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SDSP (v__436, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (let ui86 : (BitVec 3) := (Sail.BitVec.extractLsb v__436 5 3)
        let ui86 : (BitVec 3) := (Sail.BitVec.extractLsb v__436 5 3)
        let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__436 2 0)
        (pure (0b111#3 ++ ((ui53 : (BitVec 3)) ++ ((ui86 : (BitVec 3)) ++ ((encdec_reg_forwards rs2) ++ 0b10#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure (0b100#3 ++ (0#1 ++ ((encdec_reg_forwards rs1) ++ (0b00000#5 ++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JALR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure (0b100#3 ++ (1#1 ++ ((encdec_reg_forwards rs1) ++ (0b00000#5 ++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV (rd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 ++ (0#1 ++ ((encdec_reg_forwards rd) ++ ((encdec_reg_forwards rs2) ++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_EBREAK () =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure (0b100#3 ++ (1#1 ++ (0b00000#5 ++ (0b00000#5 ++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADD (rsd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 ++ (1#1 ++ ((encdec_reg_forwards rsd) ++ ((encdec_reg_forwards rs2) ++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

noncomputable def encdec_compressed_backwards (arg_ : (BitVec 16)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__564 := head_exp_
    if (((← (currentlyEnabled Ext_Zca)) && (((Sail.BitVec.extractLsb v__564 15 13) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                 v__564 11 7) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb v__564 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
    then
      (let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__564 12 12)
      let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__564 6 2)
      (pure (some (C_NOP ((imm5 : (BitVec 1)) ++ (imm40 : (BitVec 5)))))))
    else
      (do
        if (((let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__564 4 2)
             (encdec_creg_backwards_matches mapping0_)) && (((Sail.BitVec.extractLsb v__564 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                   v__564 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__564 10 7)
            let nz54 : (BitVec 2) := (Sail.BitVec.extractLsb v__564 12 11)
            let nz3 : (BitVec 1) := (Sail.BitVec.extractLsb v__564 5 5)
            let nz2 : (BitVec 1) := (Sail.BitVec.extractLsb v__564 6 6)
            let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__564 4 2)
            let rd := (encdec_creg_backwards mapping0_)
            if ((((nz96 ++ (nz54 ++ (nz3 ++ nz2))) != 0b00000000#8) && (← (currentlyEnabled
                     Ext_Zca))) : Bool)
            then
              (pure (some
                  (C_ADDI4SPN
                    (rd, ((nz96 : (BitVec 4)) ++ ((nz54 : (BitVec 2)) ++ ((nz3 : (BitVec 1)) ++ (nz2 : (BitVec 1)))))))))
            else (pure none))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__561 := head_exp_
        if (((let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__561 4 2)
             let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__561 9 7)
             ((encdec_creg_backwards_matches mapping1_) && (encdec_creg_backwards_matches mapping2_))) && (((Sail.BitVec.extractLsb
                   v__561 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__561 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let ui6 : (BitVec 1) := (Sail.BitVec.extractLsb v__561 5 5)
            let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__561 12 10)
            let ui2 : (BitVec 1) := (Sail.BitVec.extractLsb v__561 6 6)
            let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__561 4 2)
            let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__561 9 7)
            match ((encdec_creg_backwards mapping1_), (encdec_creg_backwards mapping2_)) with
            | (rs1, rd) =>
              (do
                if ((← (currentlyEnabled Ext_Zca)) : Bool)
                then
                  (pure (some
                      (C_LW
                        (((ui6 : (BitVec 1)) ++ ((ui53 : (BitVec 3)) ++ (ui2 : (BitVec 1)))), rs1, rd))))
                else (pure none)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__558 := head_exp_
            if (((let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__558 4 2)
                 let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__558 9 7)
                 ((encdec_creg_backwards_matches mapping3_) && (encdec_creg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__558 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__558 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
            then
              (do
                let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__558 6 5)
                let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__558 12 10)
                let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__558 4 2)
                let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__558 9 7)
                match ((encdec_creg_backwards mapping3_), (encdec_creg_backwards mapping4_)) with
                | (rs1, rd) =>
                  (do
                    if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
                    then
                      (pure (some (C_LD (((ui76 : (BitVec 2)) ++ (ui53 : (BitVec 3))), rs1, rd))))
                    else (pure none)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__555 := head_exp_
                if (((let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__555 4 2)
                     let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__555 9 7)
                     ((encdec_creg_backwards_matches mapping5_) && (encdec_creg_backwards_matches
                         mapping6_))) && (((Sail.BitVec.extractLsb v__555 15 13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                           v__555 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                then
                  (do
                    let ui6 : (BitVec 1) := (Sail.BitVec.extractLsb v__555 5 5)
                    let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__555 12 10)
                    let ui2 : (BitVec 1) := (Sail.BitVec.extractLsb v__555 6 6)
                    let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__555 4 2)
                    let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__555 9 7)
                    match ((encdec_creg_backwards mapping5_), (encdec_creg_backwards mapping6_)) with
                    | (rs1, rs2) =>
                      (do
                        if ((← (currentlyEnabled Ext_Zca)) : Bool)
                        then
                          (pure (some
                              (C_SW
                                (((ui6 : (BitVec 1)) ++ ((ui53 : (BitVec 3)) ++ (ui2 : (BitVec 1)))), rs1, rs2))))
                        else (pure none)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__552 := head_exp_
                    if (((let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__552 4 2)
                         let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__552 9 7)
                         ((encdec_creg_backwards_matches mapping7_) && (encdec_creg_backwards_matches
                             mapping8_))) && (((Sail.BitVec.extractLsb v__552 15 13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                               v__552 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                    then
                      (do
                        let ui76 : (BitVec 2) := (Sail.BitVec.extractLsb v__552 6 5)
                        let ui53 : (BitVec 3) := (Sail.BitVec.extractLsb v__552 12 10)
                        let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__552 4 2)
                        let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__552 9 7)
                        match ((encdec_creg_backwards mapping7_), (encdec_creg_backwards mapping8_)) with
                        | (rs1, rs2) =>
                          (do
                            if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
                            then
                              (pure (some
                                  (C_SD (((ui76 : (BitVec 2)) ++ (ui53 : (BitVec 3))), rs1, rs2))))
                            else (pure none)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__549 := head_exp_
                        if (((let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__549 11 7)
                             (encdec_reg_backwards_matches mapping9_)) && (((Sail.BitVec.extractLsb
                                   v__549 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__549 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                        then
                          (do
                            let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__549 11 7)
                            let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__549 12 12)
                            let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__549 6 2)
                            let rsd ← do (encdec_reg_backwards mapping9_)
                            if (((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
                            then
                              (pure (some
                                  (C_ADDI (((imm5 : (BitVec 1)) ++ (imm40 : (BitVec 5))), rsd))))
                            else (pure none))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__543 := head_exp_
                            if ((((xlen == 32) && (← (currentlyEnabled Ext_Zca))) && (((Sail.BitVec.extractLsb
                                       v__543 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__543 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                            then
                              (let i98 : (BitVec 2) := (Sail.BitVec.extractLsb v__543 10 9)
                              let i7 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 6 6)
                              let i6 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 7 7)
                              let i5 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 2 2)
                              let i4 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 11 11)
                              let i31 : (BitVec 3) := (Sail.BitVec.extractLsb v__543 5 3)
                              let i11 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 12 12)
                              let i10 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 8 8)
                              (pure (some
                                  (C_JAL
                                    ((i11 : (BitVec 1)) ++ ((i10 : (BitVec 1)) ++ ((i98 : (BitVec 2)) ++ ((i7 : (BitVec 1)) ++ ((i6 : (BitVec 1)) ++ ((i5 : (BitVec 1)) ++ ((i4 : (BitVec 1)) ++ (i31 : (BitVec 3)))))))))))))
                            else
                              (do
                                if (((let mapping10_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__543 11 7)
                                     (encdec_reg_backwards_matches mapping10_)) && (((Sail.BitVec.extractLsb
                                           v__543 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__543 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping10_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__543 11 7)
                                    let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__543 12 12)
                                    let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__543 6 2)
                                    let rsd ← do (encdec_reg_backwards mapping10_)
                                    if (((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled
                                               Ext_Zca)))) : Bool)
                                    then
                                      (pure (some
                                          (C_ADDIW
                                            (((imm5 : (BitVec 1)) ++ (imm40 : (BitVec 5))), rsd))))
                                    else (pure none))
                                else (pure none))) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__540 := head_exp_
                                if (((let mapping11_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__540 11 7)
                                     (encdec_reg_backwards_matches mapping11_)) && (((Sail.BitVec.extractLsb
                                           v__540 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__540 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping11_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__540 11 7)
                                    let imm5 : (BitVec 1) := (Sail.BitVec.extractLsb v__540 12 12)
                                    let imm40 : (BitVec 5) := (Sail.BitVec.extractLsb v__540 6 2)
                                    let rd ← do (encdec_reg_backwards mapping11_)
                                    if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                    then
                                      (pure (some
                                          (C_LI (((imm5 : (BitVec 1)) ++ (imm40 : (BitVec 5))), rd))))
                                    else (pure none))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__533 := head_exp_
                                    if (((← do
                                           let nzi9 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__533 12 12)
                                           let nzi87 : (BitVec 2) :=
                                             (Sail.BitVec.extractLsb v__533 4 3)
                                           let nzi6 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__533 5 5)
                                           let nzi5 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__533 2 2)
                                           let nzi4 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__533 6 6)
                                           (pure (((nzi9 ++ (nzi87 ++ (nzi6 ++ (nzi5 ++ nzi4)))) != 0b000000#6) && (← (currentlyEnabled
                                                   Ext_Zca))))) && (((Sail.BitVec.extractLsb v__533
                                               15 13) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                 v__533 11 7) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb
                                                 v__533 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                    then
                                      (let nzi9 : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__533 12 12)
                                      let nzi87 : (BitVec 2) := (Sail.BitVec.extractLsb v__533 4 3)
                                      let nzi6 : (BitVec 1) := (Sail.BitVec.extractLsb v__533 5 5)
                                      let nzi5 : (BitVec 1) := (Sail.BitVec.extractLsb v__533 2 2)
                                      let nzi4 : (BitVec 1) := (Sail.BitVec.extractLsb v__533 6 6)
                                      (pure (some
                                          (C_ADDI16SP
                                            ((nzi9 : (BitVec 1)) ++ ((nzi87 : (BitVec 2)) ++ ((nzi6 : (BitVec 1)) ++ ((nzi5 : (BitVec 1)) ++ (nzi4 : (BitVec 1))))))))))
                                    else
                                      (do
                                        if (((let mapping12_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__533 11 7)
                                             (encdec_reg_backwards_matches mapping12_)) && (((Sail.BitVec.extractLsb
                                                   v__533 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__533 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                        then
                                          (do
                                            let mapping12_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__533 11 7)
                                            let imm17 : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__533 12 12)
                                            let imm1612 : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__533 6 2)
                                            let rd ← do (encdec_reg_backwards mapping12_)
                                            if (((bne rd sp) && (((imm17 ++ imm1612) != 0b000000#6) && (← (currentlyEnabled
                                                       Ext_Zca)))) : Bool)
                                            then
                                              (pure (some
                                                  (C_LUI
                                                    (((imm17 : (BitVec 1)) ++ (imm1612 : (BitVec 5))), rd))))
                                            else (pure none))
                                        else (pure none))) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__529 := head_exp_
                                        if (((let mapping13_ : (BitVec 3) :=
                                               (Sail.BitVec.extractLsb v__529 9 7)
                                             (encdec_creg_backwards_matches mapping13_)) && (((Sail.BitVec.extractLsb
                                                   v__529 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                     v__529 11 10) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                     v__529 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                        then
                                          (do
                                            let shamt5 : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__529 12 12)
                                            let shamt40 : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__529 6 2)
                                            let mapping13_ : (BitVec 3) :=
                                              (Sail.BitVec.extractLsb v__529 9 7)
                                            let rsd := (encdec_creg_backwards mapping13_)
                                            if ((((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled
                                                     Ext_Zca))) : Bool)
                                            then
                                              (pure (some
                                                  (C_SRLI
                                                    (((shamt5 : (BitVec 1)) ++ (shamt40 : (BitVec 5))), rsd))))
                                            else (pure none))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__525 := head_exp_
                                            if (((let mapping14_ : (BitVec 3) :=
                                                   (Sail.BitVec.extractLsb v__525 9 7)
                                                 (encdec_creg_backwards_matches mapping14_)) && (((Sail.BitVec.extractLsb
                                                       v__525 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                         v__525 11 10) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                         v__525 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                            then
                                              (do
                                                let shamt5 : (BitVec 1) :=
                                                  (Sail.BitVec.extractLsb v__525 12 12)
                                                let shamt40 : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__525 6 2)
                                                let mapping14_ : (BitVec 3) :=
                                                  (Sail.BitVec.extractLsb v__525 9 7)
                                                let rsd := (encdec_creg_backwards mapping14_)
                                                if ((((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled
                                                         Ext_Zca))) : Bool)
                                                then
                                                  (pure (some
                                                      (C_SRAI
                                                        (((shamt5 : (BitVec 1)) ++ (shamt40 : (BitVec 5))), rsd))))
                                                else (pure none))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__521 := head_exp_
                                                if (((let mapping15_ : (BitVec 3) :=
                                                       (Sail.BitVec.extractLsb v__521 9 7)
                                                     (encdec_creg_backwards_matches mapping15_)) && (((Sail.BitVec.extractLsb
                                                           v__521 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                             v__521 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                             v__521 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping15_ : (BitVec 3) :=
                                                      (Sail.BitVec.extractLsb v__521 9 7)
                                                    let i5 : (BitVec 1) :=
                                                      (Sail.BitVec.extractLsb v__521 12 12)
                                                    let i40 : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__521 6 2)
                                                    let rsd := (encdec_creg_backwards mapping15_)
                                                    if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                    then
                                                      (pure (some
                                                          (C_ANDI
                                                            (((i5 : (BitVec 1)) ++ (i40 : (BitVec 5))), rsd))))
                                                    else (pure none))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__515 := head_exp_
                                                    if (((let mapping17_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__515 4 2)
                                                         let mapping16_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__515 9 7)
                                                         ((encdec_creg_backwards_matches mapping16_) && (encdec_creg_backwards_matches
                                                             mapping17_))) && (((Sail.BitVec.extractLsb
                                                               v__515 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                 v__515 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                 v__515 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping17_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__515 4 2)
                                                        let mapping16_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__515 9 7)
                                                        match ((encdec_creg_backwards mapping16_), (encdec_creg_backwards
                                                          mapping17_)) with
                                                        | (rsd, rs2) =>
                                                          (do
                                                            if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                            then (pure (some (C_SUB (rsd, rs2))))
                                                            else (pure none)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__509 := head_exp_
                                                        if (((let mapping19_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__509 4 2)
                                                             let mapping18_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__509 9 7)
                                                             ((encdec_creg_backwards_matches
                                                                 mapping18_) && (encdec_creg_backwards_matches
                                                                 mapping19_))) && (((Sail.BitVec.extractLsb
                                                                   v__509 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                     v__509 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                     v__509 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping19_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__509 4 2)
                                                            let mapping18_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__509 9 7)
                                                            match ((encdec_creg_backwards mapping18_), (encdec_creg_backwards
                                                              mapping19_)) with
                                                            | (rsd, rs2) =>
                                                              (do
                                                                if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                                then
                                                                  (pure (some (C_XOR (rsd, rs2))))
                                                                else (pure none)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__503 := head_exp_
                                                            if (((let mapping21_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__503 4
                                                                     2)
                                                                 let mapping20_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__503 9
                                                                     7)
                                                                 ((encdec_creg_backwards_matches
                                                                     mapping20_) && (encdec_creg_backwards_matches
                                                                     mapping21_))) && (((Sail.BitVec.extractLsb
                                                                       v__503 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                         v__503 6 5) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                         v__503 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping21_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__503 4 2)
                                                                let mapping20_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__503 9 7)
                                                                match ((encdec_creg_backwards
                                                                  mapping20_), (encdec_creg_backwards
                                                                  mapping21_)) with
                                                                | (rsd, rs2) =>
                                                                  (do
                                                                    if ((← (currentlyEnabled
                                                                           Ext_Zca)) : Bool)
                                                                    then
                                                                      (pure (some (C_OR (rsd, rs2))))
                                                                    else (pure none)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__497 := head_exp_
                                                                if (((let mapping23_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__497 4 2)
                                                                     let mapping22_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__497 9 7)
                                                                     ((encdec_creg_backwards_matches
                                                                         mapping22_) && (encdec_creg_backwards_matches
                                                                         mapping23_))) && (((Sail.BitVec.extractLsb
                                                                           v__497 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                             v__497 6 5) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                             v__497 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping23_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__497
                                                                        4 2)
                                                                    let mapping22_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__497
                                                                        9 7)
                                                                    match ((encdec_creg_backwards
                                                                      mapping22_), (encdec_creg_backwards
                                                                      mapping23_)) with
                                                                    | (rsd, rs2) =>
                                                                      (do
                                                                        if ((← (currentlyEnabled
                                                                               Ext_Zca)) : Bool)
                                                                        then
                                                                          (pure (some
                                                                              (C_AND (rsd, rs2))))
                                                                        else (pure none)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__491 := head_exp_
                                                                    if (((let mapping25_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__491 4 2)
                                                                         let mapping24_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__491 9 7)
                                                                         ((encdec_creg_backwards_matches
                                                                             mapping24_) && (encdec_creg_backwards_matches
                                                                             mapping25_))) && (((Sail.BitVec.extractLsb
                                                                               v__491 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                 v__491 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                 v__491 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping25_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__491 4 2)
                                                                        let mapping24_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__491 9 7)
                                                                        match ((encdec_creg_backwards
                                                                          mapping24_), (encdec_creg_backwards
                                                                          mapping25_)) with
                                                                        | (rsd, rs2) =>
                                                                          (do
                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                     Ext_Zca))) : Bool)
                                                                            then
                                                                              (pure (some
                                                                                  (C_SUBW (rsd, rs2))))
                                                                            else (pure none)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__485 := head_exp_
                                                                        if (((let mapping27_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__485 4 2)
                                                                             let mapping26_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__485 9 7)
                                                                             ((encdec_creg_backwards_matches
                                                                                 mapping26_) && (encdec_creg_backwards_matches
                                                                                 mapping27_))) && (((Sail.BitVec.extractLsb
                                                                                   v__485 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                     v__485 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                     v__485 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping27_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__485 4 2)
                                                                            let mapping26_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__485 9 7)
                                                                            match ((encdec_creg_backwards
                                                                              mapping26_), (encdec_creg_backwards
                                                                              mapping27_)) with
                                                                            | (rsd, rs2) =>
                                                                              (do
                                                                                if (((xlen == 64) && (← (currentlyEnabled
                                                                                         Ext_Zca))) : Bool)
                                                                                then
                                                                                  (pure (some
                                                                                      (C_ADDW
                                                                                        (rsd, rs2))))
                                                                                else (pure none)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__479 := head_exp_
                                                                            if (((← (currentlyEnabled
                                                                                     Ext_Zca)) && (((Sail.BitVec.extractLsb
                                                                                       v__479 15 13) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                       v__479 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                            then
                                                                              (let i98 : (BitVec 2) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 10 9)
                                                                              let i7 : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 6 6)
                                                                              let i6 : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 7 7)
                                                                              let i5 : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 2 2)
                                                                              let i4 : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 11 11)
                                                                              let i31 : (BitVec 3) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 5 3)
                                                                              let i11 : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 12 12)
                                                                              let i10 : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__479 8 8)
                                                                              (pure (some
                                                                                  (C_J
                                                                                    ((i11 : (BitVec 1)) ++ ((i10 : (BitVec 1)) ++ ((i98 : (BitVec 2)) ++ ((i7 : (BitVec 1)) ++ ((i6 : (BitVec 1)) ++ ((i5 : (BitVec 1)) ++ ((i4 : (BitVec 1)) ++ (i31 : (BitVec 3)))))))))))))
                                                                            else
                                                                              (do
                                                                                if (((let mapping28_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__479 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping28_)) && (((Sail.BitVec.extractLsb
                                                                                           v__479 15
                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__479 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping28_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__479 9 7)
                                                                                    let i8 : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__479 12 12)
                                                                                    let i76 : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__479 6 5)
                                                                                    let i5 : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__479 2 2)
                                                                                    let i43 : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__479 11 10)
                                                                                    let i21 : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__479 4 3)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping28_)
                                                                                    if ((← (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          (C_BEQZ
                                                                                            (((i8 : (BitVec 1)) ++ ((i76 : (BitVec 2)) ++ ((i5 : (BitVec 1)) ++ ((i43 : (BitVec 2)) ++ (i21 : (BitVec 2)))))), rs))))
                                                                                    else (pure none))
                                                                                else (pure none))) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__476 :=
                                                                                  head_exp_
                                                                                if (((let mapping29_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__476 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping29_)) && (((Sail.BitVec.extractLsb
                                                                                           v__476 15
                                                                                           13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__476 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping29_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__476 9 7)
                                                                                    let i8 : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__476 12 12)
                                                                                    let i76 : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__476 6 5)
                                                                                    let i5 : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__476 2 2)
                                                                                    let i43 : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__476 11 10)
                                                                                    let i21 : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__476 4 3)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping29_)
                                                                                    if ((← (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          (C_BNEZ
                                                                                            (((i8 : (BitVec 1)) ++ ((i76 : (BitVec 2)) ++ ((i5 : (BitVec 1)) ++ ((i43 : (BitVec 2)) ++ (i21 : (BitVec 2)))))), rs))))
                                                                                    else (pure none))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__473 :=
                                                                                      head_exp_
                                                                                    if (((let mapping30_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__473
                                                                                             11 7)
                                                                                         (encdec_reg_backwards_matches
                                                                                           mapping30_)) && (((Sail.BitVec.extractLsb
                                                                                               v__473
                                                                                               15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__473
                                                                                               1 0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let shamt5 : (BitVec 1) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__473
                                                                                            12 12)
                                                                                        let shamt40 : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__473 6
                                                                                            2)
                                                                                        let mapping30_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__473
                                                                                            11 7)
                                                                                        let rsd ← do
                                                                                          (encdec_reg_backwards
                                                                                            mapping30_)
                                                                                        if ((((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled
                                                                                                 Ext_Zca))) : Bool)
                                                                                        then
                                                                                          (pure (some
                                                                                              (C_SLLI
                                                                                                (((shamt5 : (BitVec 1)) ++ (shamt40 : (BitVec 5))), rsd))))
                                                                                        else
                                                                                          (pure none))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__470 :=
                                                                                          head_exp_
                                                                                        if (((let mapping31_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__470
                                                                                                 11
                                                                                                 7)
                                                                                             (encdec_reg_backwards_matches
                                                                                               mapping31_)) && (((Sail.BitVec.extractLsb
                                                                                                   v__470
                                                                                                   15
                                                                                                   13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                   v__470
                                                                                                   1
                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let ui76 : (BitVec 2) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__470
                                                                                                3 2)
                                                                                            let ui5 : (BitVec 1) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__470
                                                                                                12
                                                                                                12)
                                                                                            let ui42 : (BitVec 3) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__470
                                                                                                6 4)
                                                                                            let mapping31_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__470
                                                                                                11 7)
                                                                                            let rd ← do
                                                                                              (encdec_reg_backwards
                                                                                                mapping31_)
                                                                                            if (((bne
                                                                                                   rd
                                                                                                   zreg) && (← (currentlyEnabled
                                                                                                     Ext_Zca))) : Bool)
                                                                                            then
                                                                                              (pure (some
                                                                                                  (C_LWSP
                                                                                                    (((ui76 : (BitVec 2)) ++ ((ui5 : (BitVec 1)) ++ (ui42 : (BitVec 3)))), rd))))
                                                                                            else
                                                                                              (pure none))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__467 :=
                                                                                              head_exp_
                                                                                            if (((let mapping32_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__467
                                                                                                     11
                                                                                                     7)
                                                                                                 (encdec_reg_backwards_matches
                                                                                                   mapping32_)) && (((Sail.BitVec.extractLsb
                                                                                                       v__467
                                                                                                       15
                                                                                                       13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                       v__467
                                                                                                       1
                                                                                                       0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let ui86 : (BitVec 3) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__467
                                                                                                    4
                                                                                                    2)
                                                                                                let ui5 : (BitVec 1) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__467
                                                                                                    12
                                                                                                    12)
                                                                                                let ui43 : (BitVec 2) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__467
                                                                                                    6
                                                                                                    5)
                                                                                                let mapping32_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__467
                                                                                                    11
                                                                                                    7)
                                                                                                let rd ← do
                                                                                                  (encdec_reg_backwards
                                                                                                    mapping32_)
                                                                                                if (((bne
                                                                                                       rd
                                                                                                       zreg) && ((xlen == 64) && (← (currentlyEnabled
                                                                                                           Ext_Zca)))) : Bool)
                                                                                                then
                                                                                                  (pure (some
                                                                                                      (C_LDSP
                                                                                                        (((ui86 : (BitVec 3)) ++ ((ui5 : (BitVec 1)) ++ (ui43 : (BitVec 2)))), rd))))
                                                                                                else
                                                                                                  (pure none))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__464 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping33_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__464
                                                                                                         6
                                                                                                         2)
                                                                                                     (encdec_reg_backwards_matches
                                                                                                       mapping33_)) && (((Sail.BitVec.extractLsb
                                                                                                           v__464
                                                                                                           15
                                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                           v__464
                                                                                                           1
                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let ui76 : (BitVec 2) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__464
                                                                                                        8
                                                                                                        7)
                                                                                                    let ui52 : (BitVec 4) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__464
                                                                                                        12
                                                                                                        9)
                                                                                                    let mapping33_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__464
                                                                                                        6
                                                                                                        2)
                                                                                                    let rs2 ← do
                                                                                                      (encdec_reg_backwards
                                                                                                        mapping33_)
                                                                                                    if ((← (currentlyEnabled
                                                                                                           Ext_Zca)) : Bool)
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          (C_SWSP
                                                                                                            (((ui76 : (BitVec 2)) ++ (ui52 : (BitVec 4))), rs2))))
                                                                                                    else
                                                                                                      (pure none))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__461 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping34_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__461
                                                                                                             6
                                                                                                             2)
                                                                                                         (encdec_reg_backwards_matches
                                                                                                           mapping34_)) && (((Sail.BitVec.extractLsb
                                                                                                               v__461
                                                                                                               15
                                                                                                               13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                               v__461
                                                                                                               1
                                                                                                               0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let ui86 : (BitVec 3) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__461
                                                                                                            9
                                                                                                            7)
                                                                                                        let ui53 : (BitVec 3) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__461
                                                                                                            12
                                                                                                            10)
                                                                                                        let mapping34_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__461
                                                                                                            6
                                                                                                            2)
                                                                                                        let rs2 ← do
                                                                                                          (encdec_reg_backwards
                                                                                                            mapping34_)
                                                                                                        if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                 Ext_Zca))) : Bool)
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              (C_SDSP
                                                                                                                (((ui86 : (BitVec 3)) ++ (ui53 : (BitVec 3))), rs2))))
                                                                                                        else
                                                                                                          (pure none))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__456 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping35_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__456
                                                                                                                 11
                                                                                                                 7)
                                                                                                             (encdec_reg_backwards_matches
                                                                                                               mapping35_)) && (((Sail.BitVec.extractLsb
                                                                                                                   v__456
                                                                                                                   15
                                                                                                                   12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                   v__456
                                                                                                                   6
                                                                                                                   0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping35_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__456
                                                                                                                11
                                                                                                                7)
                                                                                                            let rs1 ← do
                                                                                                              (encdec_reg_backwards
                                                                                                                mapping35_)
                                                                                                            if (((bne
                                                                                                                   rs1
                                                                                                                   zreg) && (← (currentlyEnabled
                                                                                                                     Ext_Zca))) : Bool)
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  (C_JR
                                                                                                                    rs1)))
                                                                                                            else
                                                                                                              (pure none))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__451 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping36_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__451
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 (encdec_reg_backwards_matches
                                                                                                                   mapping36_)) && (((Sail.BitVec.extractLsb
                                                                                                                       v__451
                                                                                                                       15
                                                                                                                       12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                       v__451
                                                                                                                       6
                                                                                                                       0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping36_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__451
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let rs1 ← do
                                                                                                                  (encdec_reg_backwards
                                                                                                                    mapping36_)
                                                                                                                if (((bne
                                                                                                                       rs1
                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                then
                                                                                                                  (pure (some
                                                                                                                      (C_JALR
                                                                                                                        rs1)))
                                                                                                                else
                                                                                                                  (pure none))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__447 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping38_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__447
                                                                                                                         6
                                                                                                                         2)
                                                                                                                     let mapping37_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__447
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping37_) && (encdec_reg_backwards_matches
                                                                                                                         mapping38_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__447
                                                                                                                           15
                                                                                                                           12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__447
                                                                                                                           1
                                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping38_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__447
                                                                                                                        6
                                                                                                                        2)
                                                                                                                    let mapping37_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__447
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping37_)), (← (encdec_reg_backwards
                                                                                                                        mapping38_))) with
                                                                                                                    | (rd, rs2) =>
                                                                                                                      (do
                                                                                                                        if (((bne
                                                                                                                               rs2
                                                                                                                               zreg) && (← (currentlyEnabled
                                                                                                                                 Ext_Zca))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (C_MV
                                                                                                                                (rd, rs2))))
                                                                                                                        else
                                                                                                                          (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__437 :=
                                                                                                                      head_exp_
                                                                                                                    if (((← (currentlyEnabled
                                                                                                                             Ext_Zca)) && (v__437 == (0x9002#16 : (BitVec 16)))) : Bool)
                                                                                                                    then
                                                                                                                      (pure (some
                                                                                                                          (C_EBREAK
                                                                                                                            ())))
                                                                                                                    else
                                                                                                                      (do
                                                                                                                        if (((let mapping40_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__437
                                                                                                                                 6
                                                                                                                                 2)
                                                                                                                             let mapping39_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__437
                                                                                                                                 11
                                                                                                                                 7)
                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                 mapping39_) && (encdec_reg_backwards_matches
                                                                                                                                 mapping40_))) && (((Sail.BitVec.extractLsb
                                                                                                                                   v__437
                                                                                                                                   15
                                                                                                                                   12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                                   v__437
                                                                                                                                   1
                                                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let mapping40_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__437
                                                                                                                                6
                                                                                                                                2)
                                                                                                                            let mapping39_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__437
                                                                                                                                11
                                                                                                                                7)
                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                mapping39_)), (← (encdec_reg_backwards
                                                                                                                                mapping40_))) with
                                                                                                                            | (rsd, rs2) =>
                                                                                                                              (do
                                                                                                                                if (((bne
                                                                                                                                       rs2
                                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (C_ADD
                                                                                                                                        (rsd, rs2))))
                                                                                                                                else
                                                                                                                                  (pure none)))
                                                                                                                        else
                                                                                                                          (pure none))) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (match head_exp_ with
                                                                                                                    | s =>
                                                                                                                      (pure (C_ILLEGAL
                                                                                                                          s)))))))))))))))))))))))))))))))

noncomputable def encdec_compressed_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .C_NOP v__571 =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDI4SPN (rd, v__572) =>
    (do
      if ((← do
           let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__572 7 4)
           let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__572 7 4)
           let nz54 : (BitVec 2) := (Sail.BitVec.extractLsb v__572 3 2)
           let nz3 : (BitVec 1) := (Sail.BitVec.extractLsb v__572 1 1)
           let nz2 : (BitVec 1) := (Sail.BitVec.extractLsb v__572 0 0)
           (pure (((nz96 ++ (nz54 ++ (nz3 ++ nz2))) != 0b00000000#8) && (← (currentlyEnabled
                   Ext_Zca))))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LW (v__573, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_LD (v__574, rs1, rd) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SW (v__575, rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SD (v__576, rs1, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDI (v__577, rsd) =>
    (do
      if (((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_JAL v__578 =>
    (do
      if (((xlen == 32) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDIW (v__579, rsd) =>
    (do
      if (((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LI (v__580, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDI16SP v__581 =>
    (do
      if ((← do
           let nzi9 : (BitVec 1) := (Sail.BitVec.extractLsb v__581 5 5)
           let nzi9 : (BitVec 1) := (Sail.BitVec.extractLsb v__581 5 5)
           let nzi87 : (BitVec 2) := (Sail.BitVec.extractLsb v__581 4 3)
           let nzi6 : (BitVec 1) := (Sail.BitVec.extractLsb v__581 2 2)
           let nzi5 : (BitVec 1) := (Sail.BitVec.extractLsb v__581 1 1)
           let nzi4 : (BitVec 1) := (Sail.BitVec.extractLsb v__581 0 0)
           (pure (((nzi9 ++ (nzi87 ++ (nzi6 ++ (nzi5 ++ nzi4)))) != 0b000000#6) && (← (currentlyEnabled
                   Ext_Zca))))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LUI (v__582, rd) =>
    (do
      if ((← do
           let imm17 : (BitVec 1) := (Sail.BitVec.extractLsb v__582 5 5)
           let imm17 : (BitVec 1) := (Sail.BitVec.extractLsb v__582 5 5)
           let imm1612 : (BitVec 5) := (Sail.BitVec.extractLsb v__582 4 0)
           (pure ((bne rd sp) && (((imm17 ++ imm1612) != 0b000000#6) && (← (currentlyEnabled
                     Ext_Zca)))))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SRLI (v__583, rsd) =>
    (do
      if ((← do
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__583 5 5)
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__583 5 5)
           (pure (((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled Ext_Zca))))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SRAI (v__584, rsd) =>
    (do
      if ((← do
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__584 5 5)
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__584 5 5)
           (pure (((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled Ext_Zca))))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ANDI (v__585, rsd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SUB (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_XOR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_OR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_AND (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SUBW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_J v__586 =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_BEQZ (v__587, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_BNEZ (v__588, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SLLI (v__589, rsd) =>
    (do
      if ((← do
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__589 5 5)
           let shamt5 : (BitVec 1) := (Sail.BitVec.extractLsb v__589 5 5)
           (pure (((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled Ext_Zca))))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LWSP (v__590, rd) =>
    (do
      if (((bne rd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LDSP (v__591, rd) =>
    (do
      if (((bne rd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SWSP (v__592, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SDSP (v__593, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_JR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_JALR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_MV (rd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_EBREAK () =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADD (rsd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ILLEGAL s => (pure true)
  | _ => (pure false)

noncomputable def encdec_compressed_backwards_matches (arg_ : (BitVec 16)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__721 := head_exp_
    if (((← (currentlyEnabled Ext_Zca)) && (((Sail.BitVec.extractLsb v__721 15 13) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                 v__721 11 7) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb v__721 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
    then (pure (some true))
    else
      (do
        if (((let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__721 4 2)
             (encdec_creg_backwards_matches mapping0_)) && (((Sail.BitVec.extractLsb v__721 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                   v__721 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let nz96 : (BitVec 4) := (Sail.BitVec.extractLsb v__721 10 7)
            let nz54 : (BitVec 2) := (Sail.BitVec.extractLsb v__721 12 11)
            let nz3 : (BitVec 1) := (Sail.BitVec.extractLsb v__721 5 5)
            let nz2 : (BitVec 1) := (Sail.BitVec.extractLsb v__721 6 6)
            let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__721 4 2)
            let rd := (encdec_creg_backwards mapping0_)
            if ((((nz96 ++ (nz54 ++ (nz3 ++ nz2))) != 0b00000000#8) && (← (currentlyEnabled
                     Ext_Zca))) : Bool)
            then (pure (some true))
            else (pure none))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__718 := head_exp_
        if (((let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__718 4 2)
             let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__718 9 7)
             ((encdec_creg_backwards_matches mapping1_) && (encdec_creg_backwards_matches mapping2_))) && (((Sail.BitVec.extractLsb
                   v__718 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__718 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__718 4 2)
            let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__718 9 7)
            match ((encdec_creg_backwards mapping1_), (encdec_creg_backwards mapping2_)) with
            | (rs1, rd) =>
              (do
                if ((← (currentlyEnabled Ext_Zca)) : Bool)
                then (pure (some true))
                else (pure none)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__715 := head_exp_
            if (((let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__715 4 2)
                 let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__715 9 7)
                 ((encdec_creg_backwards_matches mapping3_) && (encdec_creg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__715 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__715 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
            then
              (do
                let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__715 4 2)
                let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__715 9 7)
                match ((encdec_creg_backwards mapping3_), (encdec_creg_backwards mapping4_)) with
                | (rs1, rd) =>
                  (do
                    if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
                    then (pure (some true))
                    else (pure none)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__712 := head_exp_
                if (((let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__712 4 2)
                     let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__712 9 7)
                     ((encdec_creg_backwards_matches mapping5_) && (encdec_creg_backwards_matches
                         mapping6_))) && (((Sail.BitVec.extractLsb v__712 15 13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                           v__712 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                then
                  (do
                    let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__712 4 2)
                    let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__712 9 7)
                    match ((encdec_creg_backwards mapping5_), (encdec_creg_backwards mapping6_)) with
                    | (rs1, rs2) =>
                      (do
                        if ((← (currentlyEnabled Ext_Zca)) : Bool)
                        then (pure (some true))
                        else (pure none)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__709 := head_exp_
                    if (((let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__709 4 2)
                         let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__709 9 7)
                         ((encdec_creg_backwards_matches mapping7_) && (encdec_creg_backwards_matches
                             mapping8_))) && (((Sail.BitVec.extractLsb v__709 15 13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                               v__709 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                    then
                      (do
                        let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__709 4 2)
                        let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__709 9 7)
                        match ((encdec_creg_backwards mapping7_), (encdec_creg_backwards mapping8_)) with
                        | (rs1, rs2) =>
                          (do
                            if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
                            then (pure (some true))
                            else (pure none)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__706 := head_exp_
                        if (((let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__706 11 7)
                             (encdec_reg_backwards_matches mapping9_)) && (((Sail.BitVec.extractLsb
                                   v__706 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__706 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                        then
                          (do
                            let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__706 11 7)
                            let rsd ← do (encdec_reg_backwards mapping9_)
                            if (((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
                            then (pure (some true))
                            else (pure none))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__700 := head_exp_
                            if ((((xlen == 32) && (← (currentlyEnabled Ext_Zca))) && (((Sail.BitVec.extractLsb
                                       v__700 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__700 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                            then (pure (some true))
                            else
                              (do
                                if (((let mapping10_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__700 11 7)
                                     (encdec_reg_backwards_matches mapping10_)) && (((Sail.BitVec.extractLsb
                                           v__700 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__700 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping10_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__700 11 7)
                                    let rsd ← do (encdec_reg_backwards mapping10_)
                                    if (((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled
                                               Ext_Zca)))) : Bool)
                                    then (pure (some true))
                                    else (pure none))
                                else (pure none))) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__697 := head_exp_
                                if (((let mapping11_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__697 11 7)
                                     (encdec_reg_backwards_matches mapping11_)) && (((Sail.BitVec.extractLsb
                                           v__697 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__697 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping11_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__697 11 7)
                                    let rd ← do (encdec_reg_backwards mapping11_)
                                    if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                    then (pure (some true))
                                    else (pure none))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__690 := head_exp_
                                    if (((← do
                                           let nzi9 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__690 12 12)
                                           let nzi87 : (BitVec 2) :=
                                             (Sail.BitVec.extractLsb v__690 4 3)
                                           let nzi6 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__690 5 5)
                                           let nzi5 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__690 2 2)
                                           let nzi4 : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__690 6 6)
                                           (pure (((nzi9 ++ (nzi87 ++ (nzi6 ++ (nzi5 ++ nzi4)))) != 0b000000#6) && (← (currentlyEnabled
                                                   Ext_Zca))))) && (((Sail.BitVec.extractLsb v__690
                                               15 13) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                 v__690 11 7) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb
                                                 v__690 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                    then (pure (some true))
                                    else
                                      (do
                                        if (((let mapping12_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__690 11 7)
                                             (encdec_reg_backwards_matches mapping12_)) && (((Sail.BitVec.extractLsb
                                                   v__690 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__690 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                        then
                                          (do
                                            let mapping12_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__690 11 7)
                                            let imm17 : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__690 12 12)
                                            let imm1612 : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__690 6 2)
                                            let rd ← do (encdec_reg_backwards mapping12_)
                                            if (((bne rd sp) && (((imm17 ++ imm1612) != 0b000000#6) && (← (currentlyEnabled
                                                       Ext_Zca)))) : Bool)
                                            then (pure (some true))
                                            else (pure none))
                                        else (pure none))) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__686 := head_exp_
                                        if (((let mapping13_ : (BitVec 3) :=
                                               (Sail.BitVec.extractLsb v__686 9 7)
                                             (encdec_creg_backwards_matches mapping13_)) && (((Sail.BitVec.extractLsb
                                                   v__686 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                     v__686 11 10) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                     v__686 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                        then
                                          (do
                                            let shamt5 : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__686 12 12)
                                            let mapping13_ : (BitVec 3) :=
                                              (Sail.BitVec.extractLsb v__686 9 7)
                                            let rsd := (encdec_creg_backwards mapping13_)
                                            if ((((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled
                                                     Ext_Zca))) : Bool)
                                            then (pure (some true))
                                            else (pure none))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__682 := head_exp_
                                            if (((let mapping14_ : (BitVec 3) :=
                                                   (Sail.BitVec.extractLsb v__682 9 7)
                                                 (encdec_creg_backwards_matches mapping14_)) && (((Sail.BitVec.extractLsb
                                                       v__682 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                         v__682 11 10) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                         v__682 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                            then
                                              (do
                                                let shamt5 : (BitVec 1) :=
                                                  (Sail.BitVec.extractLsb v__682 12 12)
                                                let mapping14_ : (BitVec 3) :=
                                                  (Sail.BitVec.extractLsb v__682 9 7)
                                                let rsd := (encdec_creg_backwards mapping14_)
                                                if ((((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled
                                                         Ext_Zca))) : Bool)
                                                then (pure (some true))
                                                else (pure none))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__678 := head_exp_
                                                if (((let mapping15_ : (BitVec 3) :=
                                                       (Sail.BitVec.extractLsb v__678 9 7)
                                                     (encdec_creg_backwards_matches mapping15_)) && (((Sail.BitVec.extractLsb
                                                           v__678 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                             v__678 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                             v__678 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping15_ : (BitVec 3) :=
                                                      (Sail.BitVec.extractLsb v__678 9 7)
                                                    let rsd := (encdec_creg_backwards mapping15_)
                                                    if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                    then (pure (some true))
                                                    else (pure none))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__672 := head_exp_
                                                    if (((let mapping17_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__672 4 2)
                                                         let mapping16_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__672 9 7)
                                                         ((encdec_creg_backwards_matches mapping16_) && (encdec_creg_backwards_matches
                                                             mapping17_))) && (((Sail.BitVec.extractLsb
                                                               v__672 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                 v__672 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                 v__672 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping17_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__672 4 2)
                                                        let mapping16_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__672 9 7)
                                                        match ((encdec_creg_backwards mapping16_), (encdec_creg_backwards
                                                          mapping17_)) with
                                                        | (rsd, rs2) =>
                                                          (do
                                                            if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                            then (pure (some true))
                                                            else (pure none)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__666 := head_exp_
                                                        if (((let mapping19_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__666 4 2)
                                                             let mapping18_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__666 9 7)
                                                             ((encdec_creg_backwards_matches
                                                                 mapping18_) && (encdec_creg_backwards_matches
                                                                 mapping19_))) && (((Sail.BitVec.extractLsb
                                                                   v__666 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                     v__666 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                     v__666 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping19_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__666 4 2)
                                                            let mapping18_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__666 9 7)
                                                            match ((encdec_creg_backwards mapping18_), (encdec_creg_backwards
                                                              mapping19_)) with
                                                            | (rsd, rs2) =>
                                                              (do
                                                                if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                                then (pure (some true))
                                                                else (pure none)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__660 := head_exp_
                                                            if (((let mapping21_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__660 4
                                                                     2)
                                                                 let mapping20_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__660 9
                                                                     7)
                                                                 ((encdec_creg_backwards_matches
                                                                     mapping20_) && (encdec_creg_backwards_matches
                                                                     mapping21_))) && (((Sail.BitVec.extractLsb
                                                                       v__660 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                         v__660 6 5) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                         v__660 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping21_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__660 4 2)
                                                                let mapping20_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__660 9 7)
                                                                match ((encdec_creg_backwards
                                                                  mapping20_), (encdec_creg_backwards
                                                                  mapping21_)) with
                                                                | (rsd, rs2) =>
                                                                  (do
                                                                    if ((← (currentlyEnabled
                                                                           Ext_Zca)) : Bool)
                                                                    then (pure (some true))
                                                                    else (pure none)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__654 := head_exp_
                                                                if (((let mapping23_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__654 4 2)
                                                                     let mapping22_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__654 9 7)
                                                                     ((encdec_creg_backwards_matches
                                                                         mapping22_) && (encdec_creg_backwards_matches
                                                                         mapping23_))) && (((Sail.BitVec.extractLsb
                                                                           v__654 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                             v__654 6 5) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                             v__654 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping23_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__654
                                                                        4 2)
                                                                    let mapping22_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__654
                                                                        9 7)
                                                                    match ((encdec_creg_backwards
                                                                      mapping22_), (encdec_creg_backwards
                                                                      mapping23_)) with
                                                                    | (rsd, rs2) =>
                                                                      (do
                                                                        if ((← (currentlyEnabled
                                                                               Ext_Zca)) : Bool)
                                                                        then (pure (some true))
                                                                        else (pure none)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__648 := head_exp_
                                                                    if (((let mapping25_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__648 4 2)
                                                                         let mapping24_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__648 9 7)
                                                                         ((encdec_creg_backwards_matches
                                                                             mapping24_) && (encdec_creg_backwards_matches
                                                                             mapping25_))) && (((Sail.BitVec.extractLsb
                                                                               v__648 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                 v__648 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                 v__648 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping25_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__648 4 2)
                                                                        let mapping24_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__648 9 7)
                                                                        match ((encdec_creg_backwards
                                                                          mapping24_), (encdec_creg_backwards
                                                                          mapping25_)) with
                                                                        | (rsd, rs2) =>
                                                                          (do
                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                     Ext_Zca))) : Bool)
                                                                            then (pure (some true))
                                                                            else (pure none)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__642 := head_exp_
                                                                        if (((let mapping27_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__642 4 2)
                                                                             let mapping26_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__642 9 7)
                                                                             ((encdec_creg_backwards_matches
                                                                                 mapping26_) && (encdec_creg_backwards_matches
                                                                                 mapping27_))) && (((Sail.BitVec.extractLsb
                                                                                   v__642 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                     v__642 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                     v__642 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping27_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__642 4 2)
                                                                            let mapping26_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__642 9 7)
                                                                            match ((encdec_creg_backwards
                                                                              mapping26_), (encdec_creg_backwards
                                                                              mapping27_)) with
                                                                            | (rsd, rs2) =>
                                                                              (do
                                                                                if (((xlen == 64) && (← (currentlyEnabled
                                                                                         Ext_Zca))) : Bool)
                                                                                then
                                                                                  (pure (some true))
                                                                                else (pure none)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__636 := head_exp_
                                                                            if (((← (currentlyEnabled
                                                                                     Ext_Zca)) && (((Sail.BitVec.extractLsb
                                                                                       v__636 15 13) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                       v__636 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                            then (pure (some true))
                                                                            else
                                                                              (do
                                                                                if (((let mapping28_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__636 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping28_)) && (((Sail.BitVec.extractLsb
                                                                                           v__636 15
                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__636 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping28_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__636 9 7)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping28_)
                                                                                    if ((← (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          true))
                                                                                    else (pure none))
                                                                                else (pure none))) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__633 :=
                                                                                  head_exp_
                                                                                if (((let mapping29_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__633 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping29_)) && (((Sail.BitVec.extractLsb
                                                                                           v__633 15
                                                                                           13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__633 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping29_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__633 9 7)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping29_)
                                                                                    if ((← (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          true))
                                                                                    else (pure none))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__630 :=
                                                                                      head_exp_
                                                                                    if (((let mapping30_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__630
                                                                                             11 7)
                                                                                         (encdec_reg_backwards_matches
                                                                                           mapping30_)) && (((Sail.BitVec.extractLsb
                                                                                               v__630
                                                                                               15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__630
                                                                                               1 0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let shamt5 : (BitVec 1) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__630
                                                                                            12 12)
                                                                                        let mapping30_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__630
                                                                                            11 7)
                                                                                        let rsd ← do
                                                                                          (encdec_reg_backwards
                                                                                            mapping30_)
                                                                                        if ((((xlen == 64) || (shamt5 == 0#1)) && (← (currentlyEnabled
                                                                                                 Ext_Zca))) : Bool)
                                                                                        then
                                                                                          (pure (some
                                                                                              true))
                                                                                        else
                                                                                          (pure none))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__627 :=
                                                                                          head_exp_
                                                                                        if (((let mapping31_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__627
                                                                                                 11
                                                                                                 7)
                                                                                             (encdec_reg_backwards_matches
                                                                                               mapping31_)) && (((Sail.BitVec.extractLsb
                                                                                                   v__627
                                                                                                   15
                                                                                                   13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                   v__627
                                                                                                   1
                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping31_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__627
                                                                                                11 7)
                                                                                            let rd ← do
                                                                                              (encdec_reg_backwards
                                                                                                mapping31_)
                                                                                            if (((bne
                                                                                                   rd
                                                                                                   zreg) && (← (currentlyEnabled
                                                                                                     Ext_Zca))) : Bool)
                                                                                            then
                                                                                              (pure (some
                                                                                                  true))
                                                                                            else
                                                                                              (pure none))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__624 :=
                                                                                              head_exp_
                                                                                            if (((let mapping32_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__624
                                                                                                     11
                                                                                                     7)
                                                                                                 (encdec_reg_backwards_matches
                                                                                                   mapping32_)) && (((Sail.BitVec.extractLsb
                                                                                                       v__624
                                                                                                       15
                                                                                                       13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                       v__624
                                                                                                       1
                                                                                                       0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping32_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__624
                                                                                                    11
                                                                                                    7)
                                                                                                let rd ← do
                                                                                                  (encdec_reg_backwards
                                                                                                    mapping32_)
                                                                                                if (((bne
                                                                                                       rd
                                                                                                       zreg) && ((xlen == 64) && (← (currentlyEnabled
                                                                                                           Ext_Zca)))) : Bool)
                                                                                                then
                                                                                                  (pure (some
                                                                                                      true))
                                                                                                else
                                                                                                  (pure none))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__621 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping33_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__621
                                                                                                         6
                                                                                                         2)
                                                                                                     (encdec_reg_backwards_matches
                                                                                                       mapping33_)) && (((Sail.BitVec.extractLsb
                                                                                                           v__621
                                                                                                           15
                                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                           v__621
                                                                                                           1
                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping33_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__621
                                                                                                        6
                                                                                                        2)
                                                                                                    let rs2 ← do
                                                                                                      (encdec_reg_backwards
                                                                                                        mapping33_)
                                                                                                    if ((← (currentlyEnabled
                                                                                                           Ext_Zca)) : Bool)
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          true))
                                                                                                    else
                                                                                                      (pure none))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__618 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping34_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__618
                                                                                                             6
                                                                                                             2)
                                                                                                         (encdec_reg_backwards_matches
                                                                                                           mapping34_)) && (((Sail.BitVec.extractLsb
                                                                                                               v__618
                                                                                                               15
                                                                                                               13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                               v__618
                                                                                                               1
                                                                                                               0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping34_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__618
                                                                                                            6
                                                                                                            2)
                                                                                                        let rs2 ← do
                                                                                                          (encdec_reg_backwards
                                                                                                            mapping34_)
                                                                                                        if (((xlen == 64) && (← (currentlyEnabled
                                                                                                                 Ext_Zca))) : Bool)
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              true))
                                                                                                        else
                                                                                                          (pure none))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__613 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping35_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__613
                                                                                                                 11
                                                                                                                 7)
                                                                                                             (encdec_reg_backwards_matches
                                                                                                               mapping35_)) && (((Sail.BitVec.extractLsb
                                                                                                                   v__613
                                                                                                                   15
                                                                                                                   12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                   v__613
                                                                                                                   6
                                                                                                                   0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping35_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__613
                                                                                                                11
                                                                                                                7)
                                                                                                            let rs1 ← do
                                                                                                              (encdec_reg_backwards
                                                                                                                mapping35_)
                                                                                                            if (((bne
                                                                                                                   rs1
                                                                                                                   zreg) && (← (currentlyEnabled
                                                                                                                     Ext_Zca))) : Bool)
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  true))
                                                                                                            else
                                                                                                              (pure none))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__608 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping36_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__608
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 (encdec_reg_backwards_matches
                                                                                                                   mapping36_)) && (((Sail.BitVec.extractLsb
                                                                                                                       v__608
                                                                                                                       15
                                                                                                                       12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                       v__608
                                                                                                                       6
                                                                                                                       0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping36_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__608
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let rs1 ← do
                                                                                                                  (encdec_reg_backwards
                                                                                                                    mapping36_)
                                                                                                                if (((bne
                                                                                                                       rs1
                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                then
                                                                                                                  (pure (some
                                                                                                                      true))
                                                                                                                else
                                                                                                                  (pure none))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__604 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping38_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__604
                                                                                                                         6
                                                                                                                         2)
                                                                                                                     let mapping37_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__604
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping37_) && (encdec_reg_backwards_matches
                                                                                                                         mapping38_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__604
                                                                                                                           15
                                                                                                                           12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__604
                                                                                                                           1
                                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping38_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__604
                                                                                                                        6
                                                                                                                        2)
                                                                                                                    let mapping37_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__604
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping37_)), (← (encdec_reg_backwards
                                                                                                                        mapping38_))) with
                                                                                                                    | (rd, rs2) =>
                                                                                                                      (do
                                                                                                                        if (((bne
                                                                                                                               rs2
                                                                                                                               zreg) && (← (currentlyEnabled
                                                                                                                                 Ext_Zca))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__594 :=
                                                                                                                      head_exp_
                                                                                                                    if (((← (currentlyEnabled
                                                                                                                             Ext_Zca)) && (v__594 == (0x9002#16 : (BitVec 16)))) : Bool)
                                                                                                                    then
                                                                                                                      (pure (some
                                                                                                                          true))
                                                                                                                    else
                                                                                                                      (do
                                                                                                                        if (((let mapping40_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__594
                                                                                                                                 6
                                                                                                                                 2)
                                                                                                                             let mapping39_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__594
                                                                                                                                 11
                                                                                                                                 7)
                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                 mapping39_) && (encdec_reg_backwards_matches
                                                                                                                                 mapping40_))) && (((Sail.BitVec.extractLsb
                                                                                                                                   v__594
                                                                                                                                   15
                                                                                                                                   12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                                   v__594
                                                                                                                                   1
                                                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let mapping40_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__594
                                                                                                                                6
                                                                                                                                2)
                                                                                                                            let mapping39_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__594
                                                                                                                                11
                                                                                                                                7)
                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                mapping39_)), (← (encdec_reg_backwards
                                                                                                                                mapping40_))) with
                                                                                                                            | (rsd, rs2) =>
                                                                                                                              (do
                                                                                                                                if (((bne
                                                                                                                                       rs2
                                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (pure none)))
                                                                                                                        else
                                                                                                                          (pure none))) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (match head_exp_ with
                                                                                                                    | s =>
                                                                                                                      (pure true))))))))))))))))))))))))))))))

def execute_WFI (_ : Unit) : SailM ExecutionResult := do
  match (← readReg cur_privilege) with
  | Machine => (pure (Enter_Wait WAIT_WFI))
  | Supervisor =>
    (do
      if (((_get_Mstatus_TW (← readReg mstatus)) == 1#1) : Bool)
      then (pure (Illegal_Instruction ()))
      else (pure (Enter_Wait WAIT_WFI)))
  | User => (pure (Illegal_Instruction ()))
  | VirtualUser =>
    (internal_error "model/extensions/I/base_insts.sail" 656 "Hypervisor extension not supported")
  | VirtualSupervisor =>
    (internal_error "model/extensions/I/base_insts.sail" 657 "Hypervisor extension not supported")

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 32) (imm ++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | LUI => (pure off)
      | AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, width ∈ {1, 2, 4, 8} -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 32) imm)
  assert (width ≤b xlen_bytes) "model/extensions/I/base_insts.sail:349.28-349.29"
  if ((width == 1) : Bool)
  then
    (do
      let data ← (( do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 7 0)) ) : SailM
        (BitVec 8) )
      match (← (vmem_write rs1 offset 1 data (Write Data) false false false)) with
      | .Ok _ => (pure RETIRE_SUCCESS)
      | .Err e => (pure e))
  else
    (do
      if ((width == 2) : Bool)
      then
        (do
          let data ← (( do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 15 0)) ) : SailM
            (BitVec 16) )
          match (← (vmem_write rs1 offset 2 data (Write Data) false false false)) with
          | .Ok _ => (pure RETIRE_SUCCESS)
          | .Err e => (pure e))
      else
        (do
          let data ← (( do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0)) ) : SailM
            (BitVec 32) )
          match (← (vmem_write rs1 offset 4 data (Write Data) false false false)) with
          | .Ok _ => (pure RETIRE_SUCCESS)
          | .Err e => (pure e)))

def execute_SRET (_ : Unit) : SailM ExecutionResult := do
  let sret_illegal ← (( do
    match (← readReg cur_privilege) with
    | User => (pure true)
    | Supervisor =>
      (pure ((not (← (currentlyEnabled Ext_S))) || ((_get_Mstatus_TSR (← readReg mstatus)) == 1#1)))
    | Machine => (pure (not (← (currentlyEnabled Ext_S))))
    | VirtualUser =>
      (internal_error "model/extensions/I/base_insts.sail" 617 "Hypervisor extension not supported")
    | VirtualSupervisor =>
      (internal_error "model/extensions/I/base_insts.sail" 618 "Hypervisor extension not supported")
    ) : SailM Bool )
  if (sret_illegal : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Supervisor)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          (set_next_pc
            (← (exception_handler (← readReg cur_privilege) (CTL_SRET ()) (← readReg PC))))
          (pure RETIRE_SUCCESS)))

def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | SLLIW => (shift_bits_left rs1_val shamt)
    | SRLIW => (shift_bits_right rs1_val shamt)
    | SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 32) result))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

def execute_SFENCE_VMA (rs1 : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  let addr ← do
    if ((bne rs1 zreg) : Bool)
    then (pure (some (← (rX_bits rs1))))
    else (pure none)
  let asid ← do
    if ((bne rs2 zreg) : Bool)
    then (pure (some (Sail.BitVec.extractLsb (← (rX_bits rs2)) (asidlen -i 1) 0)))
    else (pure none)
  match (← readReg cur_privilege) with
  | User => (pure (Illegal_Instruction ()))
  | Supervisor =>
    (do
      match (_get_Mstatus_TVM (← readReg mstatus)) with
      | 1 => (pure (Illegal_Instruction ()))
      | _ =>
        (do
          (flush_TLB asid addr)
          (pure RETIRE_SUCCESS)))
  | Machine =>
    (do
      (flush_TLB asid addr)
      (pure RETIRE_SUCCESS))
  | VirtualUser =>
    (internal_error "model/extensions/I/base_insts.sail" 682 "Hypervisor extension not supported")
  | VirtualSupervisor =>
    (internal_error "model/extensions/I/base_insts.sail" 683 "Hypervisor extension not supported")

def execute_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | ADDW => (rs1_val + rs2_val)
    | SUBW => (rs1_val - rs2_val)
    | SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 32) result))
  (pure RETIRE_SUCCESS)

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | SLT =>
        (pure (zero_extend (m := 32)
            (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | SLTU =>
        (pure (zero_extend (m := 32)
            (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex162541_ : Bool -/
def execute_REMW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (sign_extend (m := 32) (to_bits_truncate (l := 32) remainder)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex162550_ : Bool -/
def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits_truncate (l := 32) remainder))
  (pure RETIRE_SUCCESS)

def execute_MULW (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int := (BitVec.toInt rs1_bits)
  let rs2_int := (BitVec.toInt rs2_bits)
  let result32 : (BitVec 32) := (to_bits_truncate (l := 32) (rs1_int *i rs2_int))
  (wX_bits rd (sign_extend (m := 32) result32))
  (pure RETIRE_SUCCESS)

def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (mul_op.signed_rs1 : Bool)
    then (BitVec.toInt rs1_bits)
    else (BitVec.toNatInt rs1_bits)
  let rs2_int :=
    if (mul_op.signed_rs2 : Bool)
    then (BitVec.toInt rs2_bits)
    else (BitVec.toNatInt rs2_bits)
  let result_wide := (to_bits_truncate (l := (2 *i xlen)) (rs1_int *i rs2_int))
  (wX_bits rd
    (if (mul_op.high : Bool)
    then (Sail.BitVec.extractLsb result_wide ((2 *i xlen) -i 1) xlen)
    else (Sail.BitVec.extractLsb result_wide (xlen -i 1) 0)))
  (pure RETIRE_SUCCESS)

def execute_MRET (_ : Unit) : SailM ExecutionResult := do
  if ((bne (← readReg cur_privilege) Machine) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Machine)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          (set_next_pc
            (← (exception_handler (← readReg cur_privilege) (CTL_MRET ()) (← readReg PC))))
          (pure RETIRE_SUCCESS)))

def execute_LPAD (lpl : (BitVec 20)) : SailM ExecutionResult := do
  if ((← (is_landing_pad_expected ())) : Bool)
  then
    (do
      let unaligned_pc ← do (pure ((Sail.BitVec.extractLsb (← (get_arch_pc ())) 1 0) != 0b00#2))
      let label_mismatch ← do
        (pure (((Sail.BitVec.extractLsb (← (rX (Regno 7))) 31 12) != lpl) && (lpl != (zeros
                (n := 20)))))
      if ((unaligned_pc || label_mismatch) : Bool)
      then
        (pure (Trap
            ((← readReg cur_privilege), (CTL_TRAP (make_landing_pad_exception ())), (← readReg PC))))
      else
        (do
          (reset_elp ())
          (pure RETIRE_SUCCESS)))
  else (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, k_ex162587_ : Bool, width ∈ {1, 2, 4, 8} -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 32) imm)
  assert (width ≤b xlen_bytes) "model/extensions/I/base_insts.sail:287.28-287.29"
  if ((width == 1) : Bool)
  then
    (do
      match (← (vmem_read rs1 offset 1 (Read Data) false false false)) with
      | .Ok data =>
        (do
          let data : (BitVec 8) := data
          (wX_bits rd (extend_value is_unsigned data))
          (pure RETIRE_SUCCESS))
      | .Err e => (pure e))
  else
    (do
      if ((width == 2) : Bool)
      then
        (do
          match (← (vmem_read rs1 offset 2 (Read Data) false false false)) with
          | .Ok data =>
            (do
              let data : (BitVec 16) := data
              (wX_bits rd (extend_value is_unsigned data))
              (pure RETIRE_SUCCESS))
          | .Err e => (pure e))
      else
        (do
          match (← (vmem_read rs1 offset 4 (Read Data) false false false)) with
          | .Ok data =>
            (do
              let data : (BitVec 32) := data
              (wX_bits rd (extend_value is_unsigned data))
              (pure RETIRE_SUCCESS))
          | .Err e => (pure e)))

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 32) imm)))
  match (← (jump_to (BitVec.update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 32) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 32) imm)
  (wX_bits rd
    (← do
      match op with
      | ADDI => (pure ((← (rX_bits rs1)) + immext))
      | SLTI => (pure (zero_extend (m := 32) (bool_to_bits (zopz0zI_s (← (rX_bits rs1)) immext))))
      | SLTIU =>
        (pure (zero_extend (m := 32) (bool_to_bits (zopz0zI_u (← (rX_bits rs1)) immext))))
      | ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)

def execute_ILLEGAL (s : (BitVec 32)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_FENCE_TSO (_ : Unit) : SailM ExecutionResult := do
  (sail_barrier Barrier_RISCV_tso)
  (pure RETIRE_SUCCESS)

def execute_FENCE_RESERVED (fm : (BitVec 4)) (pred : (BitVec 4)) (succ : (BitVec 4)) (rs : regidx) (rd : regidx) : ExecutionResult :=
  RETIRE_SUCCESS

def execute_FENCEI_RESERVED (imm : (BitVec 12)) (rs : regidx) (rd : regidx) : ExecutionResult :=
  RETIRE_SUCCESS

def execute_FENCEI (_ : Unit) : ExecutionResult :=
  RETIRE_SUCCESS

def execute_FENCE (pred : (BitVec 4)) (succ : (BitVec 4)) : SailM ExecutionResult := do
  let fiom ← do (is_fiom_active ())
  let pred := (effective_fence_set pred fiom)
  let succ := (effective_fence_set succ fiom)
  match (pred, succ) with
  | (v__728, v__729) =>
    (do
      if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
               v__729 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
      then (sail_barrier Barrier_RISCV_rw_rw)
      else
        (do
          if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                   v__729 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
          then (sail_barrier Barrier_RISCV_r_rw)
          else
            (do
              if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                       v__729 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
              then (sail_barrier Barrier_RISCV_r_r)
              else
                (do
                  if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                           v__729 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                  then (sail_barrier Barrier_RISCV_rw_w)
                  else
                    (do
                      if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                               v__729 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                      then (sail_barrier Barrier_RISCV_w_w)
                      else
                        (do
                          if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                   v__729 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                          then (sail_barrier Barrier_RISCV_w_rw)
                          else
                            (do
                              if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                       v__729 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                              then (sail_barrier Barrier_RISCV_rw_r)
                              else
                                (do
                                  if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                           v__729 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                                  then (sail_barrier Barrier_RISCV_r_w)
                                  else
                                    (do
                                      if ((((Sail.BitVec.extractLsb v__728 1 0) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                               v__729 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                                      then (sail_barrier Barrier_RISCV_w_r)
                                      else
                                        (if (((Sail.BitVec.extractLsb v__729 1 0) == (0b00#2 : (BitVec 2))) : Bool)
                                        then (pure ())
                                        else
                                          (if (((Sail.BitVec.extractLsb v__728 1 0) == (0b00#2 : (BitVec 2))) : Bool)
                                          then (pure ())
                                          else
                                            (let _ : Unit := (print "FIXME: unsupported fence")
                                            (pure ())))))))))))))
  (pure RETIRE_SUCCESS)

def execute_ECALL (_ : Unit) : SailM ExecutionResult := do
  let trap ← (( do
    match (← readReg cur_privilege) with
    | User => (pure (E_U_EnvCall ()))
    | Supervisor => (pure (E_S_EnvCall ()))
    | Machine => (pure (E_M_EnvCall ()))
    | VirtualUser =>
      (internal_error "model/extensions/I/base_insts.sail" 574 "Hypervisor extension not supported")
    | VirtualSupervisor =>
      (internal_error "model/extensions/I/base_insts.sail" 575 "Hypervisor extension not supported")
    ) : SailM ExceptionType )
  let t : sync_exception :=
    { trap := trap
      excinfo := (none : (Option xlenbits))
      ext := none }
  (pure (Trap ((← readReg cur_privilege), (CTL_TRAP t), (← readReg PC))))

def execute_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (pure (Memory_Exception ((Virtaddr (← readReg PC)), (E_Breakpoint ()))))

/-- Type quantifiers: k_ex162657_ : Bool -/
def execute_DIVW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
    then (Neg.neg (2 ^i 31))
    else quotient
  (wX_bits rd (sign_extend (m := 32) (to_bits_truncate (l := 32) quotient)))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: k_ex162666_ : Bool -/
def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i (xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (xlen -i 1)))
    else quotient
  (wX_bits rd (to_bits_truncate (l := 32) quotient))
  (pure RETIRE_SUCCESS)

def execute_C_XOR (rsd : cregidx) (rs2 : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (execute_RTYPE rs2 rsd rsd XOR)

def execute_C_SWSP (uimm : (BitVec 6)) (rs2 : regidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b00#2))
  (execute_STORE imm rs2 sp 4)

def execute_C_SW (uimm : (BitVec 5)) (rsc1 : cregidx) (rsc2 : cregidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b00#2))
  let rs1 := (creg2reg_idx rsc1)
  let rs2 := (creg2reg_idx rsc2)
  (execute_STORE imm rs2 rs1 4)

def execute_C_SUBW (rsd : cregidx) (rs2 : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (execute_RTYPEW rs2 rsd rsd SUBW)

def execute_C_SUB (rsd : cregidx) (rs2 : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (execute_RTYPE rs2 rsd rsd SUB)

def execute_C_SRLI (shamt : (BitVec 6)) (rsd : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  (execute_SHIFTIOP shamt rsd rsd SRLI)

def execute_C_SRAI (shamt : (BitVec 6)) (rsd : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  (execute_SHIFTIOP shamt rsd rsd SRAI)

def execute_C_SLLI (shamt : (BitVec 6)) (rsd : regidx) : SailM ExecutionResult := do
  (execute_SHIFTIOP shamt rsd rsd SLLI)

def execute_C_SDSP (uimm : (BitVec 6)) (rs2 : regidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b000#3))
  (execute_STORE imm rs2 sp 8)

def execute_C_SD (uimm : (BitVec 5)) (rsc1 : cregidx) (rsc2 : cregidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b000#3))
  let rs1 := (creg2reg_idx rsc1)
  let rs2 := (creg2reg_idx rsc2)
  (execute_STORE imm rs2 rs1 8)

def execute_C_OR (rsd : cregidx) (rs2 : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (execute_RTYPE rs2 rsd rsd OR)

def execute_C_NOP (g__117 : (BitVec 6)) : ExecutionResult :=
  RETIRE_SUCCESS

def execute_C_MV (rd : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  (execute_RTYPE rs2 zreg rd ADD)

def execute_C_LWSP (uimm : (BitVec 6)) (rd : regidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b00#2))
  (execute_LOAD imm sp rd false 4)

def execute_C_LW (uimm : (BitVec 5)) (rsc : cregidx) (rdc : cregidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b00#2))
  let rd := (creg2reg_idx rdc)
  let rs := (creg2reg_idx rsc)
  (execute_LOAD imm rs rd false 4)

def execute_C_LUI (imm : (BitVec 6)) (rd : regidx) : SailM ExecutionResult := do
  let res : (BitVec 20) := (sign_extend (m := 20) imm)
  (execute_UTYPE res rd LUI)

def execute_C_LI (imm : (BitVec 6)) (rd : regidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (sign_extend (m := 12) imm)
  (execute_ITYPE imm zreg rd ADDI)

def execute_C_LDSP (uimm : (BitVec 6)) (rd : regidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b000#3))
  (execute_LOAD imm sp rd false 8)

def execute_C_LD (uimm : (BitVec 5)) (rsc : cregidx) (rdc : cregidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm ++ 0b000#3))
  let rd := (creg2reg_idx rdc)
  let rs := (creg2reg_idx rsc)
  (execute_LOAD imm rs rd false 8)

def execute_C_JR (rs1 : regidx) : SailM ExecutionResult := do
  (execute_JALR (zeros (n := 12)) rs1 zreg)

def execute_C_JALR (rs1 : regidx) : SailM ExecutionResult := do
  (execute_JALR (zeros (n := 12)) rs1 ra)

def execute_C_JAL (imm : (BitVec 11)) : SailM ExecutionResult := do
  (execute_JAL (sign_extend (m := 21) (imm ++ 0#1)) ra)

def execute_C_J (imm : (BitVec 11)) : SailM ExecutionResult := do
  (execute_JAL (sign_extend (m := 21) (imm ++ 0#1)) zreg)

def execute_C_ILLEGAL (s : (BitVec 16)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_C_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (execute_EBREAK ())

def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (jump_to ((← readReg PC) + (sign_extend (m := 32) imm)))
  else (pure RETIRE_SUCCESS)

def execute_C_BNEZ (imm : (BitVec 8)) (rs : cregidx) : SailM ExecutionResult := do
  (execute_BTYPE (sign_extend (m := 13) (imm ++ 0#1)) zreg (creg2reg_idx rs) BNE)

def execute_C_BEQZ (imm : (BitVec 8)) (rs : cregidx) : SailM ExecutionResult := do
  (execute_BTYPE (sign_extend (m := 13) (imm ++ 0#1)) zreg (creg2reg_idx rs) BEQ)

def execute_C_ANDI (imm : (BitVec 6)) (rsd : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  (execute_ITYPE (sign_extend (m := 12) imm) rsd rsd ANDI)

def execute_C_AND (rsd : cregidx) (rs2 : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (execute_RTYPE rs2 rsd rsd AND)

def execute_C_ADDW (rsd : cregidx) (rs2 : cregidx) : SailM ExecutionResult := do
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (execute_RTYPEW rs2 rsd rsd ADDW)

def execute_ADDIW (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let result ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 32) imm)))
  (wX_bits rd (sign_extend (m := 32) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS)

def execute_C_ADDIW (imm : (BitVec 6)) (rsd : regidx) : SailM ExecutionResult := do
  (execute_ADDIW (sign_extend (m := 12) imm) rsd rsd)

def execute_C_ADDI4SPN (rdc : cregidx) (nzimm : (BitVec 8)) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (0b00#2 ++ (nzimm ++ 0b00#2))
  let rd := (creg2reg_idx rdc)
  (execute_ITYPE imm sp rd ADDI)

def execute_C_ADDI16SP (imm : (BitVec 6)) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (sign_extend (m := 12) (imm ++ 0x0#4))
  (execute_ITYPE imm sp sp ADDI)

def execute_C_ADDI (imm : (BitVec 6)) (rsd : regidx) : SailM ExecutionResult := do
  let imm : (BitVec 12) := (sign_extend (m := 12) imm)
  (execute_ITYPE imm rsd rsd ADDI)

def execute_C_ADD (rsd : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  (execute_RTYPE rs2 rsd rsd ADD)

def execute_CSRReg (csr : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  (doCSR csr (← (rX_bits rs1)) rd op ((op == CSRRW) || (bne rs1 zreg)))

def execute_CSRImm (csr : (BitVec 12)) (imm : (BitVec 5)) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  (doCSR csr (zero_extend (m := 32) imm) rd op ((op == CSRRW) || (imm != (zeros (n := 5)))))

def execute (merge_var : instruction) : SailM ExecutionResult := do
  match merge_var with
  | .LPAD lpl => (execute_LPAD lpl)
  | .UTYPE (imm, rd, op) => (execute_UTYPE imm rd op)
  | .JAL (imm, rd) => (execute_JAL imm rd)
  | .BTYPE (imm, rs2, rs1, op) => (execute_BTYPE imm rs2 rs1 op)
  | .ITYPE (imm, rs1, rd, op) => (execute_ITYPE imm rs1 rd op)
  | .SHIFTIOP (shamt, rs1, rd, op) => (execute_SHIFTIOP shamt rs1 rd op)
  | .RTYPE (rs2, rs1, rd, op) => (execute_RTYPE rs2 rs1 rd op)
  | .LOAD (imm, rs1, rd, is_unsigned, width) => (execute_LOAD imm rs1 rd is_unsigned width)
  | .STORE (imm, rs2, rs1, width) => (execute_STORE imm rs2 rs1 width)
  | .ADDIW (imm, rs1, rd) => (execute_ADDIW imm rs1 rd)
  | .RTYPEW (rs2, rs1, rd, op) => (execute_RTYPEW rs2 rs1 rd op)
  | .SHIFTIWOP (shamt, rs1, rd, op) => (execute_SHIFTIWOP shamt rs1 rd op)
  | .FENCE (pred, succ) => (execute_FENCE pred succ)
  | .FENCE_TSO arg0 => (execute_FENCE_TSO arg0)
  | .ECALL arg0 => (execute_ECALL arg0)
  | .MRET arg0 => (execute_MRET arg0)
  | .SRET arg0 => (execute_SRET arg0)
  | .EBREAK arg0 => (execute_EBREAK arg0)
  | .WFI arg0 => (execute_WFI arg0)
  | .SFENCE_VMA (rs1, rs2) => (execute_SFENCE_VMA rs1 rs2)
  | .FENCE_RESERVED (fm, pred, succ, rs, rd) => (pure (execute_FENCE_RESERVED fm pred succ rs rd))
  | .FENCEI_RESERVED (imm, rs, rd) => (pure (execute_FENCEI_RESERVED imm rs rd))
  | .JALR (imm, rs1, rd) => (execute_JALR imm rs1 rd)
  | .MUL (rs2, rs1, rd, mul_op) => (execute_MUL rs2 rs1 rd mul_op)
  | .DIV (rs2, rs1, rd, is_unsigned) => (execute_DIV rs2 rs1 rd is_unsigned)
  | .REM (rs2, rs1, rd, is_unsigned) => (execute_REM rs2 rs1 rd is_unsigned)
  | .MULW (rs2, rs1, rd) => (execute_MULW rs2 rs1 rd)
  | .DIVW (rs2, rs1, rd, is_unsigned) => (execute_DIVW rs2 rs1 rd is_unsigned)
  | .REMW (rs2, rs1, rd, is_unsigned) => (execute_REMW rs2 rs1 rd is_unsigned)
  | .C_NOP g__117 => (pure (execute_C_NOP g__117))
  | .C_ADDI4SPN (rdc, nzimm) => (execute_C_ADDI4SPN rdc nzimm)
  | .C_LW (uimm, rsc, rdc) => (execute_C_LW uimm rsc rdc)
  | .C_LD (uimm, rsc, rdc) => (execute_C_LD uimm rsc rdc)
  | .C_SW (uimm, rsc1, rsc2) => (execute_C_SW uimm rsc1 rsc2)
  | .C_SD (uimm, rsc1, rsc2) => (execute_C_SD uimm rsc1 rsc2)
  | .C_ADDI (imm, rsd) => (execute_C_ADDI imm rsd)
  | .C_JAL imm => (execute_C_JAL imm)
  | .C_ADDIW (imm, rsd) => (execute_C_ADDIW imm rsd)
  | .C_LI (imm, rd) => (execute_C_LI imm rd)
  | .C_ADDI16SP imm => (execute_C_ADDI16SP imm)
  | .C_LUI (imm, rd) => (execute_C_LUI imm rd)
  | .C_SRLI (shamt, rsd) => (execute_C_SRLI shamt rsd)
  | .C_SRAI (shamt, rsd) => (execute_C_SRAI shamt rsd)
  | .C_ANDI (imm, rsd) => (execute_C_ANDI imm rsd)
  | .C_SUB (rsd, rs2) => (execute_C_SUB rsd rs2)
  | .C_XOR (rsd, rs2) => (execute_C_XOR rsd rs2)
  | .C_OR (rsd, rs2) => (execute_C_OR rsd rs2)
  | .C_AND (rsd, rs2) => (execute_C_AND rsd rs2)
  | .C_SUBW (rsd, rs2) => (execute_C_SUBW rsd rs2)
  | .C_ADDW (rsd, rs2) => (execute_C_ADDW rsd rs2)
  | .C_J imm => (execute_C_J imm)
  | .C_BEQZ (imm, rs) => (execute_C_BEQZ imm rs)
  | .C_BNEZ (imm, rs) => (execute_C_BNEZ imm rs)
  | .C_SLLI (shamt, rsd) => (execute_C_SLLI shamt rsd)
  | .C_LWSP (uimm, rd) => (execute_C_LWSP uimm rd)
  | .C_LDSP (uimm, rd) => (execute_C_LDSP uimm rd)
  | .C_SWSP (uimm, rs2) => (execute_C_SWSP uimm rs2)
  | .C_SDSP (uimm, rs2) => (execute_C_SDSP uimm rs2)
  | .C_JR rs1 => (execute_C_JR rs1)
  | .C_JALR rs1 => (execute_C_JALR rs1)
  | .C_MV (rd, rs2) => (execute_C_MV rd rs2)
  | .C_EBREAK arg0 => (execute_C_EBREAK arg0)
  | .C_ADD (rsd, rs2) => (execute_C_ADD rsd rs2)
  | .CSRReg (csr, rs1, rd, op) => (execute_CSRReg csr rs1 rd op)
  | .CSRImm (csr, imm, rd, op) => (execute_CSRImm csr imm rd op)
  | .FENCEI arg0 => (pure (execute_FENCEI arg0))
  | .ILLEGAL s => (pure (execute_ILLEGAL s))
  | .C_ILLEGAL s => (pure (execute_C_ILLEGAL s))

def assembly_backwards (arg_ : String) : SailM instruction := do
  match arg_ with
  | _ => throw Error.Exit

def assembly_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .LPAD lpl => true
  | .UTYPE (imm, rd, op) => true
  | .JAL (imm, rd) => true
  | .JALR (imm, rs1, rd) => true
  | .BTYPE (imm, rs2, rs1, op) => true
  | .ITYPE (imm, rs1, rd, op) => true
  | .SHIFTIOP (shamt, rs1, rd, op) => true
  | .RTYPE (rs2, rs1, rd, op) => true
  | .LOAD (imm, rs1, rd, is_unsigned, width) => true
  | .STORE (imm, rs2, rs1, width) => true
  | .ADDIW (imm, rs1, rd) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .RTYPEW (rs2, rs1, rd, op) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .FENCE (pred, succ) => true
  | .FENCE_TSO () => true
  | .ECALL () => true
  | .MRET () => true
  | .SRET () => true
  | .EBREAK () => true
  | .WFI () => true
  | .SFENCE_VMA (rs1, rs2) => true
  | .FENCE_RESERVED (fm, pred, succ, rs, rd) =>
    (if ((((fm != 0b0000#4) && (fm != 0b1000#4)) || ((bne rs zreg) || (bne rd zreg))) : Bool)
    then true
    else false)
  | .FENCEI_RESERVED (imm, rs, rd) =>
    (if (((imm != 0b000000000000#12) || ((bne rs zreg) || (bne rd zreg))) : Bool)
    then true
    else false)
  | .MUL (rs2, rs1, rd, mul_op) => true
  | .DIV (rs2, rs1, rd, is_unsigned) => true
  | .REM (rs2, rs1, rd, is_unsigned) => true
  | .MULW (rs2, rs1, rd) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .DIVW (rs2, rs1, rd, is_unsigned) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .REMW (rs2, rs1, rd, is_unsigned) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_NOP 0b000000 => true
  | .C_NOP imm =>
    (if ((imm != (zeros (n := 6))) : Bool)
    then true
    else false)
  | .C_ADDI4SPN (rdc, nzimm) =>
    (if ((nzimm != 0b00000000#8) : Bool)
    then true
    else false)
  | .C_LW (uimm, rsc, rdc) => true
  | .C_LD (uimm, rsc, rdc) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_SW (uimm, rsc1, rsc2) => true
  | .C_SD (uimm, rsc1, rsc2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_ADDI (imm, rsd) =>
    (if ((bne rsd zreg) : Bool)
    then true
    else false)
  | .C_JAL imm => true
  | .C_ADDIW (imm, rsd) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_LI (imm, rd) => true
  | .C_ADDI16SP imm =>
    (if ((imm != 0b000000#6) : Bool)
    then true
    else false)
  | .C_LUI (imm, rd) =>
    (if (((bne rd sp) && (imm != 0b000000#6)) : Bool)
    then true
    else false)
  | .C_SRLI (shamt, rsd) => true
  | .C_SRAI (shamt, rsd) => true
  | .C_ANDI (imm, rsd) => true
  | .C_SUB (rsd, rs2) => true
  | .C_XOR (rsd, rs2) => true
  | .C_OR (rsd, rs2) => true
  | .C_AND (rsd, rs2) => true
  | .C_SUBW (rsd, rs2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_ADDW (rsd, rs2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_J imm => true
  | .C_BEQZ (imm, rs) => true
  | .C_BNEZ (imm, rs) => true
  | .C_SLLI (shamt, rsd) => true
  | .C_LWSP (uimm, rd) =>
    (if ((bne rd zreg) : Bool)
    then true
    else false)
  | .C_LDSP (uimm, rd) =>
    (if (((bne rd zreg) && (xlen == 64)) : Bool)
    then true
    else false)
  | .C_SWSP (uimm, rs2) => true
  | .C_SDSP (uimm, rs2) =>
    (if ((xlen == 64) : Bool)
    then true
    else false)
  | .C_JR rs1 =>
    (if ((bne rs1 zreg) : Bool)
    then true
    else false)
  | .C_JALR rs1 =>
    (if ((bne rs1 zreg) : Bool)
    then true
    else false)
  | .C_MV (rd, rs2) =>
    (if ((bne rs2 zreg) : Bool)
    then true
    else false)
  | .C_EBREAK () => true
  | .C_ADD (rsd, rs2) =>
    (if ((bne rs2 zreg) : Bool)
    then true
    else false)
  | .CSRImm (csr, imm, rd, op) => true
  | .CSRReg (csr, rs1, rd, op) => true
  | .FENCEI () => true
  | .ILLEGAL s => true
  | .C_ILLEGAL s => true

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

