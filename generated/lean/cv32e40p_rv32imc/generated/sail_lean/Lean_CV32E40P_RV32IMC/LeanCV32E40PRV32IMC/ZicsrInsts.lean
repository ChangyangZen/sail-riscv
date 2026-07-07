import LeanCV32E40PRV32IMC.Prelude
import LeanCV32E40PRV32IMC.Errors
import LeanCV32E40PRV32IMC.Xlen
import LeanCV32E40PRV32IMC.Types
import LeanCV32E40PRV32IMC.Callbacks
import LeanCV32E40PRV32IMC.Regs
import LeanCV32E40PRV32IMC.SysRegs
import LeanCV32E40PRV32IMC.ExtRegs
import LeanCV32E40PRV32IMC.SysExceptions
import LeanCV32E40PRV32IMC.PmpRegs
import LeanCV32E40PRV32IMC.FdextRegs
import LeanCV32E40PRV32IMC.VextRegs
import LeanCV32E40PRV32IMC.Smcntrpmf
import LeanCV32E40PRV32IMC.SysControl
import LeanCV32E40PRV32IMC.InstRetire
import LeanCV32E40PRV32IMC.Vmem

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

def encdec_csrop_forwards (arg_ : csrop) : (BitVec 2) :=
  match arg_ with
  | CSRRW => 0b01#2
  | CSRRS => 0b10#2
  | CSRRC => 0b11#2

def encdec_csrop_backwards (arg_ : (BitVec 2)) : SailM csrop := do
  match arg_ with
  | 0b01 => (pure CSRRW)
  | 0b10 => (pure CSRRS)
  | 0b11 => (pure CSRRC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_csrop_forwards_matches (arg_ : csrop) : Bool :=
  match arg_ with
  | CSRRW => true
  | CSRRS => true
  | CSRRC => true

def encdec_csrop_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def read_CSR (merge_var : (BitVec 12)) : SailM (BitVec 32) := do
  match merge_var with
  | 0x301 => readReg misa
  | 0x300 => (pure (Sail.BitVec.extractLsb (← readReg mstatus) (xlen -i 1) 0))
  | 0x310 => (pure (Sail.BitVec.extractLsb (← readReg mstatus) 63 32))
  | 0x747 => (pure (Sail.BitVec.extractLsb (← readReg mseccfg) (xlen -i 1) 0))
  | 0x757 => (pure (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32))
  | 0x30A => (pure (Sail.BitVec.extractLsb (← readReg menvcfg) (xlen -i 1) 0))
  | 0x31A => (pure (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32))
  | 0x10A => (pure (Sail.BitVec.extractLsb (← readReg senvcfg) (xlen -i 1) 0))
  | 0x304 => readReg mie
  | 0x344 => readReg mip
  | 0x302 => (pure (Sail.BitVec.extractLsb (← readReg medeleg) (xlen -i 1) 0))
  | 0x312 => (pure (Sail.BitVec.extractLsb (← readReg medeleg) 63 32))
  | 0x303 => readReg mideleg
  | 0x342 => readReg mcause
  | 0x343 => readReg mtval
  | 0x340 => readReg mscratch
  | 0x106 => (pure (zero_extend (m := 32) (← readReg scounteren)))
  | 0x306 => (pure (zero_extend (m := 32) (← readReg mcounteren)))
  | 0x320 => (pure (zero_extend (m := 32) (← readReg mcountinhibit)))
  | 0xF11 => (pure (zero_extend (m := 32) (← readReg mvendorid)))
  | 0xF12 => readReg marchid
  | 0xF13 => readReg mimpid
  | 0xF14 => readReg mhartid
  | 0xF15 => readReg mconfigptr
  | 0x100 => (pure (Sail.BitVec.extractLsb (lower_mstatus (← readReg mstatus)) (xlen -i 1) 0))
  | 0x144 => (pure (lower_mip (← readReg mip) (← readReg mideleg)))
  | 0x104 => (pure (lower_mie (← readReg mie) (← readReg mideleg)))
  | 0x140 => readReg sscratch
  | 0x142 => readReg scause
  | 0x143 => readReg stval
  | 0x7A0 => (pure (Complement.complement (← readReg tselect)))
  | 0x105 => (get_stvec ())
  | 0x141 => (get_xepc Supervisor)
  | 0x305 => (get_mtvec ())
  | 0x341 => (get_xepc Machine)
  | v__778 =>
    (do
      if ((((Sail.BitVec.extractLsb v__778 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
             (Sail.BitVec.extractLsb v__778 3 0)
           (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
      then
        (do
          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__778 3 0)
          (pmpReadCfgReg (BitVec.toNatInt idx)))
      else
        (do
          if (((Sail.BitVec.extractLsb v__778 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__778 3 0)
              (pmpReadAddrReg (BitVec.toNatInt (0b00#2 ++ idx))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__778 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__778 3 0)
                  (pmpReadAddrReg (BitVec.toNatInt (0b01#2 ++ idx))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__778 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__778 3 0)
                      (pmpReadAddrReg (BitVec.toNatInt (0b10#2 ++ idx))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__778 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__778 3 0)
                          (pmpReadAddrReg (BitVec.toNatInt (0b11#2 ++ idx))))
                      else
                        (do
                          match v__778 with
                          | 0x001 =>
                            (pure (zero_extend (m := 32) (_get_Fcsr_FFLAGS (← readReg fcsr))))
                          | 0x002 =>
                            (pure (zero_extend (m := 32) (_get_Fcsr_FRM (← readReg fcsr))))
                          | 0x003 => (pure (zero_extend (m := 32) (← readReg fcsr)))
                          | 0x008 => readReg vstart
                          | 0x009 =>
                            (pure (zero_extend (m := 32) (_get_Vcsr_vxsat (← readReg vcsr))))
                          | 0x00A =>
                            (pure (zero_extend (m := 32) (_get_Vcsr_vxrm (← readReg vcsr))))
                          | 0x00F => (pure (zero_extend (m := 32) (← readReg vcsr)))
                          | 0xC20 => readReg vl
                          | 0xC21 => readReg vtype
                          | 0xC22 => (pure VLENB)
                          | 0x321 =>
                            (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1) 0))
                          | 0x721 => (pure (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32))
                          | 0x322 =>
                            (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1) 0))
                          | 0x722 => (pure (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32))
                          | 0x180 => readReg satp
                          | 0xC00 =>
                            (pure (Sail.BitVec.extractLsb (← readReg mcycle) (xlen -i 1) 0))
                          | 0xC01 =>
                            (pure (Sail.BitVec.extractLsb (← readReg mtime) (xlen -i 1) 0))
                          | 0xC02 =>
                            (pure (Sail.BitVec.extractLsb (← readReg minstret) (xlen -i 1) 0))
                          | 0xC80 => (pure (Sail.BitVec.extractLsb (← readReg mcycle) 63 32))
                          | 0xC81 => (pure (Sail.BitVec.extractLsb (← readReg mtime) 63 32))
                          | 0xC82 => (pure (Sail.BitVec.extractLsb (← readReg minstret) 63 32))
                          | 0xB00 =>
                            (pure (Sail.BitVec.extractLsb (← readReg mcycle) (xlen -i 1) 0))
                          | 0xB02 =>
                            (pure (Sail.BitVec.extractLsb (← readReg minstret) (xlen -i 1) 0))
                          | 0xB80 => (pure (Sail.BitVec.extractLsb (← readReg mcycle) 63 32))
                          | 0xB82 => (pure (Sail.BitVec.extractLsb (← readReg minstret) 63 32))
                          | v__778 =>
                            (internal_error "model/postlude/csr_end.sail" 17
                              (HAppend.hAppend "Read from CSR that does not exist: "
                                (BitVec.toFormatted v__778)))))))))

def write_CSR (arg0 : (BitVec 12)) (arg1 : (BitVec 32)) : SailM (Result (BitVec 32) Unit) := do
  let merge_var := (arg0, arg1)
  match merge_var with
  | (0x301, value) =>
    (do
      writeReg misa (← (legalize_misa (← readReg misa) value))
      (pure (Ok (← readReg misa))))
  | (0x300, value) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus) value))
          (pure (Ok (← readReg mstatus))))
      else
        (do
          writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
              ((Sail.BitVec.extractLsb (← readReg mstatus) 63 32) ++ (Sail.BitVec.extractLsb value
                  31 0))))
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mstatus) 31 0))))))
  | (0x310, value) =>
    (do
      writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
          ((Sail.BitVec.extractLsb value 31 0) ++ (Sail.BitVec.extractLsb (← readReg mstatus) 31 0))))
      (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mstatus) 63 32)))))
  | (0x747, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
              ((Sail.BitVec.extractLsb (← readReg mseccfg) 63 32) ++ (Sail.BitVec.extractLsb value
                  31 0))))
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0)))))
      else
        (do
          writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg) value))
          (pure (Ok (← readReg mseccfg)))))
  | (0x757, value) =>
    (do
      writeReg mseccfg (← (legalize_mseccfg (← readReg mseccfg)
          ((Sail.BitVec.extractLsb value 31 0) ++ (Sail.BitVec.extractLsb (← readReg mseccfg) 31 0))))
      (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg mseccfg) 63 32)))))
  | (0x30A, value) =>
    (do
      if ((xlen == 32) : Bool)
      then
        (do
          writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
              ((Sail.BitVec.extractLsb (← readReg menvcfg) 63 32) ++ (Sail.BitVec.extractLsb value
                  31 0))))
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg menvcfg) 31 0)))))
      else
        (do
          writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg) value))
          (pure (Ok (← readReg menvcfg)))))
  | (0x31A, value) =>
    (do
      writeReg menvcfg (← (legalize_menvcfg (← readReg menvcfg)
          ((Sail.BitVec.extractLsb value 31 0) ++ (Sail.BitVec.extractLsb (← readReg menvcfg) 31 0))))
      (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg menvcfg) 63 32)))))
  | (0x10A, value) =>
    (do
      writeReg senvcfg (← (legalize_senvcfg (← readReg senvcfg) (zero_extend (m := 32) value)))
      (pure (Ok (Sail.BitVec.extractLsb (← readReg senvcfg) (xlen -i 1) 0))))
  | (0x304, value) =>
    (do
      writeReg mie (← (legalize_mie (← readReg mie) value))
      (pure (Ok (← readReg mie))))
  | (0x344, value) =>
    (do
      writeReg mip (← (legalize_mip (← readReg mip) value))
      (pure (Ok (← readReg mip))))
  | (0x302, value) =>
    (do
      if ((xlen == 64) : Bool)
      then
        (do
          writeReg medeleg (legalize_medeleg (← readReg medeleg) value)
          (pure (Ok (← readReg medeleg))))
      else
        (do
          writeReg medeleg (legalize_medeleg (← readReg medeleg)
            ((Sail.BitVec.extractLsb (← readReg medeleg) 63 32) ++ (Sail.BitVec.extractLsb value
                31 0)))
          (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg medeleg) 31 0))))))
  | (0x312, value) =>
    (do
      writeReg medeleg (legalize_medeleg (← readReg medeleg)
        ((Sail.BitVec.extractLsb value 31 0) ++ (Sail.BitVec.extractLsb (← readReg medeleg) 31 0)))
      (pure (Ok (zero_extend (m := 32) (Sail.BitVec.extractLsb (← readReg medeleg) 63 32)))))
  | (0x303, value) =>
    (do
      writeReg mideleg (legalize_mideleg (← readReg mideleg) value)
      (pure (Ok (← readReg mideleg))))
  | (0x342, value) =>
    (do
      writeReg mcause value
      (pure (Ok (← readReg mcause))))
  | (0x343, value) =>
    (do
      writeReg mtval value
      (pure (Ok (← readReg mtval))))
  | (0x340, value) =>
    (do
      writeReg mscratch value
      (pure (Ok (← readReg mscratch))))
  | (0x106, value) =>
    (do
      writeReg scounteren (legalize_scounteren (← readReg scounteren) value)
      (pure (Ok (zero_extend (m := 32) (← readReg scounteren)))))
  | (0x306, value) =>
    (do
      writeReg mcounteren (legalize_mcounteren (← readReg mcounteren) value)
      (pure (Ok (zero_extend (m := 32) (← readReg mcounteren)))))
  | (0x320, value) =>
    (do
      writeReg mcountinhibit (legalize_mcountinhibit (← readReg mcountinhibit) value)
      (pure (Ok (zero_extend (m := 32) (← readReg mcountinhibit)))))
  | (0x100, value) =>
    (do
      writeReg mstatus (← (legalize_sstatus (← readReg mstatus) value))
      (pure (Ok (Sail.BitVec.extractLsb (lower_mstatus (← readReg mstatus)) (xlen -i 1) 0))))
  | (0x144, value) =>
    (do
      writeReg mip (legalize_sip (← readReg mip) (← readReg mideleg) value)
      (pure (Ok (lower_mip (← readReg mip) (← readReg mideleg)))))
  | (0x104, value) =>
    (do
      writeReg mie (legalize_sie (← readReg mie) (← readReg mideleg) value)
      (pure (Ok (lower_mie (← readReg mie) (← readReg mideleg)))))
  | (0x140, value) =>
    (do
      writeReg sscratch value
      (pure (Ok (← readReg sscratch))))
  | (0x142, value) =>
    (do
      writeReg scause value
      (pure (Ok (← readReg scause))))
  | (0x143, value) =>
    (do
      writeReg stval value
      (pure (Ok (← readReg stval))))
  | (0x7A0, value) =>
    (do
      writeReg tselect value
      (pure (Ok (← readReg tselect))))
  | (0x105, value) => (pure (Ok (← (set_stvec value))))
  | (0x141, value) => (pure (Ok (← (set_xepc Supervisor value))))
  | (0x305, value) => (pure (Ok (← (set_mtvec value))))
  | (0x341, value) => (pure (Ok (← (set_xepc Machine value))))
  | (v__788, value) =>
    (do
      if ((((Sail.BitVec.extractLsb v__788 11 4) == (0x3A#8 : (BitVec 8))) && (let idx : (BitVec 4) :=
             (Sail.BitVec.extractLsb v__788 3 0)
           (((BitVec.access idx 0) == 0#1) || (xlen == 32)))) : Bool)
      then
        (do
          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__788 3 0)
          let idx := (BitVec.toNatInt idx)
          (pmpWriteCfgReg idx value)
          (pure (Ok (← (pmpReadCfgReg idx)))))
      else
        (do
          if (((Sail.BitVec.extractLsb v__788 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (do
              let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__788 3 0)
              let idx := (BitVec.toNatInt (0b00#2 ++ idx))
              (pmpWriteAddrReg idx value)
              (pure (Ok (← (pmpReadAddrReg idx)))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__788 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (do
                  let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__788 3 0)
                  let idx := (BitVec.toNatInt (0b01#2 ++ idx))
                  (pmpWriteAddrReg idx value)
                  (pure (Ok (← (pmpReadAddrReg idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__788 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (do
                      let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__788 3 0)
                      let idx := (BitVec.toNatInt (0b10#2 ++ idx))
                      (pmpWriteAddrReg idx value)
                      (pure (Ok (← (pmpReadAddrReg idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__788 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (do
                          let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__788 3 0)
                          let idx := (BitVec.toNatInt (0b11#2 ++ idx))
                          (pmpWriteAddrReg idx value)
                          (pure (Ok (← (pmpReadAddrReg idx)))))
                      else
                        (do
                          match (v__788, value) with
                          | (0x001, value) =>
                            (do
                              (write_fcsr (_get_Fcsr_FRM (← readReg fcsr))
                                (Sail.BitVec.extractLsb value 4 0))
                              (pure (Ok
                                  (zero_extend (m := 32) (_get_Fcsr_FFLAGS (← readReg fcsr))))))
                          | (0x002, value) =>
                            (do
                              (write_fcsr (Sail.BitVec.extractLsb value 2 0)
                                (_get_Fcsr_FFLAGS (← readReg fcsr)))
                              (pure (Ok (zero_extend (m := 32) (_get_Fcsr_FRM (← readReg fcsr))))))
                          | (0x003, value) =>
                            (do
                              (write_fcsr (Sail.BitVec.extractLsb value 7 5)
                                (Sail.BitVec.extractLsb value 4 0))
                              (pure (Ok (zero_extend (m := 32) (← readReg fcsr)))))
                          | (0x008, value) =>
                            (do
                              (set_vstart (Sail.BitVec.extractLsb value 15 0))
                              (pure (Ok (← readReg vstart))))
                          | (0x009, value) =>
                            (do
                              (ext_write_vcsr (_get_Vcsr_vxrm (← readReg vcsr))
                                (Sail.BitVec.extractLsb value 0 0))
                              (pure (Ok (zero_extend (m := 32) (_get_Vcsr_vxsat (← readReg vcsr))))))
                          | (0x00A, value) =>
                            (do
                              (ext_write_vcsr (Sail.BitVec.extractLsb value 1 0)
                                (_get_Vcsr_vxsat (← readReg vcsr)))
                              (pure (Ok (zero_extend (m := 32) (_get_Vcsr_vxrm (← readReg vcsr))))))
                          | (0x00F, value) =>
                            (do
                              (ext_write_vcsr (Sail.BitVec.extractLsb value 2 1)
                                (Sail.BitVec.extractLsb value 0 0))
                              (pure (Ok (zero_extend (m := 32) (← readReg vcsr)))))
                          | (0x321, value) =>
                            (do
                              if ((xlen == 64) : Bool)
                              then
                                (do
                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                      (← readReg mcyclecfg) value))
                                  (pure (Ok (← readReg mcyclecfg))))
                              else
                                (do
                                  writeReg mcyclecfg (← (legalize_smcntrpmf
                                      (← readReg mcyclecfg)
                                      ((Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32) ++ (Sail.BitVec.extractLsb
                                          value 31 0))))
                                  (pure (Ok
                                      (zero_extend (m := 32)
                                        (Sail.BitVec.extractLsb (← readReg mcyclecfg) (xlen -i 1)
                                          0))))))
                          | (0x721, value) =>
                            (do
                              writeReg mcyclecfg (← (legalize_smcntrpmf (← readReg mcyclecfg)
                                  ((Sail.BitVec.extractLsb value 31 0) ++ (Sail.BitVec.extractLsb
                                      (← readReg mcyclecfg) 31 0))))
                              (pure (Ok
                                  (zero_extend (m := 32)
                                    (Sail.BitVec.extractLsb (← readReg mcyclecfg) 63 32)))))
                          | (0x322, value) =>
                            (do
                              if ((xlen == 64) : Bool)
                              then
                                (do
                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                      (← readReg minstretcfg) value))
                                  (pure (Ok
                                      (Sail.BitVec.extractLsb (← readReg minstretcfg) (xlen -i 1)
                                        0))))
                              else
                                (do
                                  writeReg minstretcfg (← (legalize_smcntrpmf
                                      (← readReg minstretcfg)
                                      ((Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32) ++ (Sail.BitVec.extractLsb
                                          value 31 0))))
                                  (pure (Ok
                                      (zero_extend (m := 32)
                                        (Sail.BitVec.extractLsb (← readReg minstretcfg)
                                          (xlen -i 1) 0))))))
                          | (0x722, value) =>
                            (do
                              writeReg minstretcfg (← (legalize_smcntrpmf
                                  (← readReg minstretcfg)
                                  ((Sail.BitVec.extractLsb value 31 0) ++ (Sail.BitVec.extractLsb
                                      (← readReg minstretcfg) 31 0))))
                              (pure (Ok
                                  (zero_extend (m := 32)
                                    (Sail.BitVec.extractLsb (← readReg minstretcfg) 63 32)))))
                          | (0x180, value) =>
                            (do
                              writeReg satp (← (legalize_satp
                                  (← (architecture (← readReg cur_privilege)))
                                  (← readReg satp) value))
                              (pure (Ok (← readReg satp))))
                          | (0xB00, value) =>
                            (do
                              writeReg mcycle (Sail.BitVec.updateSubrange (← readReg mcycle)
                                (xlen -i 1) 0 value)
                              (pure (Ok value)))
                          | (0xB02, value) =>
                            (do
                              writeReg minstret (Sail.BitVec.updateSubrange (← readReg minstret)
                                (xlen -i 1) 0 value)
                              writeReg minstret_increment false
                              (pure (Ok value)))
                          | (0xB80, value) =>
                            (do
                              writeReg mcycle (Sail.BitVec.updateSubrange (← readReg mcycle) 63 32
                                value)
                              (pure (Ok value)))
                          | (0xB82, value) =>
                            (do
                              writeReg minstret (Sail.BitVec.updateSubrange (← readReg minstret)
                                63 32 value)
                              writeReg minstret_increment false
                              (pure (Ok value)))
                          | (v__788, _) =>
                            (internal_error "model/postlude/csr_end.sail" 23
                              (HAppend.hAppend "Write to CSR that does not exist: "
                                (BitVec.toFormatted v__788)))))))))

/-- Type quantifiers: k_ex154929_ : Bool -/
def doCSR (csr : (BitVec 12)) (rs1_val : (BitVec 32)) (rd : regidx) (op : csrop) (is_CSR_Write : Bool) : SailM ExecutionResult := do
  if ((not (← (check_CSR csr (← readReg cur_privilege) is_CSR_Write))) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_CSR csr (← readReg cur_privilege) is_CSR_Write)) : Bool)
      then (pure (Ext_CSR_Check_Failure ()))
      else
        (do
          let is_CSR_Read := (not ((op == CSRRW) && (rd == zreg)))
          let csr_val ← (( do
            if (is_CSR_Read : Bool)
            then (read_CSR csr)
            else (pure (zeros (n := 32))) ) : SailM xlenbits )
          if (is_CSR_Write : Bool)
          then
            (do
              let new_val : xlenbits :=
                match op with
                | CSRRW => rs1_val
                | CSRRS => (csr_val ||| rs1_val)
                | CSRRC => (csr_val &&& (Complement.complement rs1_val))
              match (← (write_CSR csr new_val)) with
              | .Ok final_val =>
                (do
                  (csr_id_write_callback csr final_val)
                  (wX_bits rd csr_val)
                  (pure RETIRE_SUCCESS))
              | .Err () => (pure (Illegal_Instruction ())))
          else
            (do
              (csr_id_read_callback csr csr_val)
              (wX_bits rd csr_val)
              (pure RETIRE_SUCCESS))))

def csr_mnemonic_backwards (arg_ : String) : SailM csrop := do
  match arg_ with
  | "csrrw" => (pure CSRRW)
  | "csrrs" => (pure CSRRS)
  | "csrrc" => (pure CSRRC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_mnemonic_forwards_matches (arg_ : csrop) : Bool :=
  match arg_ with
  | CSRRW => true
  | CSRRS => true
  | CSRRC => true

def csr_mnemonic_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "csrrw" => true
  | "csrrs" => true
  | "csrrc" => true
  | _ => false

