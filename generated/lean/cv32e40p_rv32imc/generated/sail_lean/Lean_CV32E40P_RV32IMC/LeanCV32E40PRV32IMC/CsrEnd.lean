import LeanCV32E40PRV32IMC.HexBits

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

def csr_name_map_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  match arg_ with
  | 0x301 => true
  | 0x300 => true
  | 0x310 => true
  | 0x747 => true
  | 0x757 => true
  | 0x30A => true
  | 0x31A => true
  | 0x10A => true
  | 0x304 => true
  | 0x344 => true
  | 0x302 => true
  | 0x312 => true
  | 0x303 => true
  | 0x342 => true
  | 0x343 => true
  | 0x340 => true
  | 0x106 => true
  | 0x306 => true
  | 0x320 => true
  | 0xF11 => true
  | 0xF12 => true
  | 0xF13 => true
  | 0xF14 => true
  | 0xF15 => true
  | 0x100 => true
  | 0x144 => true
  | 0x104 => true
  | 0x140 => true
  | 0x142 => true
  | 0x143 => true
  | 0x7A0 => true
  | 0x7A1 => true
  | 0x7A2 => true
  | 0x7A3 => true
  | 0x105 => true
  | 0x141 => true
  | 0x305 => true
  | 0x341 => true
  | 0x3A0 => true
  | 0x3A1 => true
  | 0x3A2 => true
  | 0x3A3 => true
  | 0x3A4 => true
  | 0x3A5 => true
  | 0x3A6 => true
  | 0x3A7 => true
  | 0x3A8 => true
  | 0x3A9 => true
  | 0x3AA => true
  | 0x3AB => true
  | 0x3AC => true
  | 0x3AD => true
  | 0x3AE => true
  | 0x3AF => true
  | 0x3B0 => true
  | 0x3B1 => true
  | 0x3B2 => true
  | 0x3B3 => true
  | 0x3B4 => true
  | 0x3B5 => true
  | 0x3B6 => true
  | 0x3B7 => true
  | 0x3B8 => true
  | 0x3B9 => true
  | 0x3BA => true
  | 0x3BB => true
  | 0x3BC => true
  | 0x3BD => true
  | 0x3BE => true
  | 0x3BF => true
  | 0x3C0 => true
  | 0x3C1 => true
  | 0x3C2 => true
  | 0x3C3 => true
  | 0x3C4 => true
  | 0x3C5 => true
  | 0x3C6 => true
  | 0x3C7 => true
  | 0x3C8 => true
  | 0x3C9 => true
  | 0x3CA => true
  | 0x3CB => true
  | 0x3CC => true
  | 0x3CD => true
  | 0x3CE => true
  | 0x3CF => true
  | 0x3D0 => true
  | 0x3D1 => true
  | 0x3D2 => true
  | 0x3D3 => true
  | 0x3D4 => true
  | 0x3D5 => true
  | 0x3D6 => true
  | 0x3D7 => true
  | 0x3D8 => true
  | 0x3D9 => true
  | 0x3DA => true
  | 0x3DB => true
  | 0x3DC => true
  | 0x3DD => true
  | 0x3DE => true
  | 0x3DF => true
  | 0x3E0 => true
  | 0x3E1 => true
  | 0x3E2 => true
  | 0x3E3 => true
  | 0x3E4 => true
  | 0x3E5 => true
  | 0x3E6 => true
  | 0x3E7 => true
  | 0x3E8 => true
  | 0x3E9 => true
  | 0x3EA => true
  | 0x3EB => true
  | 0x3EC => true
  | 0x3ED => true
  | 0x3EE => true
  | 0x3EF => true
  | 0x001 => true
  | 0x002 => true
  | 0x003 => true
  | 0x008 => true
  | 0x009 => true
  | 0x00A => true
  | 0x00F => true
  | 0xC20 => true
  | 0xC21 => true
  | 0xC22 => true
  | 0x321 => true
  | 0x721 => true
  | 0x322 => true
  | 0x722 => true
  | 0x180 => true
  | 0xC00 => true
  | 0xC01 => true
  | 0xC02 => true
  | 0xC80 => true
  | 0xC81 => true
  | 0xC82 => true
  | 0xB00 => true
  | 0xB02 => true
  | 0xB80 => true
  | 0xB82 => true
  | reg => true

def csr_name_map_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | "misa" => (some true)
  | "mstatus" => (some true)
  | "mstatush" => (some true)
  | "mseccfg" => (some true)
  | "mseccfgh" => (some true)
  | "menvcfg" => (some true)
  | "menvcfgh" => (some true)
  | "senvcfg" => (some true)
  | "mie" => (some true)
  | "mip" => (some true)
  | "medeleg" => (some true)
  | "medelegh" => (some true)
  | "mideleg" => (some true)
  | "mcause" => (some true)
  | "mtval" => (some true)
  | "mscratch" => (some true)
  | "scounteren" => (some true)
  | "mcounteren" => (some true)
  | "mcountinhibit" => (some true)
  | "mvendorid" => (some true)
  | "marchid" => (some true)
  | "mimpid" => (some true)
  | "mhartid" => (some true)
  | "mconfigptr" => (some true)
  | "sstatus" => (some true)
  | "sip" => (some true)
  | "sie" => (some true)
  | "sscratch" => (some true)
  | "scause" => (some true)
  | "stval" => (some true)
  | "tselect" => (some true)
  | "tdata1" => (some true)
  | "tdata2" => (some true)
  | "tdata3" => (some true)
  | "stvec" => (some true)
  | "sepc" => (some true)
  | "mtvec" => (some true)
  | "mepc" => (some true)
  | "pmpcfg0" => (some true)
  | "pmpcfg1" => (some true)
  | "pmpcfg2" => (some true)
  | "pmpcfg3" => (some true)
  | "pmpcfg4" => (some true)
  | "pmpcfg5" => (some true)
  | "pmpcfg6" => (some true)
  | "pmpcfg7" => (some true)
  | "pmpcfg8" => (some true)
  | "pmpcfg9" => (some true)
  | "pmpcfg10" => (some true)
  | "pmpcfg11" => (some true)
  | "pmpcfg12" => (some true)
  | "pmpcfg13" => (some true)
  | "pmpcfg14" => (some true)
  | "pmpcfg15" => (some true)
  | "pmpaddr0" => (some true)
  | "pmpaddr1" => (some true)
  | "pmpaddr2" => (some true)
  | "pmpaddr3" => (some true)
  | "pmpaddr4" => (some true)
  | "pmpaddr5" => (some true)
  | "pmpaddr6" => (some true)
  | "pmpaddr7" => (some true)
  | "pmpaddr8" => (some true)
  | "pmpaddr9" => (some true)
  | "pmpaddr10" => (some true)
  | "pmpaddr11" => (some true)
  | "pmpaddr12" => (some true)
  | "pmpaddr13" => (some true)
  | "pmpaddr14" => (some true)
  | "pmpaddr15" => (some true)
  | "pmpaddr16" => (some true)
  | "pmpaddr17" => (some true)
  | "pmpaddr18" => (some true)
  | "pmpaddr19" => (some true)
  | "pmpaddr20" => (some true)
  | "pmpaddr21" => (some true)
  | "pmpaddr22" => (some true)
  | "pmpaddr23" => (some true)
  | "pmpaddr24" => (some true)
  | "pmpaddr25" => (some true)
  | "pmpaddr26" => (some true)
  | "pmpaddr27" => (some true)
  | "pmpaddr28" => (some true)
  | "pmpaddr29" => (some true)
  | "pmpaddr30" => (some true)
  | "pmpaddr31" => (some true)
  | "pmpaddr32" => (some true)
  | "pmpaddr33" => (some true)
  | "pmpaddr34" => (some true)
  | "pmpaddr35" => (some true)
  | "pmpaddr36" => (some true)
  | "pmpaddr37" => (some true)
  | "pmpaddr38" => (some true)
  | "pmpaddr39" => (some true)
  | "pmpaddr40" => (some true)
  | "pmpaddr41" => (some true)
  | "pmpaddr42" => (some true)
  | "pmpaddr43" => (some true)
  | "pmpaddr44" => (some true)
  | "pmpaddr45" => (some true)
  | "pmpaddr46" => (some true)
  | "pmpaddr47" => (some true)
  | "pmpaddr48" => (some true)
  | "pmpaddr49" => (some true)
  | "pmpaddr50" => (some true)
  | "pmpaddr51" => (some true)
  | "pmpaddr52" => (some true)
  | "pmpaddr53" => (some true)
  | "pmpaddr54" => (some true)
  | "pmpaddr55" => (some true)
  | "pmpaddr56" => (some true)
  | "pmpaddr57" => (some true)
  | "pmpaddr58" => (some true)
  | "pmpaddr59" => (some true)
  | "pmpaddr60" => (some true)
  | "pmpaddr61" => (some true)
  | "pmpaddr62" => (some true)
  | "pmpaddr63" => (some true)
  | "fflags" => (some true)
  | "frm" => (some true)
  | "fcsr" => (some true)
  | "vstart" => (some true)
  | "vxsat" => (some true)
  | "vxrm" => (some true)
  | "vcsr" => (some true)
  | "vl" => (some true)
  | "vtype" => (some true)
  | "vlenb" => (some true)
  | "mcyclecfg" => (some true)
  | "mcyclecfgh" => (some true)
  | "minstretcfg" => (some true)
  | "minstretcfgh" => (some true)
  | "satp" => (some true)
  | "cycle" => (some true)
  | "time" => (some true)
  | "instret" => (some true)
  | "cycleh" => (some true)
  | "timeh" => (some true)
  | "instreth" => (some true)
  | "mcycle" => (some true)
  | "minstret" => (some true)
  | "mcycleh" => (some true)
  | "minstreth" => (some true)
  | mapping0_ =>
    (if ((hex_bits_12_backwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some true))
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

