import LeanCV32E40PRV32IMC.Flow
import LeanCV32E40PRV32IMC.Prelude
import LeanCV32E40PRV32IMC.Errors
import LeanCV32E40PRV32IMC.Xlen
import LeanCV32E40PRV32IMC.Extensions
import LeanCV32E40PRV32IMC.Types
import LeanCV32E40PRV32IMC.Callbacks
import LeanCV32E40PRV32IMC.Regs
import LeanCV32E40PRV32IMC.PcAccess
import LeanCV32E40PRV32IMC.SysRegs
import LeanCV32E40PRV32IMC.SysExceptions
import LeanCV32E40PRV32IMC.PmpRegs
import LeanCV32E40PRV32IMC.PmpControl
import LeanCV32E40PRV32IMC.VextRegs
import LeanCV32E40PRV32IMC.ZicfilpRegs

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

def effectivePrivilege (t : (AccessType Unit)) (m : (BitVec 64)) (priv : Privilege) : SailM Privilege := do
  if (((bne t (InstructionFetch ())) && ((_get_Mstatus_MPRV m) == 1#1)) : Bool)
  then (privLevel_bits_forwards ((_get_Mstatus_MPP m), 0#1))
  else (pure priv)

def csrAccess (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 11 10)

def csrPriv (csr : (BitVec 12)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb csr 9 8)

def check_CSR_priv (csr : (BitVec 12)) (p : Privilege) : Bool :=
  (zopz0zKzJ_u (privLevel_to_bits p) (csrPriv csr))

/-- Type quantifiers: k_ex152351_ : Bool -/
def check_CSR_access (csr : (BitVec 12)) (isWrite : Bool) : Bool :=
  (not (isWrite && ((csrAccess csr) == 0b11#2)))

/-- Type quantifiers: k_ex152361_ : Bool -/
def is_CSR_accessible (arg0 : (BitVec 12)) (arg1 : Privilege) (arg2 : Bool) : SailM Bool := do
  let merge_var := (arg0, arg1, arg2)
  match merge_var with
  | (0x301, g__2, g__3) => (pure true)
  | (0x300, g__4, g__5) => (pure true)
  | (0x310, g__6, g__7) => (pure (xlen == 32))
  | (0x747, g__8, g__9) => (pure ((← (currentlyEnabled Ext_Zkr)) || (hartSupports Ext_Zicfilp)))
  | (0x757, g__10, g__11) =>
    (pure (((← (currentlyEnabled Ext_Zkr)) || (hartSupports Ext_Zicfilp)) && (xlen == 32)))
  | (0x30A, g__12, g__13) => (currentlyEnabled Ext_U)
  | (0x31A, g__14, g__15) => (pure ((← (currentlyEnabled Ext_U)) && (xlen == 32)))
  | (0x10A, g__16, g__17) => (currentlyEnabled Ext_S)
  | (0x304, g__18, g__19) => (pure true)
  | (0x344, g__20, g__21) => (pure true)
  | (0x302, g__22, g__23) => (currentlyEnabled Ext_S)
  | (0x312, g__24, g__25) => (pure ((← (currentlyEnabled Ext_S)) && (xlen == 32)))
  | (0x303, g__26, g__27) => (currentlyEnabled Ext_S)
  | (0x342, g__28, g__29) => (pure true)
  | (0x343, g__30, g__31) => (pure true)
  | (0x340, g__32, g__33) => (pure true)
  | (0x106, g__34, g__35) => (currentlyEnabled Ext_S)
  | (0x306, g__36, g__37) => (currentlyEnabled Ext_U)
  | (0x320, g__38, g__39) => (pure true)
  | (0xF11, g__40, g__41) => (pure true)
  | (0xF12, g__42, g__43) => (pure true)
  | (0xF13, g__44, g__45) => (pure true)
  | (0xF14, g__46, g__47) => (pure true)
  | (0xF15, g__48, g__49) => (pure true)
  | (0x100, g__50, g__51) => (currentlyEnabled Ext_S)
  | (0x144, g__52, g__53) => (currentlyEnabled Ext_S)
  | (0x104, g__54, g__55) => (currentlyEnabled Ext_S)
  | (0x140, g__56, g__57) => (currentlyEnabled Ext_S)
  | (0x142, g__58, g__59) => (currentlyEnabled Ext_S)
  | (0x143, g__60, g__61) => (currentlyEnabled Ext_S)
  | (0x7A0, g__62, g__63) => (pure true)
  | (0x105, g__64, g__65) => (currentlyEnabled Ext_S)
  | (0x141, g__66, g__67) => (currentlyEnabled Ext_S)
  | (0x305, g__68, g__69) => (pure true)
  | (0x341, g__70, g__71) => (pure true)
  | (v__768, g__72, g__73) =>
    (do
      if (((Sail.BitVec.extractLsb v__768 11 4) == (0x3A#8 : (BitVec 8))) : Bool)
      then
        (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__768 3 0)
        (pure ((sys_pmp_count >b (4 *i (BitVec.toNatInt idx))) && (((BitVec.access idx 0) == 0#1) || (xlen == 32)))))
      else
        (do
          if (((Sail.BitVec.extractLsb v__768 11 4) == (0x3B#8 : (BitVec 8))) : Bool)
          then
            (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__768 3 0)
            (pure (sys_pmp_count >b (BitVec.toNatInt (0b00#2 ++ idx)))))
          else
            (do
              if (((Sail.BitVec.extractLsb v__768 11 4) == (0x3C#8 : (BitVec 8))) : Bool)
              then
                (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__768 3 0)
                (pure (sys_pmp_count >b (BitVec.toNatInt (0b01#2 ++ idx)))))
              else
                (do
                  if (((Sail.BitVec.extractLsb v__768 11 4) == (0x3D#8 : (BitVec 8))) : Bool)
                  then
                    (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__768 3 0)
                    (pure (sys_pmp_count >b (BitVec.toNatInt (0b10#2 ++ idx)))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__768 11 4) == (0x3E#8 : (BitVec 8))) : Bool)
                      then
                        (let idx : (BitVec 4) := (Sail.BitVec.extractLsb v__768 3 0)
                        (pure (sys_pmp_count >b (BitVec.toNatInt (0b11#2 ++ idx)))))
                      else
                        (do
                          match (v__768, g__72, g__73) with
                          | (0x001, g__74, g__75) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x002, g__76, g__77) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x003, g__78, g__79) =>
                            (pure ((← (currentlyEnabled Ext_F)) || (← (currentlyEnabled
                                    Ext_Zfinx))))
                          | (0x008, g__80, g__81) => (currentlyEnabled Ext_V)
                          | (0x009, g__82, g__83) => (currentlyEnabled Ext_V)
                          | (0x00A, g__84, g__85) => (currentlyEnabled Ext_V)
                          | (0x00F, g__86, g__87) => (currentlyEnabled Ext_V)
                          | (0xC20, g__88, g__89) => (currentlyEnabled Ext_V)
                          | (0xC21, g__90, g__91) => (currentlyEnabled Ext_V)
                          | (0xC22, g__92, g__93) => (currentlyEnabled Ext_V)
                          | (0x321, g__94, g__95) => (currentlyEnabled Ext_Smcntrpmf)
                          | (0x721, g__96, g__97) =>
                            (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
                          | (0x322, g__98, g__99) => (currentlyEnabled Ext_Smcntrpmf)
                          | (0x722, g__100, g__101) =>
                            (pure ((← (currentlyEnabled Ext_Smcntrpmf)) && (xlen == 32)))
                          | (0x180, g__72, g__102) =>
                            (pure ((← (currentlyEnabled Ext_S)) && (not
                                  ((g__72 == Supervisor) && ((_get_Mstatus_TVM (← readReg mstatus)) == 1#1)))))
                          | (0xC00, g__72, g__103) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && (← (counter_enabled 0
                                    g__72))))
                          | (0xC01, g__72, g__104) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && (← (counter_enabled 1
                                    g__72))))
                          | (0xC02, g__72, g__105) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && (← (counter_enabled 2
                                    g__72))))
                          | (0xC80, g__72, g__106) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                      0 g__72)))))
                          | (0xC81, g__72, g__107) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                      1 g__72)))))
                          | (0xC82, g__72, g__108) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && ((xlen == 32) && (← (counter_enabled
                                      2 g__72)))))
                          | (0xB00, g__109, g__110) => (currentlyEnabled Ext_Zicntr)
                          | (0xB02, g__111, g__112) => (currentlyEnabled Ext_Zicntr)
                          | (0xB80, g__113, g__114) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
                          | (0xB82, g__115, g__116) =>
                            (pure ((← (currentlyEnabled Ext_Zicntr)) && (xlen == 32)))
                          | _ => (pure false)))))))

/-- Type quantifiers: k_ex152586_ : Bool -/
def check_CSR (csr : (BitVec 12)) (p : Privilege) (isWrite : Bool) : SailM Bool := do
  (pure ((check_CSR_priv csr p) && ((check_CSR_access csr isWrite) && (← (is_CSR_accessible csr p
            isWrite)))))

def exception_delegatee (e : ExceptionType) (p : Privilege) : SailM Privilege := do
  let idx := (BitVec.toNatInt (exceptionType_bits_forwards e))
  let super ← do (pure (bit_to_bool (BitVec.access (← readReg medeleg) idx)))
  let deleg ← do
    if (((← (currentlyEnabled Ext_S)) && super) : Bool)
    then (pure Supervisor)
    else (pure Machine)
  if ((zopz0zI_u (privLevel_to_bits deleg) (privLevel_to_bits p)) : Bool)
  then (pure p)
  else (pure deleg)

def findPendingInterrupt (ip : (BitVec 32)) : (Option InterruptType) :=
  let ip := (Mk_Minterrupts ip)
  if (((_get_Minterrupts_MEI ip) == 1#1) : Bool)
  then (some I_M_External)
  else
    (if (((_get_Minterrupts_MSI ip) == 1#1) : Bool)
    then (some I_M_Software)
    else
      (if (((_get_Minterrupts_MTI ip) == 1#1) : Bool)
      then (some I_M_Timer)
      else
        (if (((_get_Minterrupts_SEI ip) == 1#1) : Bool)
        then (some I_S_External)
        else
          (if (((_get_Minterrupts_SSI ip) == 1#1) : Bool)
          then (some I_S_Software)
          else
            (if (((_get_Minterrupts_STI ip) == 1#1) : Bool)
            then (some I_S_Timer)
            else none)))))

def getPendingSet (priv : Privilege) : SailM (Option ((BitVec 32) × Privilege)) := do
  assert ((← (currentlyEnabled Ext_S)) || ((← readReg mideleg) == (zeros (n := 32)))) "model/sys/sys_control.sail:70.58-70.59"
  let pending_m ← do
    (pure ((← readReg mip) &&& ((← readReg mie) &&& (Complement.complement (← readReg mideleg)))))
  let pending_s ← do (pure ((← readReg mip) &&& ((← readReg mie) &&& (← readReg mideleg))))
  let mIE ← do
    (pure (((priv == Machine) && ((_get_Mstatus_MIE (← readReg mstatus)) == 1#1)) || ((priv == Supervisor) || (priv == User))))
  let sIE ← do
    (pure (((priv == Supervisor) && ((_get_Mstatus_SIE (← readReg mstatus)) == 1#1)) || (priv == User)))
  if ((mIE && (pending_m != (zeros (n := 32)))) : Bool)
  then (pure (some (pending_m, Machine)))
  else
    (if ((sIE && (pending_s != (zeros (n := 32)))) : Bool)
    then (pure (some (pending_s, Supervisor)))
    else (pure none))

def shouldWakeForInterrupt (_ : Unit) : SailM Bool := do
  (pure (((← readReg mip) &&& (← readReg mie)) != (zeros (n := 32))))

def dispatchInterrupt (priv : Privilege) : SailM (Option (InterruptType × Privilege)) := do
  match (← (getPendingSet priv)) with
  | none => (pure none)
  | .some (ip, p) =>
    (match (findPendingInterrupt ip) with
    | none => (pure none)
    | .some i => (pure (some (i, p))))

def tval (excinfo : (Option (BitVec 32))) : (BitVec 32) :=
  match excinfo with
  | .some e => e
  | none => (zeros (n := 32))

def track_trap (p : Privilege) : SailM Unit := do
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  match p with
  | Machine =>
    (do
      (csr_name_write_callback "mcause" (← readReg mcause))
      (csr_name_write_callback "mtval" (← readReg mtval))
      (csr_name_write_callback "mepc" (← readReg mepc)))
  | Supervisor =>
    (do
      (csr_name_write_callback "scause" (← readReg scause))
      (csr_name_write_callback "stval" (← readReg stval))
      (csr_name_write_callback "sepc" (← readReg sepc)))
  | User => (internal_error "model/sys/sys_control.sail" 148 "Invalid privilege level")
  | VirtualUser =>
    (internal_error "model/sys/sys_control.sail" 149 "Hypervisor extension not supported")
  | VirtualSupervisor =>
    (internal_error "model/sys/sys_control.sail" 150 "Hypervisor extension not supported")

/-- Type quantifiers: k_ex152652_ : Bool -/
def trap_handler (del_priv : Privilege) (intr : Bool) (c : (BitVec 6)) (pc : (BitVec 32)) (info : (Option (BitVec 32))) (ext : (Option Unit)) : SailM (BitVec 32) := do
  let _ : Unit := (trap_callback ())
  if ((get_config_print_platform ()) : Bool)
  then
    (pure (print_endline
        (HAppend.hAppend "handling "
          (HAppend.hAppend
            (if (intr : Bool)
            then "int#"
            else "exc#")
            (HAppend.hAppend (BitVec.toFormatted c)
              (HAppend.hAppend " at priv "
                (HAppend.hAppend (← (privLevel_to_str del_priv))
                  (HAppend.hAppend " with tval " (BitVec.toFormatted (tval info))))))))))
  else (pure ())
  if ((hartSupports Ext_Zicfilp) : Bool)
  then (zicfilp_preserve_elp_on_trap del_priv)
  else (pure ())
  match del_priv with
  | Machine =>
    (do
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (32 -i 1) (32 -i 1)
        (bool_to_bits intr))
      writeReg mcause (Sail.BitVec.updateSubrange (← readReg mcause) (32 -i 2) 0
        (zero_extend (m := (32 -i 1)) c))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7
        (_get_Mstatus_MIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits (← readReg cur_privilege)))
      writeReg mtval (tval info)
      writeReg mepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg mcause)))
  | Supervisor =>
    (do
      assert (← (currentlyEnabled Ext_S)) "no supervisor mode present for delegation"
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (32 -i 1) (32 -i 1)
        (bool_to_bits intr))
      writeReg scause (Sail.BitVec.updateSubrange (← readReg scause) (32 -i 2) 0
        (zero_extend (m := (32 -i 1)) c))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5
        (_get_Mstatus_SIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1 0#1)
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8
        (← do
          match (← readReg cur_privilege) with
          | User => (pure 0#1)
          | Supervisor => (pure 1#1)
          | Machine =>
            (internal_error "model/sys/sys_control.sail" 195 "invalid privilege for s-mode trap")
          | VirtualUser =>
            (internal_error "model/sys/sys_control.sail" 196 "Hypervisor extension not supported")
          | VirtualSupervisor =>
            (internal_error "model/sys/sys_control.sail" 197 "Hypervisor extension not supported")))
      writeReg stval (tval info)
      writeReg sepc pc
      writeReg cur_privilege del_priv
      let _ : Unit := (handle_trap_extension del_priv pc ext)
      (track_trap del_priv)
      (prepare_trap_vector del_priv (← readReg scause)))
  | User => (internal_error "model/sys/sys_control.sail" 210 "Invalid privilege level")
  | VirtualUser =>
    (internal_error "model/sys/sys_control.sail" 211 "Hypervisor extension not supported")
  | VirtualSupervisor =>
    (internal_error "model/sys/sys_control.sail" 212 "Hypervisor extension not supported")

def exception_handler (cur_priv : Privilege) (ctl : ctl_result) (pc : (BitVec 32)) : SailM (BitVec 32) := do
  match ctl with
  | .CTL_TRAP e =>
    (do
      let del_priv ← do (exception_delegatee e.trap cur_priv)
      if ((get_config_print_platform ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "trapping from "
              (HAppend.hAppend (← (privLevel_to_str cur_priv))
                (HAppend.hAppend " to "
                  (HAppend.hAppend (← (privLevel_to_str del_priv))
                    (HAppend.hAppend " to handle " (exceptionType_to_str e.trap))))))))
      else (pure ())
      (trap_handler del_priv false (exceptionType_bits_forwards e.trap) pc e.excinfo e.ext))
  | .CTL_MRET () =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
        (_get_Mstatus_MPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 1#1)
      writeReg cur_privilege (← (privLevel_bits_forwards
          ((_get_Mstatus_MPP (← readReg mstatus)), 0#1)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
        (privLevel_to_bits
          (← do
            if ((← (currentlyEnabled Ext_U)) : Bool)
            then (pure User)
            else (pure Machine))))
      if ((bne (← readReg cur_privilege) Machine) : Bool)
      then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
      else (pure ())
      if ((hartSupports Ext_Zicfilp) : Bool)
      then (zicfilp_restore_elp_on_xret XRET_M (← readReg cur_privilege))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      if ((get_config_print_platform ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (← (privLevel_to_str prev_priv))
                (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
      else (pure ())
      (prepare_xret_target Machine))
  | .CTL_SRET () =>
    (do
      let prev_priv ← do readReg cur_privilege
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
        (_get_Mstatus_SPIE (← readReg mstatus)))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 1#1)
      writeReg cur_privilege (← do
        if (((_get_Mstatus_SPP (← readReg mstatus)) == 1#1) : Bool)
        then (pure Supervisor)
        else (pure User))
      writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 0#1)
      if ((bne (← readReg cur_privilege) Machine) : Bool)
      then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
      else (pure ())
      if ((hartSupports Ext_Zicfilp) : Bool)
      then (zicfilp_restore_elp_on_xret XRET_S (← readReg cur_privilege))
      else (pure ())
      (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
      if ((get_config_print_platform ()) : Bool)
      then
        (pure (print_endline
            (HAppend.hAppend "ret-ing from "
              (HAppend.hAppend (← (privLevel_to_str prev_priv))
                (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
      else (pure ())
      (prepare_xret_target Supervisor))

def xtval_exception_value (e : ExceptionType) (excinfo : (BitVec 32)) : (Option (BitVec 32)) :=
  if ((match e with
     | .E_Breakpoint () => true
     | .E_Load_Addr_Align () => true
     | .E_Load_Access_Fault () => true
     | .E_SAMO_Addr_Align () => true
     | .E_SAMO_Access_Fault () => true
     | .E_Fetch_Addr_Align () => true
     | .E_Fetch_Access_Fault () => true
     | .E_Illegal_Instr () => true
     | _ => true) : Bool)
  then (some excinfo)
  else none

def handle_exception (xtval : (BitVec 32)) (e : ExceptionType) : SailM Unit := do
  let t : sync_exception :=
    { trap := e
      excinfo := (xtval_exception_value e xtval)
      ext := none }
  (set_next_pc (← (exception_handler (← readReg cur_privilege) (CTL_TRAP t) (← readReg PC))))

def handle_interrupt (i : InterruptType) (del_priv : Privilege) : SailM Unit := do
  (set_next_pc
    (← (trap_handler del_priv true (interruptType_bits_forwards i) (← readReg PC) none none)))

def reset_misa (_ : Unit) : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 0 0
    (bool_to_bits (hartSupports Ext_A)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 2 2
    (bool_to_bits (hartSupports Ext_C)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 1 1
    (bool_to_bits (hartSupports Ext_B)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12
    (bool_to_bits (hartSupports Ext_M)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 20 20
    (bool_to_bits (hartSupports Ext_U)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 18 18
    (bool_to_bits (hartSupports Ext_S)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 21 21
    (bool_to_bits (hartSupports Ext_V)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 4 4 (bool_to_bits base_E_enabled))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 8 8
    (Complement.complement (_get_Misa_E (← readReg misa))))
  if (((hartSupports Ext_F) && (hartSupports Ext_Zfinx)) : Bool)
  then (internal_error "model/sys/sys_control.sail" 308 "F and Zfinx cannot both be enabled!")
  else (pure ())
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 5 5
    (bool_to_bits (hartSupports Ext_F)))
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 3 3 0#1)
  (csr_name_write_callback "misa" (← readReg misa))

def set_pc_reset_address (addr : (BitVec 64)) : SailM Unit := do
  writeReg pc_reset_address (trunc (m := 32) addr)

def reset_sys (_ : Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  (reset_misa ())
  (cancel_reservation ())
  writeReg PC (← readReg pc_reset_address)
  writeReg nextPC (← readReg pc_reset_address)
  writeReg mcause (zeros (n := 32))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 9 9
    (bool_to_bits (false : Bool)))
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 8 8
    (bool_to_bits (false : Bool)))
  if ((hartSupports Ext_Zicfilp) : Bool)
  then writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 10 10 0#1)
  else (pure ())
  writeReg vstart (zeros (n := 32))
  writeReg vl (zeros (n := 32))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 0b00#2)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (32 -i 1) (32 -i 1) 1#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (32 -i 2) 8
    (zeros (n := (32 -i 9))))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 0b000#3)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 0b000#3)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_add_meta (r : (Result k_t ExceptionType)) (m : Unit) : (Result (k_t × Unit) ExceptionType) :=
  match r with
  | .Ok v => (Ok (v, m))
  | .Err e => (Err e)

/-- Type quantifiers: k_t : Type -/
def MemoryOpResult_drop_meta (r : (Result (k_t × Unit) ExceptionType)) : (Result k_t ExceptionType) :=
  match r with
  | .Ok (v, m) => (Ok v)
  | .Err e => (Err e)

