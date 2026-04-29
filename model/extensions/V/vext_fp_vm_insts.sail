// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// ******************************************************************************
// This file implements part of the vector extension.
// Mask instructions from Chap 13 (floating-point)
// ******************************************************************************

// ****************************** OPFVV (VVMTYPE) *******************************
// FVVM instructions' destination is a mask register
union clause instruction = FVVMTYPE : (fvvmfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_fvvmfunct6 : fvvmfunct6 <-> bits(6) = {
  FVVM_VMFEQ      <-> 0b011000,
  FVVM_VMFLE      <-> 0b011001,
  FVVM_VMFLT      <-> 0b011011,
  FVVM_VMFNE      <-> 0b011100
}

mapping clause encdec = FVVMTYPE(funct6, vm, vs2, vs1, vd)
  <-> encdec_fvvmfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b001 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_V)

function clause execute(FVVMTYPE(funct6, vm, vs2, vs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_vd_unmasked(SEW, rm_3b) then return Illegal_Instruction();
  assert(SEW != 8);

  if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(16) = read_single_element(16, i, vs1);
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        let res : bool = match funct6 {
          FVVM_VMFEQ => fp_eq(vs2_val, vs1_val),
          FVVM_VMFNE => ~(fp_eq(vs2_val, vs1_val)),
          FVVM_VMFLE => fp_le(vs2_val, vs1_val),
          FVVM_VMFLT => fp_lt(vs2_val, vs1_val)
        };
        assert(i < vlen);
        V(vd) = [V(vd) with i = bool_to_bit(res)]
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(32) = read_single_element(32, i, vs1);
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        let res : bool = match funct6 {
          FVVM_VMFEQ => fp_eq(vs2_val, vs1_val),
          FVVM_VMFNE => ~(fp_eq(vs2_val, vs1_val)),
          FVVM_VMFLE => fp_le(vs2_val, vs1_val),
          FVVM_VMFLT => fp_lt(vs2_val, vs1_val)
        };
        assert(i < vlen);
        V(vd) = [V(vd) with i = bool_to_bit(res)]
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(64) = read_single_element(64, i, vs1);
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        let res : bool = match funct6 {
          FVVM_VMFEQ => fp_eq(vs2_val, vs1_val),
          FVVM_VMFNE => ~(fp_eq(vs2_val, vs1_val)),
          FVVM_VMFLE => fp_le(vs2_val, vs1_val),
          FVVM_VMFLT => fp_lt(vs2_val, vs1_val)
        };
        assert(i < vlen);
        V(vd) = [V(vd) with i = bool_to_bit(res)]
      }
    }
  };

  set_vstart(zeros());
  RETIRE_SUCCESS
}

mapping fvvmtype_mnemonic : fvvmfunct6 <-> string = {
  FVVM_VMFEQ      <-> "vmfeq.vv",
  FVVM_VMFLE      <-> "vmfle.vv",
  FVVM_VMFLT      <-> "vmflt.vv",
  FVVM_VMFNE      <-> "vmfne.vv"
}

mapping clause assembly = FVVMTYPE(funct6, vm, vs2, vs1, vd)
  <-> fvvmtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

// ****************************** OPFVF (VFMTYPE) *******************************
// VFM instructions' destination is a mask register
union clause instruction = FVFMTYPE : (fvfmfunct6, bits(1), vregidx, fregidx, vregidx)

mapping encdec_fvfmfunct6 : fvfmfunct6 <-> bits(6) = {
  VFM_VMFEQ      <-> 0b011000,
  VFM_VMFLE      <-> 0b011001,
  VFM_VMFLT      <-> 0b011011,
  VFM_VMFNE      <-> 0b011100,
  VFM_VMFGT      <-> 0b011101,
  VFM_VMFGE      <-> 0b011111
}

mapping clause encdec = FVFMTYPE(funct6, vm, vs2, rs1, vd)
  <-> encdec_fvfmfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_freg(rs1) @ 0b101 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_V)

function clause execute(FVFMTYPE(funct6, vm, vs2, rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_vd_unmasked(SEW, rm_3b) then return Illegal_Instruction();
  assert(SEW != 8);

  if SEW == 16 then {
    let rs1_val : bits(16) = get_scalar_fp(rs1, 16);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        let res : bool = match funct6 {
          VFM_VMFEQ => fp_eq(vs2_val, rs1_val),
          VFM_VMFNE => ~(fp_eq(vs2_val, rs1_val)),
          VFM_VMFLE => fp_le(vs2_val, rs1_val),
          VFM_VMFLT => fp_lt(vs2_val, rs1_val),
          VFM_VMFGE => fp_ge(vs2_val, rs1_val),
          VFM_VMFGT => fp_gt(vs2_val, rs1_val)
        };
        assert(i < vlen);
        V(vd) = [V(vd) with i = bool_to_bit(res)]
      }
    }
  } else if SEW == 32 then {
    let rs1_val : bits(32) = get_scalar_fp(rs1, 32);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        let res : bool = match funct6 {
          VFM_VMFEQ => fp_eq(vs2_val, rs1_val),
          VFM_VMFNE => ~(fp_eq(vs2_val, rs1_val)),
          VFM_VMFLE => fp_le(vs2_val, rs1_val),
          VFM_VMFLT => fp_lt(vs2_val, rs1_val),
          VFM_VMFGE => fp_ge(vs2_val, rs1_val),
          VFM_VMFGT => fp_gt(vs2_val, rs1_val)
        };
        assert(i < vlen);
        V(vd) = [V(vd) with i = bool_to_bit(res)]
      }
    }
  } else {
    let rs1_val : bits(64) = get_scalar_fp(rs1, 64);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        let res : bool = match funct6 {
          VFM_VMFEQ => fp_eq(vs2_val, rs1_val),
          VFM_VMFNE => ~(fp_eq(vs2_val, rs1_val)),
          VFM_VMFLE => fp_le(vs2_val, rs1_val),
          VFM_VMFLT => fp_lt(vs2_val, rs1_val),
          VFM_VMFGE => fp_ge(vs2_val, rs1_val),
          VFM_VMFGT => fp_gt(vs2_val, rs1_val)
        };
        assert(i < vlen);
        V(vd) = [V(vd) with i = bool_to_bit(res)]
      }
    }
  };

  set_vstart(zeros());
  RETIRE_SUCCESS
}

mapping fvfmtype_mnemonic : fvfmfunct6 <-> string = {
  VFM_VMFEQ      <-> "vmfeq.vf",
  VFM_VMFLE      <-> "vmfle.vf",
  VFM_VMFLT      <-> "vmflt.vf",
  VFM_VMFNE      <-> "vmfne.vf",
  VFM_VMFGT      <-> "vmfgt.vf",
  VFM_VMFGE      <-> "vmfge.vf"
}

mapping clause assembly = FVFMTYPE(funct6, vm, vs2, rs1, vd)
  <-> fvfmtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ freg_name(rs1) ^ maybe_vmask(vm)
