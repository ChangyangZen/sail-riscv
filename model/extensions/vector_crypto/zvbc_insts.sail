// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

function clause currentlyEnabled(Ext_Zvbc) = hartSupports(Ext_Zvbc) & currentlyEnabled(Ext_V)

union clause instruction = VCLMUL_VV : (bits(1), vregidx, vregidx, vregidx)

mapping clause encdec = VCLMUL_VV (vm, vs2, vs1, vd)
  <-> 0b001100 @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbc) & get_sew() == 64

mapping clause assembly = VCLMUL_VV (vm, vs2, vs1, vd)
  <-> "vclmul.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

function clause execute (VCLMUL_VV(vm, vs2, vs1, vd)) = {
  let SEW       = get_sew();
  let LMUL_pow  = get_lmul_pow();
  let num_elem  = get_num_elem(LMUL_pow, SEW);

  if SEW != 64 then return Illegal_Instruction();

  foreach (i from 0 to (num_elem - 1)) {
    let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
      Ok(v)   => v,
      Err(()) => return Illegal_Instruction()
    };
    if active then {
      let vs1_val : bits(64) = read_single_element(64, i, vs1);
      let vs2_val : bits(64) = read_single_element(64, i, vs2);
      let prod : bits(128) = carryless_mul(vs1_val, vs2_val);
      write_single_element(64, i, vd, prod[63 .. 0])
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VCLMUL_VX : (bits(1), vregidx, regidx, vregidx)

mapping clause encdec = VCLMUL_VX (vm, vs2, rs1, vd)
  <-> 0b001100 @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b110 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbc) & get_sew() == 64

mapping clause assembly = VCLMUL_VX (vm, vs2, rs1, vd)
  <-> "vclmul.vx" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

function clause execute (VCLMUL_VX(vm, vs2, rs1, vd)) = {
  let SEW       = get_sew();
  let LMUL_pow  = get_lmul_pow();
  let num_elem  = get_num_elem(LMUL_pow, SEW);

  if SEW != 64 then return Illegal_Instruction();

  let rs1_val : bits(64) = get_scalar(rs1, 64);

  foreach (i from 0 to (num_elem - 1)) {
    let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
      Ok(v)   => v,
      Err(()) => return Illegal_Instruction()
    };
    if active then {
      let vs2_val : bits(64) = read_single_element(64, i, vs2);
      let prod : bits(128) = carryless_mul(rs1_val, vs2_val);
      write_single_element(64, i, vd, prod[63 .. 0])
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VCLMULH_VV : (bits(1), vregidx, vregidx, vregidx)

mapping clause encdec = VCLMULH_VV (vm, vs2, vs1, vd)
  <-> 0b001101 @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbc) & get_sew() == 64

mapping clause assembly = VCLMULH_VV (vm, vs2, vs1, vd)
  <-> "vclmulh.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

function clause execute (VCLMULH_VV(vm, vs2, vs1, vd)) = {
  let SEW       = get_sew();
  let LMUL_pow  = get_lmul_pow();
  let num_elem  = get_num_elem(LMUL_pow, SEW);

  if SEW != 64 then return Illegal_Instruction();

  foreach (i from 0 to (num_elem - 1)) {
    let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
      Ok(v)   => v,
      Err(()) => return Illegal_Instruction()
    };
    if active then {
      let vs1_val : bits(64) = read_single_element(64, i, vs1);
      let vs2_val : bits(64) = read_single_element(64, i, vs2);
      let prod : bits(128) = carryless_mul(vs1_val, vs2_val);
      write_single_element(64, i, vd, prod[127 .. 64])
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VCLMULH_VX : (bits(1), vregidx, regidx, vregidx)

mapping clause encdec = VCLMULH_VX (vm, vs2, rs1, vd)
  <-> 0b001101 @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b110 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbc) & get_sew() == 64

mapping clause assembly = VCLMULH_VX (vm, vs2, rs1, vd)
  <-> "vclmulh.vx" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

function clause execute (VCLMULH_VX(vm, vs2, rs1, vd)) = {
  let SEW       = get_sew();
  let LMUL_pow  = get_lmul_pow();
  let num_elem  = get_num_elem(LMUL_pow, SEW);

  if SEW != 64 then return Illegal_Instruction();

  let rs1_val : bits(64) = get_scalar(rs1, 64);

  foreach (i from 0 to (num_elem - 1)) {
    let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
      Ok(v)   => v,
      Err(()) => return Illegal_Instruction()
    };
    if active then {
      let vs2_val : bits(64) = read_single_element(64, i, vs2);
      let prod : bits(128) = carryless_mul(rs1_val, vs2_val);
      write_single_element(64, i, vd, prod[127 .. 64])
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}
