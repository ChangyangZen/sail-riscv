// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// ******************************************************************************
// This file implements part of the vector extension.
// Chapter 14: Vector Reduction Instructions
// ******************************************************************************

// ******************** OPIVV (Widening Integer Reduction) **********************
union clause instruction = RIVVTYPE : (rivvfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_rivvfunct6 : rivvfunct6 <-> bits(6) = {
  IVV_VWREDSUMU   <-> 0b110000,
  IVV_VWREDSUM    <-> 0b110001
}

mapping clause encdec = RIVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> encdec_rivvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b000 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_V)

function clause execute(RIVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let SEW_widen = SEW * 2;

  if illegal_widening_reduction(SEW_widen) then return Illegal_Instruction();

  assert(SEW_widen <= 64);

  let num_elem_vs = get_num_elem(LMUL_pow, SEW);
  let num_elem_vd = get_num_elem(0, SEW_widen); // vd regardless of LMUL setting

  if unsigned(vl) == 0 then return RETIRE_SUCCESS; // if vl=0, no operation is performed

  if SEW == 8 then {
    var sum : bits(16) = read_single_element(16, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        let elem : bits(16) = match funct6 {
          IVV_VWREDSUMU  => to_bits_unsafe(16, unsigned(vs2_val)),
          IVV_VWREDSUM   => to_bits_unsafe(16, signed(vs2_val))
        };
        sum = sum + elem
      }
    };
    write_single_element(16, 0, vd, sum)
  } else if SEW == 16 then {
    var sum : bits(32) = read_single_element(32, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        let elem : bits(32) = match funct6 {
          IVV_VWREDSUMU  => to_bits_unsafe(32, unsigned(vs2_val)),
          IVV_VWREDSUM   => to_bits_unsafe(32, signed(vs2_val))
        };
        sum = sum + elem
      }
    };
    write_single_element(32, 0, vd, sum)
  } else {
    var sum : bits(64) = read_single_element(64, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        let elem : bits(64) = match funct6 {
          IVV_VWREDSUMU  => to_bits_unsafe(64, unsigned(vs2_val)),
          IVV_VWREDSUM   => to_bits_unsafe(64, signed(vs2_val))
        };
        sum = sum + elem
      }
    };
    write_single_element(64, 0, vd, sum)
  };

  // other elements in vd are treated as tail elements, currently remain unchanged
  // TODO: configuration support for agnostic behavior
  set_vstart(zeros());
  RETIRE_SUCCESS
}

mapping rivvtype_mnemonic : rivvfunct6 <-> string = {
  IVV_VWREDSUMU  <-> "vwredsumu.vs",
  IVV_VWREDSUM   <-> "vwredsum.vs"
}

mapping clause assembly = RIVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> rivvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

// ****************** OPMVV (Single-Width Integer Reduction) ********************
union clause instruction = RMVVTYPE : (rmvvfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_rmvvfunct6 : rmvvfunct6 <-> bits(6) = {
  MVV_VREDSUM     <-> 0b000000,
  MVV_VREDAND     <-> 0b000001,
  MVV_VREDOR      <-> 0b000010,
  MVV_VREDXOR     <-> 0b000011,
  MVV_VREDMINU    <-> 0b000100,
  MVV_VREDMIN     <-> 0b000101,
  MVV_VREDMAXU    <-> 0b000110,
  MVV_VREDMAX     <-> 0b000111
}

mapping clause encdec = RMVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> encdec_rmvvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_V)

function clause execute(RMVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem_vs = get_num_elem(LMUL_pow, SEW);
  let num_elem_vd = get_num_elem(0, SEW); // vd regardless of LMUL setting

  if illegal_reduction() then return Illegal_Instruction();

  if unsigned(vl) == 0 then return RETIRE_SUCCESS; // if vl=0, no operation is performed

  if SEW == 8 then {
    var sum : bits(8) = read_single_element(8, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        sum = match funct6 {
          MVV_VREDSUM   => sum + vs2_val,
          MVV_VREDAND   => sum & vs2_val,
          MVV_VREDOR    => sum | vs2_val,
          MVV_VREDXOR   => sum ^ vs2_val,
          MVV_VREDMIN   => to_bits_unsafe(8, min(signed(vs2_val), signed(sum))),
          MVV_VREDMINU  => to_bits_unsafe(8, min(unsigned(vs2_val), unsigned(sum))),
          MVV_VREDMAX   => to_bits_unsafe(8, max(signed(vs2_val), signed(sum))),
          MVV_VREDMAXU  => to_bits_unsafe(8, max(unsigned(vs2_val), unsigned(sum)))
        }
      }
    };
    write_single_element(8, 0, vd, sum)
  } else if SEW == 16 then {
    var sum : bits(16) = read_single_element(16, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        sum = match funct6 {
          MVV_VREDSUM   => sum + vs2_val,
          MVV_VREDAND   => sum & vs2_val,
          MVV_VREDOR    => sum | vs2_val,
          MVV_VREDXOR   => sum ^ vs2_val,
          MVV_VREDMIN   => to_bits_unsafe(16, min(signed(vs2_val), signed(sum))),
          MVV_VREDMINU  => to_bits_unsafe(16, min(unsigned(vs2_val), unsigned(sum))),
          MVV_VREDMAX   => to_bits_unsafe(16, max(signed(vs2_val), signed(sum))),
          MVV_VREDMAXU  => to_bits_unsafe(16, max(unsigned(vs2_val), unsigned(sum)))
        }
      }
    };
    write_single_element(16, 0, vd, sum)
  } else if SEW == 32 then {
    var sum : bits(32) = read_single_element(32, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        sum = match funct6 {
          MVV_VREDSUM   => sum + vs2_val,
          MVV_VREDAND   => sum & vs2_val,
          MVV_VREDOR    => sum | vs2_val,
          MVV_VREDXOR   => sum ^ vs2_val,
          MVV_VREDMIN   => to_bits_unsafe(32, min(signed(vs2_val), signed(sum))),
          MVV_VREDMINU  => to_bits_unsafe(32, min(unsigned(vs2_val), unsigned(sum))),
          MVV_VREDMAX   => to_bits_unsafe(32, max(signed(vs2_val), signed(sum))),
          MVV_VREDMAXU  => to_bits_unsafe(32, max(unsigned(vs2_val), unsigned(sum)))
        }
      }
    };
    write_single_element(32, 0, vd, sum)
  } else {
    var sum : bits(64) = read_single_element(64, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        sum = match funct6 {
          MVV_VREDSUM   => sum + vs2_val,
          MVV_VREDAND   => sum & vs2_val,
          MVV_VREDOR    => sum | vs2_val,
          MVV_VREDXOR   => sum ^ vs2_val,
          MVV_VREDMIN   => to_bits_unsafe(64, min(signed(vs2_val), signed(sum))),
          MVV_VREDMINU  => to_bits_unsafe(64, min(unsigned(vs2_val), unsigned(sum))),
          MVV_VREDMAX   => to_bits_unsafe(64, max(signed(vs2_val), signed(sum))),
          MVV_VREDMAXU  => to_bits_unsafe(64, max(unsigned(vs2_val), unsigned(sum)))
        }
      }
    };
    write_single_element(64, 0, vd, sum)
  };

  // other elements in vd are treated as tail elements, currently remain unchanged
  // TODO: configuration support for agnostic behavior
  set_vstart(zeros());
  RETIRE_SUCCESS
}

mapping rmvvtype_mnemonic : rmvvfunct6 <-> string = {
  MVV_VREDSUM   <-> "vredsum.vs",
  MVV_VREDAND   <-> "vredand.vs",
  MVV_VREDOR    <-> "vredor.vs",
  MVV_VREDXOR   <-> "vredxor.vs",
  MVV_VREDMINU  <-> "vredminu.vs",
  MVV_VREDMIN   <-> "vredmin.vs",
  MVV_VREDMAXU  <-> "vredmaxu.vs",
  MVV_VREDMAX   <-> "vredmax.vs"
}

mapping clause assembly = RMVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> rmvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)
