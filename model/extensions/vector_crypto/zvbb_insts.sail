// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

function clause currentlyEnabled(Ext_Zvbb) = hartSupports(Ext_Zvbb) & currentlyEnabled(Ext_V)
function clause currentlyEnabled(Ext_Zvkb) = (hartSupports(Ext_Zvkb) | currentlyEnabled(Ext_Zvbb)) & currentlyEnabled(Ext_V)

union clause instruction = VANDN_VV : (bits(1), vregidx, vregidx, vregidx)

mapping clause encdec = VANDN_VV(vm, vs1, vs2, vd)
  <-> 0b000001 @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b000 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VANDN_VV(vm, vs1, vs2, vd)
  <-> "vandn.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

function clause execute (VANDN_VV(vm, vs1, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(8) = read_single_element(8, i, vs1);
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, ~(vs1_val) & vs2_val)
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(16) = read_single_element(16, i, vs1);
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, ~(vs1_val) & vs2_val)
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
        write_single_element(32, i, vd, ~(vs1_val) & vs2_val)
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
        write_single_element(64, i, vd, ~(vs1_val) & vs2_val)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VANDN_VX : (bits(1), vregidx, regidx, vregidx)

mapping clause encdec = VANDN_VX(vm, vs2, rs1, vd)
  <-> 0b000001 @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b100 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VANDN_VX(vm, vs2, rs1, vd)
  <-> "vandn.vx" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

function clause execute (VANDN_VX(vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    let rs1_val : bits(8) = get_scalar(rs1, 8);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, ~(rs1_val) & vs2_val)
      }
    }
  } else if SEW == 16 then {
    let rs1_val : bits(16) = get_scalar(rs1, 16);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, ~(rs1_val) & vs2_val)
      }
    }
  } else if SEW == 32 then {
    let rs1_val : bits(32) = get_scalar(rs1, 32);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, ~(rs1_val) & vs2_val)
      }
    }
  } else {
    let rs1_val : bits(64) = get_scalar(rs1, 64);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, ~(rs1_val) & vs2_val)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VBREV_V : (bits(1), vregidx, vregidx)

mapping clause encdec = VBREV_V(vm, vs2, vd)
  <-> 0b010010 @ vm @ encdec_vreg(vs2) @ 0b01010 @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VBREV_V(vm, vs2, vd)
  <-> "vbrev.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

function clause execute (VBREV_V(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, reverse_bits(vs2_val))
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, reverse_bits(vs2_val))
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, reverse_bits(vs2_val))
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, reverse_bits(vs2_val))
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VBREV8_V : (bits(1), vregidx, vregidx)

mapping clause encdec = VBREV8_V(vm, vs2, vd)
  <-> 0b010010 @ vm @ encdec_vreg(vs2) @ 0b01000 @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VBREV8_V(vm, vs2, vd)
  <-> "vbrev8.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

function clause execute (VBREV8_V(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, brev8(vs2_val))
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, brev8(vs2_val))
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, brev8(vs2_val))
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, brev8(vs2_val))
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VREV8_V : (bits(1), vregidx, vregidx)

mapping clause encdec = VREV8_V(vm, vs2, vd)
  <-> 0b010010 @ vm @ encdec_vreg(vs2) @ 0b01001 @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VREV8_V(vm, vs2, vd)
  <-> "vrev8.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

function clause execute (VREV8_V(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, rev8(vs2_val))
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, rev8(vs2_val))
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, rev8(vs2_val))
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, rev8(vs2_val))
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VCLZ_V : (bits(1), vregidx, vregidx)

mapping clause encdec = VCLZ_V (vm, vs2, vd)
  <-> 0b010010 @ vm @ encdec_vreg(vs2) @ 0b01100 @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VCLZ_V (vm, vs2, vd)
  <-> "vclz.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

function clause execute (VCLZ_V(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        let result  : bits(8) = to_bits(count_leading_zeros(vs2_val));
        write_single_element(8, i, vd, result)
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        let result  : bits(16) = to_bits(count_leading_zeros(vs2_val));
        write_single_element(16, i, vd, result)
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        let result  : bits(32) = to_bits(count_leading_zeros(vs2_val));
        write_single_element(32, i, vd, result)
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        let result  : bits(64) = to_bits(count_leading_zeros(vs2_val));
        write_single_element(64, i, vd, result)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VCTZ_V : (bits(1), vregidx, vregidx)

mapping clause encdec = VCTZ_V (vm, vs2, vd)
  <-> 0b010010 @ vm @ encdec_vreg(vs2) @ 0b01101 @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VCTZ_V (vm, vs2, vd)
  <-> "vctz.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

function clause execute (VCTZ_V(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        let result  : bits(8) = to_bits(count_trailing_zeros(vs2_val));
        write_single_element(8, i, vd, result)
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        let result  : bits(16) = to_bits(count_trailing_zeros(vs2_val));
        write_single_element(16, i, vd, result)
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        let result  : bits(32) = to_bits(count_trailing_zeros(vs2_val));
        write_single_element(32, i, vd, result)
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        let result  : bits(64) = to_bits(count_trailing_zeros(vs2_val));
        write_single_element(64, i, vd, result)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VCPOP_V : (bits(1), vregidx, vregidx)

mapping clause encdec = VCPOP_V (vm, vs2, vd)
  <-> 0b010010 @ vm @ encdec_vreg(vs2) @ 0b01110 @ 0b010 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VCPOP_V (vm, vs2, vd)
  <-> "vcpop.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

function clause execute (VCPOP_V(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        let result  : bits(8) = to_bits(count_ones(vs2_val));
        write_single_element(8, i, vd, result)
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        let result  : bits(16) = to_bits(count_ones(vs2_val));
        write_single_element(16, i, vd, result)
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        let result  : bits(32) = to_bits(count_ones(vs2_val));
        write_single_element(32, i, vd, result)
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        let result  : bits(64) = to_bits(count_ones(vs2_val));
        write_single_element(64, i, vd, result)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VROL_VV : (bits(1), vregidx, vregidx, vregidx)

mapping clause encdec = VROL_VV(vm, vs1, vs2, vd)
  <-> 0b010101 @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b000 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VROL_VV(vm, vs1, vs2, vd)
 <-> "vrol.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

function clause execute (VROL_VV(vm, vs1, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(8) = read_single_element(8, i, vs1);
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, vs2_val <<< vs1_val[2 .. 0])
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(16) = read_single_element(16, i, vs1);
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, vs2_val <<< vs1_val[3 .. 0])
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
        write_single_element(32, i, vd, vs2_val <<< vs1_val[4 .. 0])
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
        write_single_element(64, i, vd, vs2_val <<< vs1_val[5 .. 0])
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VROL_VX : (bits(1), vregidx, regidx, vregidx)

mapping clause encdec = VROL_VX(vm, vs2, rs1, vd)
  <-> 0b010101 @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b100 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VROL_VX(vm, vs2, rs1, vd)
 <-> "vrol.vx" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

function clause execute (VROL_VX(vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    let rs1_val : bits(8) = get_scalar(rs1, 8);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, vs2_val <<< rs1_val[2 .. 0])
      }
    }
  } else if SEW == 16 then {
    let rs1_val : bits(16) = get_scalar(rs1, 16);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, vs2_val <<< rs1_val[3 .. 0])
      }
    }
  } else if SEW == 32 then {
    let rs1_val : bits(32) = get_scalar(rs1, 32);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, vs2_val <<< rs1_val[4 .. 0])
      }
    }
  } else {
    let rs1_val : bits(64) = get_scalar(rs1, 64);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, vs2_val <<< rs1_val[5 .. 0])
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VROR_VV : (bits(1), vregidx, vregidx, vregidx)

mapping clause encdec = VROR_VV(vm, vs1, vs2, vd)
  <-> 0b010100 @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b000 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VROR_VV(vm, vs1, vs2, vd)
 <-> "vror.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

function clause execute (VROR_VV(vm, vs1, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(8) = read_single_element(8, i, vs1);
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, vs2_val >>> vs1_val[2 .. 0])
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs1_val : bits(16) = read_single_element(16, i, vs1);
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, vs2_val >>> vs1_val[3 .. 0])
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
        write_single_element(32, i, vd, vs2_val >>> vs1_val[4 .. 0])
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
        write_single_element(64, i, vd, vs2_val >>> vs1_val[5 .. 0])
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VROR_VX : (bits(1), vregidx, regidx, vregidx)

mapping clause encdec = VROR_VX(vm, vs2, rs1, vd)
  <-> 0b010100 @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b100 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VROR_VX(vm, vs2, rs1, vd)
 <-> "vror.vx" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1)^ maybe_vmask(vm)

function clause execute (VROR_VX(vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    let rs1_val : bits(8) = get_scalar(rs1, 8);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, vs2_val >>> rs1_val[2 .. 0])
      }
    }
  } else if SEW == 16 then {
    let rs1_val : bits(16) = get_scalar(rs1, 16);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, vs2_val >>> rs1_val[3 .. 0])
      }
    }
  } else if SEW == 32 then {
    let rs1_val : bits(32) = get_scalar(rs1, 32);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, vs2_val >>> rs1_val[4 .. 0])
      }
    }
  } else {
    let rs1_val : bits(64) = get_scalar(rs1, 64);
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, vs2_val >>> rs1_val[5 .. 0])
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VROR_VI : (bits(1), vregidx, bits(6), vregidx)

mapping clause encdec = VROR_VI(vm, vs2, uimm5 @ uimm40, vd)
  <-> 0b01010 @ uimm5 @ vm @ encdec_vreg(vs2) @ uimm40 : bits(5) @ 0b011 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvkb)

mapping clause assembly = VROR_VI(vm, vs2, uimm, vd)
 <-> "vror.vi" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ hex_bits_6(uimm) ^ maybe_vmask(vm)

function clause execute (VROR_VI(vm, vs2, uimm, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(8) = read_single_element(8, i, vs2);
        write_single_element(8, i, vd, vs2_val >>> uimm[2 .. 0])
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = read_single_element(16, i, vs2);
        write_single_element(16, i, vd, vs2_val >>> uimm[3 .. 0])
      }
    }
  } else if SEW == 32 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = read_single_element(32, i, vs2);
        write_single_element(32, i, vd, vs2_val >>> uimm[4 .. 0])
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = read_single_element(64, i, vs2);
        write_single_element(64, i, vd, vs2_val >>> uimm[5 .. 0])
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VWSLL_VV : (bits(1), vregidx, vregidx, vregidx)

mapping clause encdec = VWSLL_VV (vm, vs2, vs1, vd)
  <-> 0b110101 @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b000 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VWSLL_VV (vm, vs2, vs1, vd)
  <-> "vwsll.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

function clause execute (VWSLL_VV(vm, vs2, vs1, vd)) = {
  let SEW            = get_sew();
  let LMUL_pow       = get_lmul_pow();
  let num_elem       = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen)) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then return Illegal_Instruction();

  assert(SEW_widen <= 64);

  assert(num_elem <= vlen);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = zero_extend(read_single_element(8, i, vs2));
        let vs1_val : bits(16) = zero_extend(read_single_element(8, i, vs1));
        let shamt   : bits(16) = vs1_val & to_bits_unsafe(16, 15);
        let result  : bits(16) = vs2_val << shamt;
        write_single_element(16, i, vd, result)
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = zero_extend(read_single_element(16, i, vs2));
        let vs1_val : bits(32) = zero_extend(read_single_element(16, i, vs1));
        let shamt   : bits(32) = vs1_val & to_bits_unsafe(32, 31);
        let result  : bits(32) = vs2_val << shamt;
        write_single_element(32, i, vd, result)
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = zero_extend(read_single_element(32, i, vs2));
        let vs1_val : bits(64) = zero_extend(read_single_element(32, i, vs1));
        let shamt   : bits(64) = vs1_val & to_bits_unsafe(64, 63);
        let result  : bits(64) = vs2_val << shamt;
        write_single_element(64, i, vd, result)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VWSLL_VX : (bits(1), vregidx, regidx, vregidx)

mapping clause encdec = VWSLL_VX (vm, vs2, rs1, vd)
  <-> 0b110101 @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b100 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VWSLL_VX (vm, vs2, rs1, vd)
  <-> "vwsll.vx" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

function clause execute (VWSLL_VX(vm, vs2, rs1, vd)) = {
  let SEW            = get_sew();
  let LMUL_pow       = get_lmul_pow();
  let num_elem       = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then return Illegal_Instruction();

  assert(SEW_widen <= 64);

  if SEW == 8 then {
    let rs1_val : bits(16) = zero_extend(get_scalar(rs1, 8));
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = zero_extend(read_single_element(8, i, vs2));
        let result : bits(16) = vs2_val << (rs1_val & to_bits_unsafe(16, 15));
        write_single_element(16, i, vd, result)
      }
    }
  } else if SEW == 16 then {
    let rs1_val : bits(32) = zero_extend(get_scalar(rs1, 16));
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = zero_extend(read_single_element(16, i, vs2));
        let result : bits(32) = vs2_val << (rs1_val & to_bits_unsafe(32, 31));
        write_single_element(32, i, vd, result)
      }
    }
  } else {
    let rs1_val : bits(64) = zero_extend(get_scalar(rs1, 32));
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = zero_extend(read_single_element(32, i, vs2));
        let result : bits(64) = vs2_val << (rs1_val & to_bits_unsafe(64, 63));
        write_single_element(64, i, vd, result)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = VWSLL_VI : (bits(1), vregidx, bits(5), vregidx)

mapping clause encdec = VWSLL_VI (vm, vs2, uimm, vd)
  <-> 0b110101 @ vm @ encdec_vreg(vs2) @ uimm @ 0b011 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_Zvbb)

mapping clause assembly = VWSLL_VI (vm, vs2, uimm, vd)
  <-> "vwsll.vi" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ hex_bits_5(uimm) ^ maybe_vmask(vm)

function clause execute (VWSLL_VI(vm, vs2, uimm, vd)) = {
  let SEW            = get_sew();
  let LMUL_pow       = get_lmul_pow();
  let num_elem       = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then return Illegal_Instruction();

  assert(SEW_widen <= 64);

  assert(num_elem <= vlen);

  if SEW == 8 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(16) = zero_extend(read_single_element(8, i, vs2));
        let shamt   : bits(16) = to_bits_unsafe(16, unsigned(uimm)) & to_bits_unsafe(16, 15);
        let result  : bits(16) = vs2_val << shamt;
        write_single_element(16, i, vd, result)
      }
    }
  } else if SEW == 16 then {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(32) = zero_extend(read_single_element(16, i, vs2));
        let shamt   : bits(32) = to_bits_unsafe(32, unsigned(uimm)) & to_bits_unsafe(32, 31);
        let result  : bits(32) = vs2_val << shamt;
        write_single_element(32, i, vd, result)
      }
    }
  } else {
    foreach (i from 0 to (num_elem - 1)) {
      let active : bool = match is_active_vector_element(num_elem, LMUL_pow_widen, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let vs2_val : bits(64) = zero_extend(read_single_element(32, i, vs2));
        let shamt   : bits(64) = to_bits_unsafe(64, unsigned(uimm)) & to_bits_unsafe(64, 63);
        let result  : bits(64) = vs2_val << shamt;
        write_single_element(64, i, vd, result)
      }
    }
  };
  set_vstart(zeros());
  RETIRE_SUCCESS
}
