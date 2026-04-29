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

// ********************* OPFVV (Floating-Point Reduction) ***********************
union clause instruction = RFVVTYPE : (rfvvfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_rfvvfunct6 : rfvvfunct6 <-> bits(6) = {
  FVV_VFREDOSUM   <-> 0b000011,
  FVV_VFREDUSUM   <-> 0b000001,
  FVV_VFREDMAX    <-> 0b000111,
  FVV_VFREDMIN    <-> 0b000101,
  FVV_VFWREDOSUM  <-> 0b110011,
  FVV_VFWREDUSUM  <-> 0b110001
}

mapping clause encdec = RFVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> encdec_rfvvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b001 @ encdec_vreg(vd) @ 0b1010111
  when currentlyEnabled(Ext_V)

val process_rfvv_single : (rfvvfunct6, bits(1), vregidx, vregidx, vregidx, nat1, sew_bitsize, range(-3, 3)) -> ExecutionResult
function process_rfvv_single(funct6, vm, vs2, vs1, vd, num_elem_vs, SEW, LMUL_pow) = {
  let rm_3b = fcsr[FRM];
  let num_elem_vd = get_num_elem(0, SEW); // vd regardless of LMUL setting

  if illegal_fp_reduction(SEW, rm_3b) then return Illegal_Instruction();
  assert(SEW != 8);

  if unsigned(vl) == 0 then return RETIRE_SUCCESS; // if vl=0, no operation is performed

  if SEW == 16 then {
    var sum : bits(16) = read_single_element(16, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let elem : bits(16) = read_single_element(16, i, vs2);
        sum = match funct6 {
          // currently ordered/unordered sum reductions do the same operations
          FVV_VFREDOSUM   => fp_add(rm_3b, sum, elem),
          FVV_VFREDUSUM   => fp_add(rm_3b, sum, elem),
          FVV_VFREDMAX    => fp_max(sum, elem),
          FVV_VFREDMIN    => fp_min(sum, elem),
          _               => internal_error(__FILE__, __LINE__, "Widening op unexpected")
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
        let elem : bits(32) = read_single_element(32, i, vs2);
        sum = match funct6 {
          // currently ordered/unordered sum reductions do the same operations
          FVV_VFREDOSUM   => fp_add(rm_3b, sum, elem),
          FVV_VFREDUSUM   => fp_add(rm_3b, sum, elem),
          FVV_VFREDMAX    => fp_max(sum, elem),
          FVV_VFREDMIN    => fp_min(sum, elem),
          _               => internal_error(__FILE__, __LINE__, "Widening op unexpected")
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
        let elem : bits(64) = read_single_element(64, i, vs2);
        sum = match funct6 {
          // currently ordered/unordered sum reductions do the same operations
          FVV_VFREDOSUM   => fp_add(rm_3b, sum, elem),
          FVV_VFREDUSUM   => fp_add(rm_3b, sum, elem),
          FVV_VFREDMAX    => fp_max(sum, elem),
          FVV_VFREDMIN    => fp_min(sum, elem),
          _               => internal_error(__FILE__, __LINE__, "Widening op unexpected")
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

val process_rfvv_widening_reduction : (rfvvfunct6, bits(1), vregidx, vregidx, vregidx, nat1, sew_bitsize, range(-3, 3)) -> ExecutionResult
function process_rfvv_widening_reduction(funct6, vm, vs2, vs1, vd, num_elem_vs, SEW, LMUL_pow) = {
  let rm_3b          = fcsr[FRM];
  let SEW_widen      = SEW * 2;

  if illegal_fp_widening_reduction(SEW, rm_3b, SEW_widen) then return Illegal_Instruction();
  assert(SEW >= 16 & SEW_widen <= 64);

  let num_elem_vd = get_num_elem(0, SEW_widen); // vd regardless of LMUL setting

  if unsigned(vl) == 0 then return RETIRE_SUCCESS; // if vl=0, no operation is performed

  if SEW == 16 then {
    var sum : bits(32) = read_single_element(32, 0, vs1); // vs1 regardless of LMUL setting
    foreach (i from 0 to (num_elem_vs - 1)) {
      let active : bool = match is_active_vector_element(num_elem_vs, LMUL_pow, vm, i) {
        Ok(v)   => v,
        Err(()) => return Illegal_Instruction()
      };
      if active then {
        let elem : bits(16) = read_single_element(16, i, vs2);
        // currently ordered/unordered sum reductions do the same operations
        sum = fp_add(rm_3b, sum, fp_widen(elem))
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
        let elem : bits(32) = read_single_element(32, i, vs2);
        // currently ordered/unordered sum reductions do the same operations
        sum = fp_add(rm_3b, sum, fp_widen(elem))
      }
    };
    write_single_element(64, 0, vd, sum)
  };
  // other elements in vd are treated as tail elements, currently remain unchanged
  // TODO: configuration support for agnostic behavior
  set_vstart(zeros());
  RETIRE_SUCCESS
}

function clause execute(RFVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem_vs = get_num_elem(LMUL_pow, SEW);

  if funct6 == FVV_VFWREDOSUM | funct6 == FVV_VFWREDUSUM then
    process_rfvv_widening_reduction(funct6, vm, vs2, vs1, vd, num_elem_vs, SEW, LMUL_pow)
  else
    process_rfvv_single(funct6, vm, vs2, vs1, vd, num_elem_vs, SEW, LMUL_pow)
}

mapping rfvvtype_mnemonic : rfvvfunct6 <-> string = {
  FVV_VFREDOSUM   <-> "vfredosum.vs",
  FVV_VFREDUSUM   <-> "vfredusum.vs",
  FVV_VFREDMAX    <-> "vfredmax.vs",
  FVV_VFREDMIN    <-> "vfredmin.vs",
  FVV_VFWREDOSUM  <-> "vfwredosum.vs",
  FVV_VFWREDUSUM  <-> "vfwredusum.vs"
}

mapping clause assembly = RFVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> rfvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)
