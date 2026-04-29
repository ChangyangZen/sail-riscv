// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

function clause currentlyEnabled(Ext_Zvknha) = hartSupports(Ext_Zvknha) & currentlyEnabled(Ext_V)
function clause currentlyEnabled(Ext_Zvknhb) = hartSupports(Ext_Zvknhb) & currentlyEnabled(Ext_V)

union clause instruction = VSHA2MS_VV : (vregidx, vregidx, vregidx)

mapping clause encdec = VSHA2MS_VV(vs2, vs1, vd)
  <-> 0b1011011 @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b010 @ encdec_vreg(vd) @ 0b1110111
  when (currentlyEnabled(Ext_Zvknha) & get_sew() == 32) | (currentlyEnabled(Ext_Zvknhb) & (get_sew() == 32 | get_sew() == 64)) & zvknhab_check_encdec(vs2, vs1, vd)

mapping clause assembly = VSHA2MS_VV(vs2, vs1, vd)
  <-> "vsha2ms.vv" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1)

function clause execute (VSHA2MS_VV(vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  assert(SEW == 32 | SEW == 64);

  let eg_len   = (unsigned(vl) / 4);
  let eg_start = (unsigned(vstart) / 4);

  if SEW == 32 then {
    foreach (i from eg_start to (eg_len - 1)) {
      assert(i * 4 + 3 < num_elem);

      let w0  : bits(32) = read_single_element(32, i * 4 + 0, vd);
      let w1  : bits(32) = read_single_element(32, i * 4 + 1, vd);
      let w2  : bits(32) = read_single_element(32, i * 4 + 2, vd);
      let w3  : bits(32) = read_single_element(32, i * 4 + 3, vd);

      let w4  : bits(32) = read_single_element(32, i * 4 + 0, vs2);
      let w9  : bits(32) = read_single_element(32, i * 4 + 1, vs2);
      let w10 : bits(32) = read_single_element(32, i * 4 + 2, vs2);
      let w11 : bits(32) = read_single_element(32, i * 4 + 3, vs2);

      let w12 : bits(32) = read_single_element(32, i * 4 + 0, vs1);
      let w14 : bits(32) = read_single_element(32, i * 4 + 2, vs1);
      let w15 : bits(32) = read_single_element(32, i * 4 + 3, vs1);

      let w16 : bits(32) = zvk_sig1(w14, 32) + w9  + zvk_sig0(w1, 32) + w0;
      let w17 : bits(32) = zvk_sig1(w15, 32) + w10 + zvk_sig0(w2, 32) + w1;
      let w18 : bits(32) = zvk_sig1(w16, 32) + w11 + zvk_sig0(w3, 32) + w2;
      let w19 : bits(32) = zvk_sig1(w17, 32) + w12 + zvk_sig0(w4, 32) + w3;

      write_single_element(32, i * 4 + 0, vd, w16);
      write_single_element(32, i * 4 + 1, vd, w17);
      write_single_element(32, i * 4 + 2, vd, w18);
      write_single_element(32, i * 4 + 3, vd, w19);
    }
  } else {
    foreach (i from eg_start to (eg_len - 1)) {
      assert(i * 4 + 3 < num_elem);

      let w0  : bits(64) = read_single_element(64, i * 4 + 0, vd);
      let w1  : bits(64) = read_single_element(64, i * 4 + 1, vd);
      let w2  : bits(64) = read_single_element(64, i * 4 + 2, vd);
      let w3  : bits(64) = read_single_element(64, i * 4 + 3, vd);

      let w4  : bits(64) = read_single_element(64, i * 4 + 0, vs2);
      let w9  : bits(64) = read_single_element(64, i * 4 + 1, vs2);
      let w10 : bits(64) = read_single_element(64, i * 4 + 2, vs2);
      let w11 : bits(64) = read_single_element(64, i * 4 + 3, vs2);

      let w12 : bits(64) = read_single_element(64, i * 4 + 0, vs1);
      let w14 : bits(64) = read_single_element(64, i * 4 + 2, vs1);
      let w15 : bits(64) = read_single_element(64, i * 4 + 3, vs1);

      let w16 : bits(64) = zvk_sig1(w14, 64) + w9  + zvk_sig0(w1, 64) + w0;
      let w17 : bits(64) = zvk_sig1(w15, 64) + w10 + zvk_sig0(w2, 64) + w1;
      let w18 : bits(64) = zvk_sig1(w16, 64) + w11 + zvk_sig0(w3, 64) + w2;
      let w19 : bits(64) = zvk_sig1(w17, 64) + w12 + zvk_sig0(w4, 64) + w3;

      write_single_element(64, i * 4 + 0, vd, w16);
      write_single_element(64, i * 4 + 1, vd, w17);
      write_single_element(64, i * 4 + 2, vd, w18);
      write_single_element(64, i * 4 + 3, vd, w19);
    }
  };

  set_vstart(zeros());
  RETIRE_SUCCESS
}

union clause instruction = ZVKSHA2TYPE : (zvk_vsha2_funct6, vregidx, vregidx, vregidx)

mapping encdec_vsha2 : zvk_vsha2_funct6 <-> bits(6) = {
  ZVK_VSHA2CH_VV <-> 0b101110,
  ZVK_VSHA2CL_VV <-> 0b101111,
}

mapping clause encdec = ZVKSHA2TYPE(funct6, vs2, vs1, vd)
  <-> encdec_vsha2(funct6) @ 0b1 @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b010 @ encdec_vreg(vd) @ 0b1110111
  when (currentlyEnabled(Ext_Zvknha) & get_sew() == 32) | (currentlyEnabled(Ext_Zvknhb) & (get_sew() == 32 | get_sew() == 64)) & zvknhab_check_encdec(vs2, vs1, vd)

mapping vsha2_mnemonic : zvk_vsha2_funct6 <-> string = {
  ZVK_VSHA2CH_VV <-> "vsha2ch.vv",
  ZVK_VSHA2CL_VV <-> "vsha2cl.vv",
}

mapping clause assembly = ZVKSHA2TYPE(funct6, vs2, vs1, vd)
  <-> vsha2_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1)

function clause execute (ZVKSHA2TYPE(funct6, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  assert(SEW == 32 | SEW == 64);

  let eg_len   = (unsigned(vl) / 4);
  let eg_start = (unsigned(vstart) / 4);

  if SEW == 32 then {
    foreach (i from eg_start to (eg_len - 1)) {
      assert(i * 4 + 3 < num_elem);

      var f : bits(32) = read_single_element(32, i * 4 + 0, vs2);
      var e : bits(32) = read_single_element(32, i * 4 + 1, vs2);
      var b : bits(32) = read_single_element(32, i * 4 + 2, vs2);
      var a : bits(32) = read_single_element(32, i * 4 + 3, vs2);

      var h : bits(32) = read_single_element(32, i * 4 + 0, vd);
      var g : bits(32) = read_single_element(32, i * 4 + 1, vd);
      var d : bits(32) = read_single_element(32, i * 4 + 2, vd);
      var c : bits(32) = read_single_element(32, i * 4 + 3, vd);

      let w0 : bits(32) = if funct6 == ZVK_VSHA2CL_VV
                          then read_single_element(32, i * 4 + 0, vs1)
                          else read_single_element(32, i * 4 + 2, vs1);
      let w1 : bits(32) = if funct6 == ZVK_VSHA2CL_VV
                          then read_single_element(32, i * 4 + 1, vs1)
                          else read_single_element(32, i * 4 + 3, vs1);

      var T1 : bits(32) = h + zvk_sum1(e, 32) + zvk_ch(e, f, g) + w0;
      var T2 : bits(32) = zvk_sum0(a, 32) + zvk_maj(a, b, c);

      h  = g;
      g  = f;
      f  = e;
      e  = d + T1;
      d  = c;
      c  = b;
      b  = a;
      a  = T1 + T2;

      T1 = h + zvk_sum1(e, 32) + zvk_ch(e, f, g) + w1;
      T2 = zvk_sum0(a, 32) + zvk_maj(a, b, c);
      h  = g;
      g  = f;
      f  = e;
      e  = d + T1;
      d  = c;
      c  = b;
      b  = a;
      a  = T1 + T2;

      write_single_element(32, i * 4 + 0, vd, f);
      write_single_element(32, i * 4 + 1, vd, e);
      write_single_element(32, i * 4 + 2, vd, b);
      write_single_element(32, i * 4 + 3, vd, a);
    }
  } else {
    foreach (i from eg_start to (eg_len - 1)) {
      assert(i * 4 + 3 < num_elem);

      var f : bits(64) = read_single_element(64, i * 4 + 0, vs2);
      var e : bits(64) = read_single_element(64, i * 4 + 1, vs2);
      var b : bits(64) = read_single_element(64, i * 4 + 2, vs2);
      var a : bits(64) = read_single_element(64, i * 4 + 3, vs2);

      var h : bits(64) = read_single_element(64, i * 4 + 0, vd);
      var g : bits(64) = read_single_element(64, i * 4 + 1, vd);
      var d : bits(64) = read_single_element(64, i * 4 + 2, vd);
      var c : bits(64) = read_single_element(64, i * 4 + 3, vd);

      let w0 : bits(64) = if funct6 == ZVK_VSHA2CL_VV
                          then read_single_element(64, i * 4 + 0, vs1)
                          else read_single_element(64, i * 4 + 2, vs1);
      let w1 : bits(64) = if funct6 == ZVK_VSHA2CL_VV
                          then read_single_element(64, i * 4 + 1, vs1)
                          else read_single_element(64, i * 4 + 3, vs1);

      var T1 : bits(64) = h + zvk_sum1(e, 64) + zvk_ch(e, f, g) + w0;
      var T2 : bits(64) = zvk_sum0(a, 64) + zvk_maj(a, b, c);

      h  = g;
      g  = f;
      f  = e;
      e  = d + T1;
      d  = c;
      c  = b;
      b  = a;
      a  = T1 + T2;

      T1 = h + zvk_sum1(e, 64) + zvk_ch(e, f, g) + w1;
      T2 = zvk_sum0(a, 64) + zvk_maj(a, b, c);
      h  = g;
      g  = f;
      f  = e;
      e  = d + T1;
      d  = c;
      c  = b;
      b  = a;
      a  = T1 + T2;

      write_single_element(64, i * 4 + 0, vd, f);
      write_single_element(64, i * 4 + 1, vd, e);
      write_single_element(64, i * 4 + 2, vd, b);
      write_single_element(64, i * 4 + 3, vd, a);
    }
  };

  set_vstart(zeros());
  RETIRE_SUCCESS
}
