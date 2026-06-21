// Termination measures for the pruned RV64IM Lean model.
//
// The upstream termination.sail also gives measures for compressed instruction
// constructors. Those constructors are intentionally absent from the pruned
// RV64IM instruction datatype, so this file keeps only the extension
// enablement measures needed by the minimal model.

function currentlyEnabled_measure(ext : extension) -> int =
  match ext {
    Ext_Zicsr => 0,
    Ext_A => 1,
    Ext_B => 1,
    Ext_C => 1,
    Ext_D => 1,
    Ext_F => 1,
    Ext_M => 1,
    Ext_S => 1,
    Ext_V => 1,
    Ext_H => 4,
    Ext_Smcntrpmf => 3,
    Ext_Zabha => 3,
    Ext_Zacas => 3,
    Ext_Zcb => 3,
    Ext_Zcd => 3,
    Ext_Zcf => 3,
    Ext_Zcmop => 3,
    Ext_Zfhmin => 3,
    Ext_Zhinx => 3,
    Ext_Zicfilp => 3,
    Ext_Zvkb => 3,
    Ext_Sscofpmf => 3,
    Ext_Svrsw60t59b => 3,
    Ext_Zhinxmin => 4,
    _ => 2
  }

termination_measure currentlyEnabled(ext) = currentlyEnabled_measure(ext)
termination_measure virtual_memory_supported(_) = 3

// get_xLPE() and currentlyEnabled() are mutually recursive:
// currentlyEnabled(Ext_Zicfilp) -> get_xLPE(_) -> currentlyEnabled(Ext_S).
termination_measure get_xLPE(_) = 2

function hartSupports_measure(ext : extension) -> int =
  match ext {
    Ext_D => 1,
    Ext_Zvkn => 1,
    Ext_Zvks => 1,
    Ext_C => 2,
    Ext_Zvknc => 2,
    Ext_Zvkng => 2,
    Ext_Zvksc => 2,
    Ext_Zvksg => 2,
    _ => 0,
  }

termination_measure hartSupports(ext) = hartSupports_measure(ext)
