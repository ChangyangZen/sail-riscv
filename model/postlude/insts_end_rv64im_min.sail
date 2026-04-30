// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// Put the illegal instructions last to use their wildcard match.

// *****************************************************************

mapping clause encdec = ILLEGAL(s) <-> s

function clause execute (ILLEGAL(s)) = Illegal_Instruction()

mapping clause assembly = ILLEGAL(s) <-> "illegal" ^ spc() ^ hex_bits_32(s)

// End definitions
end extension
end extensionName
end hartSupports
end currentlyEnabled
end instruction
end execute
end assembly
end encdec

val print_insn : instruction -> string
function print_insn insn = assembly(insn)

overload to_str = {print_insn}
