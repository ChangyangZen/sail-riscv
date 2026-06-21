# Theorem-Prover Generation Notes

This branch records theorem-prover generation flows for both the pruned RV64IM
proof model and the full all-module Lean RISC-V artifact.  The upstream build
system already contains the default Lean, Lem, and Isabelle generation rules in
`model/CMakeLists.txt`; this document records the branch-specific changes
needed to make the generated definitions usable for proof work.

## Existing Build-System Hooks

The shared CMake generation rules are in `model/CMakeLists.txt`.

- Lean generation is recorded in the `Lean` section, around the
  `lean_sail_common`, `lean_sail_default`, and `generated_lean_${arch}`
  targets.
- Lem generation is recorded in the `Lem` section, around the
  `generated_lem_${arch}` target.
- Isabelle generation is recorded in the `Isabelle` section, around the
  `generated_isabelle_${arch}` target.

The normal route to Isabelle is:

```text
Sail source + config
  -> sail --lem
  -> .lem files
  -> lem -isa
  -> Isabelle .thy files
```

The normal route to Lean is direct:

```text
Sail source + config
  -> sail --lean
  -> Lean package
  -> lake build
```

## Pruned RV64IM Scope

The proof-oriented model used here is RV64I plus the M extension.

Operationally, the generated `hartSupports` function supports only:

```text
Ext_M
```

Most other extension tags still exist in the generated `extension` datatype
because shared Sail code mentions them, but their `hartSupports` cases evaluate
to `false` for this configuration.

The generated instruction datatype is intentionally much smaller than the full
RISC-V model.  It contains:

- RV64I base integer constructors such as `UTYPE`, `JAL`, `JALR`, `BTYPE`,
  `ITYPE`, `SHIFTIOP`, `RTYPE`, `LOAD`, and `STORE`.
- RV64 word constructors such as `ADDIW`, `RTYPEW`, and `SHIFTIWOP`.
- system/control/reserved constructors such as `FENCE`, `FENCE_TSO`, `ECALL`,
  `MRET`, `SRET`, `EBREAK`, `WFI`, `SFENCE_VMA`, `FENCE_RESERVED`, and
  `FENCEI_RESERVED`.
- M-extension constructors such as `MUL`, `DIV`, `REM`, `MULW`, `DIVW`, and
  `REMW`.
- `ILLEGAL`.

It does not include vector, floating-point, compressed, atomic, or crypto
instruction constructors.

## Lean Generation Record

### Full All-Module RV64D/V/FP/Privileged Artifact

This branch now also records a full all-module Lean generation artifact, not
only the pruned RV64IM model.  The artifact is committed under the repository
so it can be reviewed and reused without re-running the Sail backend:

```text
generated/lean/full_rv64d_v256_e64/
```

The generated package is:

```text
generated/lean/full_rv64d_v256_e64/generated/sail_lean/Lean_RV64D_Full
```

The reproducible generation entry point is:

```text
scripts/generate_sail_full_lean.sh
```

It uses:

```text
Config:           generated/lean/full_rv64d_v256_e64/config/rv64d_v256_e64.json
Selected files:   generated/lean/full_rv64d_v256_e64/config/rv64d_full_selected_files.txt
Selected count:   140 Sail files
Generated modules: 123 Lean module files under LeanRV64DFull/
Lake jobs:        105
```

The command intentionally uses `--all-modules`, so the generated Lean source
contains the broad Sail-RISC-V source surface: base integer, M, A, F, D,
compressed-related code, vector, vector FP, vector crypto, bitmanip, Zicsr,
Zicbom/Zicbop/Zicboz, Zicfilp, Zicond, PMP, virtual memory/MMU, RVFI, and
platform support.  Runtime support is still governed by the generated config
and `hartSupports`; this artifact is a broad source translation, not a
minimal proof model.

Validation status:

```text
No generated `partial def` occurrences.
Build completed successfully (105 jobs).
Elapsed wall time: 9:12.61
Maximum resident set size: 2,939,308 KB
Largest late module: LeanRV64DFull.InstsEnd, 313 s
```

The successful build log is:

```text
generated/lean/full_rv64d_v256_e64/logs/lake_build_full_lean.log
```

The build used the project-local Lean/Elan installation:

```bash
ELAN_HOME=<project>/sail-lean-termination-fix-20260619/elan_home \
TMPDIR=generated/lean/full_rv64d_v256_e64/runtime_tmp \
TMP=generated/lean/full_rv64d_v256_e64/runtime_tmp \
TEMP=generated/lean/full_rv64d_v256_e64/runtime_tmp \
lake build
```

Do not use `/tmp` for these builds; keep runtime files under the artifact
directory.

### Pruned RV64IM Artifact

The successful Lean artifact was generated from this branch using a patched
Sail Lean backend.  The generated package was:

```text
isa-artifacts-lean/rv64im_min_lean_termination_fix_20260619/generated/sail_lean/Lean_RV64IM_Min
```

The generation script used for the artifact was:

```text
isa-artifacts-lean/rv64im_min_lean_termination_fix_20260619/scripts/generate_sail_rv64im_lean_no_partial.sh
```

The generated Lean model built successfully with:

```text
Build completed successfully (63 jobs).
```

Important generated properties:

- No generated `partial def` remains in the RV64IM package.
- `currentlyEnabled` and `get_xLPE` are generated as total mutually recursive
  definitions with `termination_by` and `decreasing_by`.
- `hartSupports` is also generated with a checked termination proof.

The Lean command follows the same shape as the CMake Lean generation rule:

```bash
sail \
  --lean \
  --memo-z3 \
  --lean-output-dir <out-dir> \
  --lean-force-output \
  --lean-non-beq-type instruction \
  --lean-noncomputable \
  --lean-noncomputable-function encdec_forwards \
  --lean-noncomputable-function encdec_backwards \
  --lean-noncomputable-function encdec_forwards_matches \
  --lean-noncomputable-function encdec_backwards_matches \
  --lean-noncomputable-function encdec_compressed_forwards \
  --lean-noncomputable-function encdec_compressed_backwards \
  --lean-noncomputable-function encdec_compressed_forwards_matches \
  --lean-noncomputable-function encdec_compressed_backwards_matches \
  --lean-import-file ../handwritten_support/RiscvExtras.lean \
  -o Lean_RV64IM_Min \
  --variable "TERMINATION_FILE = true" \
  <selected RV64IM Sail files>
```

For local runs, use a project-local Lean/Elan and temporary directory.  Do not
use `/tmp` for long prover builds.

Example:

```bash
ELAN_HOME=<project>/elan_home \
TMPDIR=<artifact>/runtime_tmp \
TMP=<artifact>/runtime_tmp \
TEMP=<artifact>/runtime_tmp \
lake build
```

## Lean-Specific Fixes

The main Lean generation blocker was termination.  Sail already contains
`termination_measure` declarations, but the Lean backend did not emit enough
Lean termination information for the mutually recursive extension-enablement
functions.

The patched Lean backend should emit definitions of the following shape:

```lean
mutual
  def currentlyEnabled (merge_var : extension) : SailM Bool := do
    ...
  termination_by (currentlyEnabled_measure merge_var).toNat
  decreasing_by
    all_goals
      simp_wf
      try unfold Nat.toNat at *
      try simp [currentlyEnabled_measure] at *
      try omega

  def get_xLPE (p : Privilege) : SailM Bool := do
    ...
  termination_by (2).toNat
  decreasing_by
    all_goals
      simp_wf
      try unfold Nat.toNat at *
      try simp [currentlyEnabled_measure] at *
      try omega
end
```

Backend-side requirements:

- Preserve Sail `termination_measure` declarations.
- Substitute measure binders into the final generated Lean function parameters.
- Emit direct `termination_by` clauses instead of destructuring generated
  argument tuples in the measure expression.
- Emit robust `decreasing_by` proofs using `simp_wf`, explicit unfolding of
  the generated `Nat.toNat` identity abbreviation when needed, the relevant
  measure helper definitions, and `omega`.
- Avoid adding unrelated measure helpers to a local `simp` set.

This branch also adds a pruned termination file:

```text
model/termination/termination_rv64im_min.sail
```

The full upstream `model/termination/termination.sail` contains compressed
instruction termination clauses.  Those clauses mention compressed constructors
that are intentionally absent from the pruned RV64IM instruction datatype, so
the full termination file is not suitable for this pruned model.

The Lean handwritten support files also required updates:

- Remove the invalid top-level `variable [Arch]`.
- Put platform and reservation symbols under `Sail.ConcurrencyInterfaceV1`.
- Use `extension.ctorIdx` instead of deprecated `extension.toCtorIdx`.

## Isabelle Generation Record

The Isabelle generation route is recorded in `model/CMakeLists.txt`, around
the `generated_lem_${arch}` and `generated_isabelle_${arch}` targets.  The
default route is:

```text
Sail source + config
  -> sail --lem
  -> .lem files
  -> lem -isa
  -> Isabelle .thy files
```

The successful proof-oriented artifact is the pruned RV64IM mwords heap:

```text
Session: Sail-Rv64IM-Core-Pruned-IsoHome
Heap:    $project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/isabelle_home_isolated/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/Sail-Rv64IM-Core-Pruned-IsoHome
Size:    247 MB
Status:  isabelle build exited 0
```

The final build uses Isabelle2025-2, Poly/ML 5.9.2, `--lem-mwords`,
an RV64I+M-only Sail input set, conservative generated-file pruning, and an
isolated Isabelle `HOME` to avoid an Isabelle2025-2 presentation/source-path
bug.

### Final Artifact Layout

```text
$project/isa-artifacts-mwords/
|-- test_rv64im_core_pruned_mwords/
|   |-- config/rv64im.json
|   |-- lem_out/{rv64im.lem,rv64im_types.lem}
|   |-- isabelle/rv64im/
|   |-- logs/
|   `-- prune_unused_generated.py
`-- test_rv64im_core_pruned_isohome_20260430/
    |-- isabelle/rv64im/
    |-- isabelle_home_isolated/
    |-- logs/
    |-- run_isohome_build.sh
    `-- RV64IM_MWORDS_ISABELLE_REPRODUCIBILITY.md
```

The first tree records generation and pruning.  The second tree is the final
clean build tree with the formal session:

```isabelle
session "Sail-Rv64IM-Core-Pruned-IsoHome" = "Sail" +
```

### Problem Summary

The original full `Sail-Rv64d` Isabelle build was not practical:

- The generated full model included a very large instruction datatype and broad
  RV64D/V/FP/platform state.
- The old bitvector representation used many `bitU list` values, which made
  generated definitions and datatype lemmas expensive.
- Poly/ML memory consumption grew to hundreds of GB in the full build path.
- Even after reducing the target to RV64IM, final `isabelle build`
  presentation failed once due to a source-name mismatch between
  `~/projects/...` and `$project/...`.

The effective fix was a pipeline:

1. Fix Sail/Lem mwords generation so generated Isabelle uses
   `Word.word`/mword datatypes instead of list-of-bits for machine words.
2. Generate a small RV64I+M Sail model instead of the full all-extension model.
3. Conservatively prune unused generated type synonyms and patch a few
   proof-irrelevant or generated helpers that were bad for Isabelle.
4. Build under an isolated `HOME` outside the source tree so Isabelle stores
   session-source paths consistently.

### Sail/Lem Backend Work: Use mwords, Not `bitU list`

The important rule was:

```text
Do not generate Isabelle-facing dynamic bitvector values as bitU list.
Use --lem-mwords and concrete mword/Word.word widths.
```

The relevant Sail backend checkout was:

```text
$project/sail-clean
```

Modified backend/support files there:

```text
lib/hex_bits_signed.sail
lib/isabelle/Add_Cancel_Distinct.thy
lib/isabelle/Sail2_monadic_combinators_lemmas.thy
lib/isabelle/Sail2_operators_mwords_lemmas.thy
lib/isabelle/Sail2_values_lemmas.thy
src/sail_lem_backend/pretty_print_lem.ml
```

The largest patch was `src/sail_lem_backend/pretty_print_lem.ml`.  It added
the mwords-specific Lem pretty-printing support needed by this RISC-V model:

- Emit `mword tyN` / Isabelle `N Word.word` instead of bit-list vectors.
- Add missing `Size` instances needed by generated wide word types.
- Avoid unresolved `Machine_word.Size 'a` constraints in generated Lem for
  common bitvector operations.
- Special-case problematic generated helpers such as print/parse/cast/
  softfloat and some memory/TLB helpers where dynamic widths used to leak into
  Lem.
- Keep concrete widths at the Lem/Isabelle boundary wherever possible.

Useful audit command:

```bash
git -C $project/sail-clean diff --stat
```

Expected summary from the working artifact:

```text
src/sail_lem_backend/pretty_print_lem.ml          | 906 +++++++++++++++++++++-
6 files changed, 892 insertions(+), 29 deletions(-)
```

This mattered because the old generation produced many bit-list operations.
Those are expensive for Isabelle because bitvector operations expand over a
list representation.  The successful artifacts use concrete words such as:

```isabelle
32 Word.word
64 Word.word
```

The remaining `bitU` use is mostly for actual single bits, not full
machine-word data.

### Avoid the Full RISC-V Model: Generate RV64I + M Only

The full Sail-RISC-V project still declares many extension families and state
components even if disabled by config.  For base integer/M-extension proof
targets, the Isabelle heap did not need:

```text
F/D floating-point instruction constructors
V/vector registers and vector instruction constructors
vector_crypto/Zv* constructors
A/atomics when proving only RV64I+M
compressed C constructors if C is disabled
RVFI theorem output and large RVFI packet datatypes
```

The effective approach was to create a small Sail project/file set in:

```text
$project/sail-riscv-clean/model
```

RV64IM-minimal files:

```text
model/core/regs_rv64im_min.sail
model/core/types_rv64im_min.sail
model/postlude/decode_ext_rv64im_min.sail
model/postlude/fetch_rv64im_min.sail
model/postlude/insts_end_rv64im_min.sail
model/postlude/step_common_rv64im_min.sail
model/postlude/step_rv64im_min.sail
model/rv64im_min.sail_project
model/sys/insts_begin_rv64im_min.sail
model/sys/sys_control_rv64im_min.sail
```

The exact effective file list is recorded in the artifact:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords/logs/rv64im_selected_files.txt
```

It includes the common core, memory/platform/CSR basics, base I instructions,
M extension instructions, and minimal postlude/decode/fetch/step files.  It
does not include V, FP, vector_crypto, or full all-extension decode machinery.

The RV64IM config is:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords/config/rv64im.json
```

Key extension settings:

```json
"M": { "supported": true },
"A": { "supported": false },
"F": { "supported": false },
"D": { "supported": false },
"V": { "supported": false },
"B": { "supported": false }
```

### Resulting Instruction Datatype

The final generated instruction datatype starts at `Rv64im_types.thy:371`.
It contains RV64I/system forms plus M-extension forms:

```isabelle
datatype instruction =
    ILLEGAL "32 Word.word"
  | LPAD "20 Word.word"
  | UTYPE ...
  | JAL ...
  | JALR ...
  | BTYPE ...
  | ITYPE ...
  | SHIFTIOP ...
  | RTYPE ...
  | LOAD ...
  | STORE ...
  | ADDIW ...
  | RTYPEW ...
  | SHIFTIWOP ...
  | FENCE ...
  | FENCE_TSO ...
  | ECALL
  | MRET
  | SRET
  | EBREAK
  | WFI
  | SFENCE_VMA
  | FENCE_RESERVED ...
  | FENCEI_RESERVED ...
  | MUL
  | DIV
  | REM
  | MULW
  | DIVW
  | REMW
```

There are no `V*`, `FVV*`, `FVF*`, `VLSEG*`, `VAES*`, etc. constructors.

The final generated `regstate` is still not a mathematically minimal CPU state.
It keeps platform/CSR/PMP/TLB fields required by the selected shared model
files, but it is much smaller than the original full RV64D/V state:

```bash
grep -c '^definition.*_ref ' \
  $project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/isabelle/rv64im/Rv64im_types.thy
```

Current result:

```text
90
```

The original full RV64D path had 168 register refs, including FP/vector state.
This pruned RV64IM heap avoids vector registers and large FP/vector
instruction families.

### Generate Lem and Isabelle with mwords

Artifact variables:

```bash
project=<workspace root>
ART=$project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords
MODEL=$project/sail-riscv-clean/model
SAIL=$project/sail-clean/sail
```

Important flags:

```text
--lem
--lem-mwords
--strict-var
--strict-bitvector
--strict-exponentials
```

Generation command shape:

```bash
cd "$MODEL"
SAIL_FILES=$(cat "$ART/logs/rv64im_selected_files.txt")

"$SAIL" \
  --strict-var \
  --strict-bitvector \
  --strict-exponentials \
  --lem \
  --lem-mwords \
  --lem-lib Riscv_extras \
  --lem-lib Riscv_extras_fdext \
  --lem-output-dir "$ART/lem_out" \
  --isa-output-dir "$ART/isabelle/rv64im" \
  -o rv64im \
  --config "$ART/config/rv64im.json" \
  $SAIL_FILES \
  > "$ART/logs/rv64im_sail_lem_mwords.log" 2>&1
```

Observed Sail warnings in the current log were non-fatal initial-state
evaluation warnings:

```text
Warning: Incomplete pattern match statement at extensions/M/mext_insts.sail
Warning: Unable to evaluate initial state, using default values only
Failure("run_frame got Fail: ...")
Warning: Unable to evaluate initial state, using default values only
Failure("run_frame got Fail: Fundef not found: legalize_senvcfg")
```

Then convert Lem to Isabelle:

```bash
cd "$ART/lem_out"

~/.opam/sail-lem/bin/lem \
  -no_lifting_toplevel_match_for Rv64im_types.ast \
  -wl ign \
  -isa \
  -outdir "$ART/isabelle/rv64im" \
  -lib Sail=$project/sail-clean/src/gen_lib \
  $project/sail-riscv-clean/handwritten_support/riscv_extras.lem \
  $project/sail-riscv-clean/handwritten_support/riscv_extras_fdext.lem \
  rv64im_types.lem rv64im.lem \
  > "$ART/logs/rv64im_lem_to_isa_mwords.log" 2>&1
```

The successful `rv64im_lem_to_isa_mwords.log` was empty, meaning Lem produced
no diagnostic output.

### Conservative Generated-File Pruning

Post-generation pruning was intentionally conservative.  Do not delete
generated datatypes or state fields merely because they look irrelevant.  The
script only removes names that occur exactly once across the generated files.

Script:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords/prune_unused_generated.py
```

Run:

```bash
cd $project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords
python3 prune_unused_generated.py > logs/prune_unused_generated.log
```

Current output:

```text
Pruned Isabelle synonyms: bits_rm, bits_fflags, bits_BF16, bits_H, bits_S, bits_D, bits_W, bits_WU, bits_L, bits_LU
Pruned Lem synonyms: bits_rm, bits_fflags, bits_BF16, bits_H, bits_S, bits_D, bits_W, bits_WU, bits_L, bits_LU
Removed 10 Isabelle lines and 10 Lem lines
Referenced symbols left intact:
  Ext_V: 9
  Ext_F: 12
  Ext_D: 8
  TLB_Entry: 61
  satp: 9
  pmpaddr_n: 5
  C_ILLEGAL: 0
  cregidx: 0
  F_RVC: 0
  RISCV_strong_access: 739
```

This means extension enum constructors and platform/TLB/PMP fields were left
alone when still referenced.

### Generated Isabelle Patches That Made the Heap Build

Several generated Isabelle definitions were patched because they were either
proof-irrelevant, recursively generated in a way Isabelle did not like, or
unnecessarily pulled in dynamic-width behavior.  The current patched examples
are in:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/isabelle/rv64im/Rv64im.thy
```

Printing is irrelevant for ISA theorem semantics.  The generated `print_bits0`
was specialized/stubbed:

```isabelle
definition print_bits0 :: "string \<Rightarrow> bitU list \<Rightarrow> unit" where
  "print_bits0 _ _ = ()"
```

This avoids dictionary/typeclass trouble from generated print helpers.

`n_leading_spaces0` was converted from a recursive function into a simple
definition:

```isabelle
definition n_leading_spaces0 :: "string \<Rightarrow> int" where
  "n_leading_spaces0 _ = ((0 :: int)::ii)"
```

This is acceptable for the current proof-oriented target because assembly
pretty-print parsing is not part of the theorem path.

The target supports M and leaves everything else disabled:

```isabelle
definition hartSupports :: "extension \<Rightarrow> bool" where
  "hartSupports ext = (case ext of Ext_M \<Rightarrow> True | _ \<Rightarrow> False)"
```

Then `currentlyEnabled` becomes a monadic wrapper:

```isabelle
definition currentlyEnabled :: "extension \<Rightarrow> ... monad" where
  "currentlyEnabled ext = return (hartSupports ext)"
```

The generated model referenced `legalize_*` helpers that were not useful for
the RV64IM proof target.  They were made identity functions:

```isabelle
definition legalize_menvcfg :: "... " where
  "legalize_menvcfg _ v = return v"

definition legalize_mseccfg :: "... " where
  "legalize_mseccfg _ v = return v"

definition legalize_senvcfg :: "... " where
  "legalize_senvcfg _ v = return v"
```

`read_ram` and `write_ram` were changed from generated `fun` equations with
constructor patterns on the left-hand side into definitions that case-split on
the `physaddr`.  This avoids fragile function package behavior.

`pt_walk` was stubbed for the current machine-mode/bare RV64IM theorem target:

```isabelle
definition pt_walk :: "... " where
  "pt_walk sv_width vpn ac priv mxr do_sum pt_base level global1 ext_ptw =
     return (Err (PTW_Invalid_PTE (), ext_ptw))"
```

If future proofs require S-mode virtual memory semantics, this stub must be
replaced by a real generated or hand-verified page-table walk.

`Rv64imAuxiliary.thy` was simplified because several formerly recursive
generated helpers became definitions.  Old termination-proof commands were
removed.  The current file is:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/isabelle/rv64im/Rv64imAuxiliary.thy
```

Line count:

```text
30
```

### Isabelle Session ROOT

Final ROOT:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/isabelle/rv64im/ROOT
```

Contents:

```isabelle
session "Sail-Rv64IM-Core-Pruned-IsoHome" = "Sail" +
  options [document = false, browser_info = false]
  theories
    Riscv_extras
    Riscv_extras_fdext
    Rv64im_types
    Rv64im
    Rv64imAuxiliary
    Rv64im_lemmas
```

### Isabelle2025-2 Presentation/Source-Path Bug

The earlier non-isolated build completed the heap but failed in final
presentation:

```text
Finished Sail-Rv64IM-Core-Pruned (0:06:30 elapsed time, 0:13:06 cpu time, factor 2.01)
*** Missing session source file "$project/afp/thys/Word_Lib/Enumeration.thy"
```

The reported file existed, was readable from Isabelle/Scala, and was present in
the parent `Word_Lib` session database.  The failure was caused by exact string
lookup of session-source names: the database stored the file as:

```text
~/projects/afp/thys/Word_Lib/Enumeration.thy
```

but presentation requested:

```text
$project/afp/thys/Word_Lib/Enumeration.thy
```

Relevant environment:

```text
Isabelle version: Isabelle2025-2
ISABELLE_HOME=$project/.local/Isabelle2025-2
ISABELLE_HOME_USER=<home>/.isabelle/Isabelle2025-2
ML_SYSTEM=polyml-5.9.2
```

Path aliasing on this machine:

```text
readlink -f ~/projects
$project
```

No AFP component was globally registered:

```bash
PATH=<home>/.local/Isabelle2025-2/bin:$PATH isabelle components -l | grep -i afp
# no output
```

Reproduction command:

```bash
PATH=<home>/.local/Isabelle2025-2/bin:$PATH \
isabelle build -b -v \
  -o document=false \
  -o browser_info=false \
  -d ~/projects/afp/thys/Word_Lib \
  -d ~/.opam/sail-lem/share/lem/isabelle-lib \
  -d ~/projects/sail-clean/lib/isabelle \
  -d $project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords/isabelle/rv64im \
  Sail-Rv64IM-Core-Pruned \
  > $project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords/logs/sail_rv64im_core_pruned_build_retry16.log 2>&1
```

Relevant log excerpt:

```text
216:Finished Sail-Rv64IM-Core-Pruned (0:06:30 elapsed time, 0:13:06 cpu time, factor 2.01)
228:*** Missing session source file "$project/afp/thys/Word_Lib/Enumeration.thy"
```

The target heap and database were written:

```text
<home>/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/Sail-Rv64IM-Core-Pruned 247M
<home>/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/log/Sail-Rv64IM-Core-Pruned.db 2.4M
```

The heap loaded successfully:

```bash
PATH=<home>/.local/Isabelle2025-2/bin:$PATH \
isabelle ML_process \
  -d ~/projects/afp/thys/Word_Lib \
  -d <home>/.opam/sail-lem/share/lem/isabelle-lib \
  -d <project>/sail-clean/lib/isabelle \
  -d $project/isa-artifacts-mwords/test_rv64im_core_pruned_mwords/isabelle/rv64im \
  -l Sail-Rv64IM-Core-Pruned \
  -e 'writeln "heap loaded"'
```

Output:

```text
heap loaded
val it = (): unit
```

Isabelle/Scala could read the exact reported path:

```bash
PATH=<home>/.local/Isabelle2025-2/bin:$PATH \
isabelle scala -e '{
  val p = java.nio.file.Paths.get("$project/afp/thys/Word_Lib/Enumeration.thy")
  println("exists=" + java.nio.file.Files.exists(p))
  println("readable=" + java.nio.file.Files.isReadable(p))
  if (java.nio.file.Files.exists(p)) println("real=" + p.toRealPath())
}'
```

Output:

```text
exists=true
readable=true
real=$project/afp/thys/Word_Lib/Enumeration.thy
```

The parent `Word_Lib` DB contained the source file body:

```bash
sqlite3 <home>/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/log/Word_Lib.db \
  "select session_name, name, digest, compressed, length(body)
   from isabelle_sources
   where name like '%Enumeration.thy%';"
```

Output:

```text
Word_Lib|~/projects/afp/thys/Word_Lib/Enumeration.thy|ef646f0ad2417864fe00a8180e84abeb2b7613f8|1|3137
```

Exact key mismatch:

```bash
sqlite3 <home>/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/log/Word_Lib.db \
  "select count(*) from isabelle_sources
   where session_name='Word_Lib'
     and name='$project/afp/thys/Word_Lib/Enumeration.thy';
   select count(*) from isabelle_sources
   where session_name='Word_Lib'
     and name='~/projects/afp/thys/Word_Lib/Enumeration.thy';"
```

Output:

```text
0
1
```

Local Isabelle source-code analysis:

- `src/Pure/Build/export.scala` presentation obtains sources by exact DB
  lookup via `store.read_sources(database.db, database.session, name = name)`.
- `src/Pure/Build/store.scala` stores sources using `File.symbolic_path(path)`.
- Sources are read back using exact SQL equality on `session_name` and `name`.

This explains the failure: the DB stored `~/projects/...`, but presentation
requested `$project/...`.  These spellings denote the same real file on this
system, but exact SQL lookup failed.

Conclusion: this was a presentation/export path canonicalization issue in
Isabelle2025-2, not a missing AFP file, not a corrupt `Word_Lib` heap, and not
a failed target theory.

Suggested upstream fix direction: normalize source names consistently at both
write and read sites, or make presentation source lookup try equivalent
symbolic/absolute names when direct lookup fails.

### Isolated HOME Workaround

Effective workaround: build with `HOME` set to an isolated directory that is not
a prefix of the source tree:

```text
HOME=$ART/isabelle_home_isolated
```

This forces Isabelle to store source paths as absolute `$project/...` paths,
not `~/projects/...`.

Verification:

```bash
sqlite3 \
  $project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/isabelle_home_isolated/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/log/Word_Lib.db \
  "select session_name, name, compressed, length(body)
   from isabelle_sources
   where name like '%Enumeration.thy%';"
```

Expected:

```text
Word_Lib|$project/afp/thys/Word_Lib/Enumeration.thy|1|3137
```

### Final Build Command

Use the checked-in runner:

```bash
cd $project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430
./run_isohome_build.sh
```

Runner:

```text
$project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430/run_isohome_build.sh
```

Important settings:

```bash
ART=$project/isa-artifacts-mwords/test_rv64im_core_pruned_isohome_20260430
ISO_HOME="$ART/isabelle_home_isolated"
SESSION=Sail-Rv64IM-Core-Pruned-IsoHome

HOME="$ISO_HOME" \
PATH=<home>/.local/Isabelle2025-2/bin:$PATH \
isabelle build -b -v \
  -o ML_system_64=true \
  -o document=false \
  -o browser_info=false \
  -d $project/afp/thys/Word_Lib \
  -d ~/.opam/sail-lem/share/lem/isabelle-lib \
  -d ~/projects/sail-clean/lib/isabelle \
  -d "$ART/isabelle/rv64im" \
  "$SESSION"
```

The final rerun completed with exit code 0:

```text
Finished at Thu Apr 30 15:11:05 GMT-7 2026
0:00:08 elapsed time
```

The first isolated run rebuilt all parent heaps and then the target heap.  The
second run was fast because everything was already present in the isolated
`ISABELLE_HOME_USER`.

### Build Timing and Heap Sizes

Useful target build timings from the non-isolated retry logs:

```text
Timing LEM (8 threads, 22.836s elapsed time, 115.165s cpu time, 13.246s GC time, factor 5.04)
Finished LEM (0:00:38 elapsed time, 0:02:27 cpu time, factor 3.80)

Timing Sail (8 threads, 63.536s elapsed time, 262.063s cpu time, 37.651s GC time, factor 4.12)
Finished Sail (0:01:39 elapsed time, 0:05:41 cpu time, factor 3.44)

Timing Sail-Rv64IM-Core-Pruned (8 threads, 363.880s elapsed time, 729.225s cpu time, 117.164s GC time, factor 2.00)
Finished Sail-Rv64IM-Core-Pruned (0:06:30 elapsed time, 0:13:06 cpu time, factor 2.01)
```

Other useful target-session timings:

```text
retry13: Finished Sail-Rv64IM-Core-Pruned (0:06:38 elapsed time, 0:13:09 cpu time, factor 1.98)
retry14: Finished Sail-Rv64IM-Core-Pruned (0:06:15 elapsed time, 0:12:46 cpu time, factor 2.04)
```

Final isolated heap files:

```text
Pure                                  31M
HOL                                  334M
Word_Lib                              71M
LEM                                   72M
Sail                                 153M
Sail-Rv64IM-Core-Pruned-IsoHome      247M
```

Generated theory sizes:

```text
    371 Riscv_extras_fdext.thy
    123 Riscv_extras.thy
     30 Rv64imAuxiliary.thy
    206 Rv64im_lemmas.thy
  30219 Rv64im.thy
   2093 Rv64im_types.thy
  33042 total
```

### Isabelle/PolyML Sandbox Caveat

Known Isabelle/PolyML caveat:

```text
I/O error: Operation not permitted
```

Treat this as a sandbox/filesystem issue unless the Isabelle log reports a real
theory, type, or proof error.  Rerun with a project-local isolated `HOME`,
project-local `TMPDIR`, and, when heap writes are required, outside the normal
sandbox.

Example pattern:

```bash
HOME=<artifact>/isabelle_home_isolated \
TMPDIR=<artifact>/runtime_tmp \
TMP=<artifact>/runtime_tmp \
TEMP=<artifact>/runtime_tmp \
isabelle build \
  -o document=false \
  -o browser_info=false \
  -d <AFP Word_Lib path> \
  -d <sail-lem Isabelle library path> \
  -d <sail-clean Isabelle library path> \
  -d <generated rv64im Isabelle path> \
  Sail-Rv64IM-Core-Pruned-IsoHome
```

### Practical Lessons

- `--lem-mwords` is required but not sufficient.  The backend also needs to
  avoid dynamic-width `mword 'a` leaks that Lem cannot solve.
- Do not build the full Sail-RISC-V all-extension model if the theorem only
  concerns RV64I/M instructions.
- Prune at the Sail project/file-list level first.  Generated `.thy` pruning
  should be conservative and name-count based.
- Proof-irrelevant generated helpers such as printing can be stubbed to avoid
  typeclass/dictionary noise.
- Do not manually delete generated datatypes/state fields unless exact grep
  proves they are unused.
- Isabelle's heap can be valid even when final presentation fails; verify with
  `ML_process -l SESSION`.
- For reproducible batch builds on this filesystem, prefer an isolated
  project-local `HOME` outside the source tree.

### Known Limitations

- The RV64IM model still contains some privileged/platform/PMP/TLB support
  because shared memory and CSR files require them.
- `pt_walk` is stubbed for the current bare/machine-mode proof target.  Do not
  use this heap as a complete S-mode virtual-memory theorem model without
  restoring real page-table-walk semantics.
- `hartSupports` intentionally only enables `Ext_M`; other extension checks
  return false.
- Initial-state evaluation warnings from Sail generation are still present but
  non-blocking.
- The final generated Isabelle patches are currently post-generation edits.
  For long-term maintenance, move more of these decisions into the Sail backend
  or a deterministic post-generation patch script.

## Datatype Assessment

For Lean, the current datatypes are usable for RV64IM proof work:

- `xlenbits` is `BitVec 64`.
- `regtype` is `xlenbits`.
- `regidx` wraps a 5-bit `BitVec`, matching hardware register encoding.
- instructions are represented by a pruned inductive datatype.
- registers are represented by a dependent mapping
  `RegisterType : Register -> Type`, which avoids the large dynamic
  `register_value` conversion layer used by the Lem/Isabelle route.

Tradeoffs:

- Tuple payload constructors are less ergonomic than named constructor fields
  for proof scripts.
- `regidx` as `BitVec 5` is hardware-faithful, but proof abstractions may want
  helper lemmas relating it to `Fin 32`.
- The generated `Register` datatype still includes CSR, PMP, TLB, platform, and
  trap state.  For hardware refinement, use a smaller architectural projection
  rather than exposing every generated register directly.

Compared with Isabelle:

- Lean now has a cleaner dependent register typing story.
- Isabelle already has more local proof scaffolding in this project, but needed
  more pruning, mword/static-word work, AFP/session care, and heap-management
  discipline.
- Lean required stronger totality work up front, but after the termination fix
  the pruned RV64IM package builds directly with Lake.

## Files To Commit For This Branch

Commit these Sail-RISC-V files:

```text
doc/TheoremProverGeneration.md
README.md
handwritten_support/RiscvExtras.lean
handwritten_support/RiscvExtrasExecutable.lean
model/termination/termination_rv64im_min.sail
scripts/generate_sail_full_lean.sh
generated/lean/full_rv64d_v256_e64/
```

The Sail compiler backend fix is in a different repository and should be
committed separately:

```text
<sail-root>/src/sail_lean_backend/pretty_print_lean.ml
<sail-root>/src/sail_lean_backend/dune
<sail-root>/src/sail_lean_backend/Sail/Sail.lean
```

Do not commit unrelated external artifact directories from:

```text
isa-artifacts-lean/
isa-artifacts-mwords/
```

Those are reproducibility artifacts outside this repository, not source changes
for this branch.  The committed full Lean artifact under `generated/lean/` is
intentional for this branch.
