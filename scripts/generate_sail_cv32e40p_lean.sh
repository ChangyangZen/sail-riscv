#!/usr/bin/env bash
set -euo pipefail

REPO="${SAIL_RISCV:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
SAIL_ROOT="${SAIL_ROOT:-$HOME/projects/sail-0.20.1-bench}"
SAIL_BIN="${SAIL_BIN:-$SAIL_ROOT/_build/default/src/bin/sail.exe}"
SAIL_LEAN_PLUGIN="${SAIL_LEAN_PLUGIN:-$SAIL_ROOT/_build/default/src/sail_lean_backend/sail_plugin_lean.cmxs}"

ART="${ART:-$REPO/generated/lean/cv32e40p_rv32imc}"
CONFIG="${CONFIG:-$ART/config/cv32e40p_rv32imc.json}"
OUT_ROOT="${OUT_ROOT:-$ART/generated/sail_lean}"
OUT_MODEL="${OUT_MODEL:-Lean_CV32E40P_RV32IMC}"
LOG="$ART/logs/generate_sail_cv32e40p_lean.log"
SELECTED_FILES="$ART/config/selected_files.txt"
RUNTIME_TMP="$ART/runtime_tmp"
SMT_CACHE="$ART/sail_smt_cache.db"

MODULES=(
  I_insts
  M_insts
  Zicsr_insts
  Zicntr
  Zifenci
  Zca
  postlude
  main
)

mkdir -p "$ART/config" "$ART/logs" "$OUT_ROOT" "$RUNTIME_TMP"

if [[ ! -f "$CONFIG" ]]; then
  echo "Missing config: $CONFIG" >&2
  exit 2
fi

if [[ ! -x "$SAIL_BIN" ]]; then
  echo "Missing Sail binary: $SAIL_BIN" >&2
  exit 2
fi

if [[ ! -f "$SAIL_LEAN_PLUGIN" ]]; then
  echo "Missing Lean backend plugin: $SAIL_LEAN_PLUGIN" >&2
  exit 2
fi

{
  echo "artifact=$ART"
  echo "repo=$REPO"
  echo "sail_root=$SAIL_ROOT"
  echo "sail_bin=$SAIL_BIN"
  echo "sail_lean_plugin=$SAIL_LEAN_PLUGIN"
  SAIL_DIR="$SAIL_ROOT" "$SAIL_BIN" --version
  echo "config=$CONFIG"
  echo "out_root=$OUT_ROOT"
  echo "out_model=$OUT_MODEL"
  echo "modules=${MODULES[*]}"
  echo

  cd "$REPO"

  SAIL_DIR="$SAIL_ROOT" \
  TMPDIR="$RUNTIME_TMP" TMP="$RUNTIME_TMP" TEMP="$RUNTIME_TMP" \
  "$SAIL_BIN" \
    --strict-var \
    --strict-bitvector \
    --strict-exponentials \
    --require-version 0.19 \
    --config "$CONFIG" \
    --memo-z3-path "$SMT_CACHE" \
    model/riscv.sail_project \
    --variable "TERMINATION_FILE = true" \
    "${MODULES[@]}" \
    --list-files \
    > "$SELECTED_FILES"

  echo "selected_files=$SELECTED_FILES"
  echo "selected_file_count=$(tr ' ' '\n' < "$SELECTED_FILES" | sed '/^$/d' | wc -l)"
  echo

  SAIL_DIR="$SAIL_ROOT" \
  TMPDIR="$RUNTIME_TMP" TMP="$RUNTIME_TMP" TEMP="$RUNTIME_TMP" \
  "$SAIL_BIN" \
    --strict-var \
    --strict-bitvector \
    --strict-exponentials \
    --require-version 0.19 \
    --config "$CONFIG" \
    --memo-z3-path "$SMT_CACHE" \
    model/riscv.sail_project \
    --variable "TERMINATION_FILE = true" \
    "${MODULES[@]}" \
    --just-check

  echo
  echo "typecheck=ok"
  echo

  SAIL_DIR="$SAIL_ROOT" \
  TMPDIR="$RUNTIME_TMP" TMP="$RUNTIME_TMP" TEMP="$RUNTIME_TMP" \
  "$SAIL_BIN" \
    --plugin "$SAIL_LEAN_PLUGIN" \
    --strict-var \
    --strict-bitvector \
    --strict-exponentials \
    --require-version 0.19 \
    --config "$CONFIG" \
    --lean \
    --memo-z3 \
    --memo-z3-path "$SMT_CACHE" \
    --lean-output-dir "$OUT_ROOT" \
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
    --lean-partial-function currentlyEnabled \
    --lean-partial-function get_xLPE \
    --lean-import-file handwritten_support/RiscvExtras.lean \
    -o "$OUT_MODEL" \
    model/riscv.sail_project \
    --variable "TERMINATION_FILE = true" \
    "${MODULES[@]}"

  echo
  echo "Generated Lean package:"
  find "$OUT_ROOT/$OUT_MODEL" -maxdepth 4 -type f | sort
} 2>&1 | tee "$LOG"
