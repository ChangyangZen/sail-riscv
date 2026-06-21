#!/usr/bin/env bash
set -euo pipefail

REPO="${SAIL_RISCV:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
SAIL_ROOT="${SAIL_ROOT:-$HOME/projects/sail-0.20.1-bench}"
SAIL_BIN="${SAIL_BIN:-$SAIL_ROOT/_build/default/src/bin/sail.exe}"
SAIL_LEAN_PLUGIN="${SAIL_LEAN_PLUGIN:-$SAIL_ROOT/_build/default/src/sail_lean_backend/sail_plugin_lean.cmxs}"

ART="${ART:-$REPO/generated/lean/full_rv64d_v256_e64}"
CONFIG="${CONFIG:-$ART/config/rv64d_v256_e64.json}"
OUT_ROOT="${OUT_ROOT:-$ART/generated/sail_lean}"
OUT_MODEL="${OUT_MODEL:-Lean_RV64D_Full}"
LOG="$ART/logs/generate_sail_full_lean.log"
SELECTED_FILES="$ART/config/rv64d_full_selected_files.txt"
RUNTIME_TMP="$ART/runtime_tmp"

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
  echo

  cd "$REPO/model"

  SAIL_DIR="$SAIL_ROOT" \
  TMPDIR="$RUNTIME_TMP" TMP="$RUNTIME_TMP" TEMP="$RUNTIME_TMP" \
  "$SAIL_BIN" \
    --strict-var \
    --strict-bitvector \
    --strict-exponentials \
    --require-version 0.19 \
    riscv.sail_project \
    --variable "TERMINATION_FILE = true" \
    --all-modules \
    --list-files \
    > "$SELECTED_FILES"

  echo "selected_files=$SELECTED_FILES"
  echo "selected_file_count=$(tr ' ' '\n' < "$SELECTED_FILES" | sed '/^$/d' | wc -l)"
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
    --lean-import-file ../handwritten_support/RiscvExtras.lean \
    -o "$OUT_MODEL" \
    --all-modules \
    --variable "TERMINATION_FILE = true" \
    riscv.sail_project

  echo
  echo "Generated Lean package:"
  find "$OUT_ROOT/$OUT_MODEL" -maxdepth 4 -type f | sort
} 2>&1 | tee "$LOG"
