#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
T42_FILE="$ROOT/Paper/BlindTests/NNLecture16/Theorem42/StrictFinal.lean"
T43_FILE="$ROOT/Paper/BlindTests/NNLecture16/Theorem43/StrictFinal.lean"

if [[ ! -f "$T42_FILE" || ! -f "$T43_FILE" ]]; then
  echo "[check_final_signature] missing strict-final files"
  exit 1
fi

extract_stmt() {
  local file="$1"
  local theorem_name="$2"
  awk -v name="$theorem_name" '
    $0 ~ "^theorem "name"$" || $0 ~ "^theorem "name"[[:space:]]" {capture=1}
    capture {print}
    capture && /:= by/ {exit}
  ' "$file"
}

FORBIDDEN='hDense|UniversalApproxProperty|UniversalApproxAlgorithm|SampleConcentrationData|FiniteClassConcentrationData|HasSubgaussianMGF'

T42_STMT="$(extract_stmt "$T42_FILE" "theorem42_strict_final")"
T43_STMT="$(extract_stmt "$T43_FILE" "theorem43_strict_final")"

if [[ -z "$T42_STMT" ]]; then
  echo "[check_final_signature] theorem42_strict_final not found"
  exit 1
fi
if [[ -z "$T43_STMT" ]]; then
  echo "[check_final_signature] theorem43_strict_final not found"
  exit 1
fi

if echo "$T42_STMT" | rg -q "$FORBIDDEN"; then
  echo "[check_final_signature] forbidden token found in theorem42_strict_final signature"
  echo "$T42_STMT"
  exit 1
fi

if echo "$T43_STMT" | rg -q "$FORBIDDEN"; then
  echo "[check_final_signature] forbidden token found in theorem43_strict_final signature"
  echo "$T43_STMT"
  exit 1
fi

echo "[check_final_signature] OK"
