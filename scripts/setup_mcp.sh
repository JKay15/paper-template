#!/usr/bin/env bash
set -euo pipefail

if codex mcp list | rg -q '^lean-lsp\b'; then
  echo "lean-lsp MCP already configured"
  exit 0
fi

codex mcp add lean-lsp -- uvx lean-lsp-mcp

echo "lean-lsp MCP configured"
