# paper-template

本仓库是三仓协同里的最外层运行入口：

1. `paper-template`：论文项目与 Codex 运行入口。
2. `lean-proof-skills`：skillpack 父仓（内部含 `lean4` 与 `ml-paper-workflow`）。
3. `MLTheory`：共享 Lean 理论库（通过 Lake `git + tag` 依赖）。

## 目录装配

```text
.agents/
  skillpacks/
    lean-proof-skills/           # submodule（父仓）
  skills/
    lean4 -> ../skillpacks/lean-proof-skills/.agents/skills/lean4
    ml-paper-workflow -> ../skillpacks/lean-proof-skills/.agents/skills/ml-paper-workflow
.codex/config.toml               # repo-scope Codex + lean-lsp MCP
lakefile.toml                    # MLTheory git+tag pin
Paper/Smoke.lean                 # 冒烟导入验证
scripts/setup_mcp.sh             # MCP 注册兜底脚本
```

## 一键装配

```bash
git submodule update --init --recursive
scripts/setup_mcp.sh
```

`lakefile.toml` 中的 `MLTheory` URL 默认是占位值，使用前替换为真实地址：

```toml
[[require]]
name = "MLTheory"
git = "https://github.com/JKay15/mltheory-lean.git"
rev = "v0.1.0"
```

## 验证

```bash
codex mcp list
~/.elan/bin/lake build
```

## 升级与回滚

1. 升级 `lean-proof-skills`：更新 submodule 指针并回归验证。
2. 升级 `MLTheory`：修改 `lakefile.toml` 中 `rev = "vX.Y.Z"` 并回归验证。
3. 回滚 skillpack：恢复旧 submodule 指针。
4. 回滚 MLTheory：恢复旧 tag pin。
