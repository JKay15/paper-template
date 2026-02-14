# AGENTS.md

本文件是 `paper-template` 的仓库级执行规范，用于确保 Codex 在三仓协同下稳定工作。

## 1. 文件命名约定（避免歧义）
1. 主规范文件名使用 `AGENTS.md`。
2. `AGENT.md` 仅作为兼容入口，内容应指向本文件。

## 2. skills 发现与初始化
1. repo-scope skills 固定路径：
- `.agents/skills/lean4`
- `.agents/skills/ml-paper-workflow`
2. 上述两个路径应为 symlink，目标在：
- `.agents/skillpacks/lean-proof-skills/.agents/skills/lean4`
- `.agents/skillpacks/lean-proof-skills/.agents/skills/ml-paper-workflow`
3. 若 skills 缺失或 symlink 失效，先执行：
```bash
git submodule update --init --recursive
```
4. 不允许随意改动 skillpack 正文（`lean-proof-skills`）；仅在用户明确要求时才修改。

## 3. MLTheory 依赖发现规则
1. `MLTheory` 在本仓不是 submodule/symlink，而是 Lake 依赖（`git + rev`）。
2. 依赖声明位于 `lakefile.toml` 的 `[[require]] name = "MLTheory"`。
3. 执行 `lake build` 后，依赖会出现在：
- `.lake/packages/MLTheory`
4. 若 `.lake/packages/MLTheory` 不存在，先执行：
```bash
~/.elan/bin/lake build
```

## 4. Lean 工作流最小门禁
1. 先跑文件级检查：
```bash
~/.elan/bin/lake env lean Paper/Smoke.lean
```
2. 再跑项目级构建：
```bash
~/.elan/bin/lake build
```
3. 如需 Lean 交互能力，确认 MCP：
```bash
codex mcp list
```
若无 `lean-lsp`，执行：
```bash
scripts/setup_mcp.sh
```

## 5. 协作原则
1. 优先使用 repo-scope skills，而不是全局 skills。
2. 先复用 `MLTheory` 现有模块，不重复造轮子。
3. 若模块或定理找不到，先确认依赖已拉取（`lake build`），再开始补实现。
