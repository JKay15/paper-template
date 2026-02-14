# AGENT.md

兼容文件名（主规范文件为 `AGENTS.md`）。

请优先阅读并遵循：
`/Users/xiongjiangkai/xjk_papers/paper-template/AGENTS.md`

关键约束摘要：
1. `AGENTS.md` 是主规范，`AGENT.md` 仅作兼容入口。
2. 若 skills 缺失，先 `git submodule update --init --recursive`。
3. `MLTheory` 通过 Lake 依赖拉取，执行 `~/.elan/bin/lake build` 后位于 `.lake/packages/MLTheory`。
4. 不随意改动 `lean-proof-skills` 正文，除非用户明确要求。
