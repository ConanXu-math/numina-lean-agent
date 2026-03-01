# Lean-ADMM + Numina-Lean-Agent 集成说明

## 目标

把 `adaptive admm/lean_admm` 的最后 translate 步骤（`math -> Lean4`）接入 `numina-lean-agent`，获得多轮修复和可验证闭环能力，同时保留原有 API 翻译路径作为回退。

## 当前状态

- 已在 `adaptive admm/lean_admm/alpha_evolve/translate_LLM.py` 中加入后端切换：
  - `TRANSLATE_BACKEND=api`（默认）：走原始 `LLMClient` 路径
  - `TRANSLATE_BACKEND=numina_agent` 或 `agent`：走 `scripts.run_claude` agent 路径
- 已在 `__main__` 开启严格校验：
  - 先执行 `check_math_form`（R1-R7）
  - 校验失败则中止，不继续翻译 Lean

## 端到端工作流

1. 读取 Python 策略代码（默认 `openevolve_output/best/best_program.py`）
2. `code -> math_form`：`get_math_form_from_code`
3. `math_form -> check`：`check_math_form` + `parse_check_result`
   - 若 `False`：打印问题并停止
4. `math_form -> Lean`：`get_lean4_results`
   - 根据 `TRANSLATE_BACKEND` 选择 `api` 或 `numina_agent`
5. 输出最终 Lean 代码

## Agent 模式细节

当 `TRANSLATE_BACKEND=numina_agent` 时：

- 在 `alpha_evolve/.agent_translate_tmp/` 下创建：
  - `translated_output.lean`
  - `translate_agent_prompt.txt`
- 调用：

```bash
python -m scripts.run_claude run <target_file> \
  --prompt-file <prompt_file> \
  --cwd <repo_root> \
  --max-rounds 3 \
  --check True
```

- 成功后读取 `translated_output.lean` 作为输出
- 失败时自动回退到 `api` 翻译路径

## 如何运行

### 1) 默认 API 翻译

```bash
python "adaptive admm/lean_admm/alpha_evolve/translate_LLM.py"
```

### 2) Agent 翻译（推荐）

```bash
export TRANSLATE_BACKEND=numina_agent
python "adaptive admm/lean_admm/alpha_evolve/translate_LLM.py"
```

## 依赖与注意事项

- Agent 模式依赖 Claude CLI 和 MCP（lean-lsp）已可用
- `--cwd` 目录需有正确的 MCP 配置
- 项目路径包含空格（`adaptive admm`），请保持参数化调用（不要手写拼接 shell 字符串）

## 下一步建议

- 增加 `TRANSLATE_AGENT_MAX_ROUNDS` 环境变量，避免硬编码 `max_rounds=3`
- 给临时输出加时间戳，避免每次覆盖同一个 `translated_output.lean`
- 记录每次翻译的校验结果和最终后端来源（api / agent），便于对比质量与稳定性
