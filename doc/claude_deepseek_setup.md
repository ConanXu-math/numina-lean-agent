# Claude Code + DeepSeek 接入操作指南

本文档用于记录从安装 Claude Code 到在本项目中通过 DeepSeek 兼容接口运行的完整流程，便于后续重复配置。

## 1. 适用范围

- 操作系统：macOS / Linux（本文以 macOS + zsh 为例）
- 项目目录：`numina-lean-agent`
- 目标：在 Claude Code 中使用 DeepSeek 的 Anthropic 兼容接口

## 2. 前置条件

请先确保以下命令可用：

```bash
git --version
curl --version
python --version
```

并提前准备好 DeepSeek API Key。

## 3. 安装 Claude Code

可使用官方安装脚本：

```bash
curl -fsSL https://claude.ai/install.sh | bash
```

安装后验证：

```bash
claude --version
```

如果命令不可用，重开一个终端后再试。

## 4. 配置 DeepSeek（项目级，推荐）

在项目根目录创建配置文件 `./.claude/settings.json`：

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "https://api.deepseek.com/anthropic",
    "ANTHROPIC_AUTH_TOKEN": "YOUR_DEEPSEEK_API_KEY",
    "API_TIMEOUT_MS": "600000",
    "ANTHROPIC_MODEL": "deepseek-chat",
    "ANTHROPIC_SMALL_FAST_MODEL": "deepseek-chat",
    "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1"
  }
}
```

将 `YOUR_DEEPSEEK_API_KEY` 替换为你的真实 Key。

说明：

- `ANTHROPIC_BASE_URL`：DeepSeek 的 Anthropic 兼容端点
- `ANTHROPIC_AUTH_TOKEN`：认证令牌（API Key）
- `API_TIMEOUT_MS=600000`：10 分钟超时，减少长输出超时失败
- `ANTHROPIC_MODEL`：主模型
- `ANTHROPIC_SMALL_FAST_MODEL`：快速模型
- `CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1`：禁用非必要流量

## 5. 启动与验证

在项目根目录启动：

```bash
cd /Users/conanxu/Desktop/numina-lean-agent
claude
```

进入 Claude Code 后建议执行：

- `/status`：确认当前 provider/model 已按配置生效
- `/model deepseek-chat`：必要时手动切换模型

如果能正常对话并返回结果，说明接入成功。

## 6. 与本项目 runner 联动

本项目执行器会调用本机 `claude` 命令，因此只要上面的 Claude Code 配置生效，项目脚本通常可直接复用。

示例（在项目根目录执行）：

```bash
python -m scripts.run_claude run leanproblems/Minif2f/mathd_numbertheory_284.lean \
  --prompt_file prompts/prompt_complete_file.txt \
  --max_rounds 5
```

```bash
python -m scripts.run_claude batch config/config_minif2f.yaml
```

## 7. 可选：临时环境变量方式（一次性）

如果不想写入 `settings.json`，可临时导出环境变量：

```bash
export ANTHROPIC_BASE_URL="https://api.deepseek.com/anthropic"
export ANTHROPIC_AUTH_TOKEN="YOUR_DEEPSEEK_API_KEY"
export API_TIMEOUT_MS="600000"
export ANTHROPIC_MODEL="deepseek-chat"
export ANTHROPIC_SMALL_FAST_MODEL="deepseek-chat"
export CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC="1"
```

然后执行 `claude`。该方式仅对当前 shell 会话生效。

## 8. 常见问题排查

### 8.1 401 或鉴权失败

- 检查 `ANTHROPIC_AUTH_TOKEN` 是否为有效 DeepSeek Key
- 确认 Key 权限和额度正常

### 8.2 404 / 模型不存在

- 检查 `ANTHROPIC_BASE_URL` 是否为兼容端点
- 检查模型名是否可用（例如 `deepseek-chat`）

### 8.3 请求超时

- 增大 `API_TIMEOUT_MS`，例如 `600000`
- 简化单次任务，降低输出长度

### 8.4 配置没生效

- 确认配置文件路径是项目内 `./.claude/settings.json`
- 确认在项目目录启动 `claude`
- 用 `/status` 再次核对当前配置

### 8.5 `Either prompt or prompt_file must be provided`

- 常见原因是 `--prompt_file` 路径写错
- 本项目正确路径是 `prompts/prompt_complete_file.txt`，不是 `config/prompt_complete_file.txt`
- 可先运行 `ls prompts` 确认文件存在后再执行命令

## 9. 安全建议

- 不要将真实 API Key 提交到仓库
- 建议将 Key 仅保存在本地配置文件
- 本仓库已忽略 `.claude/` 目录，通常不会被 git 跟踪

## 10. 快速复用清单

每次新机器迁移时按以下顺序：

1. 安装 Claude Code
2. 在项目中创建 `./.claude/settings.json`
3. 写入 DeepSeek 兼容配置和 API Key
4. `cd` 到项目目录执行 `claude`
5. `/status` 验证模型
6. 运行项目命令 `python -m scripts.run_claude ...`

