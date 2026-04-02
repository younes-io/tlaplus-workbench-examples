# tlaplus-workbench-examples

This repository contains TLA+ examples for both TLC model checking and TLAPS theorem proving, produced with assistance from Codex CLI and kept compatible with the current `younes-io/agent-skills` TLA+ skills.

## Scope

These are one-shot TLA+ examples produced for exploration and learning.
They are not production-hardened specs and are not maintained as long-lived models.

## Attribution

These specs were authored in this repository using Codex CLI with assistance from the TLA+ checking and proof skills in `younes-io/agent-skills`.

Current upstream skill names:

- `tla-check` for TLC model checking
- `tla-proof` for TLAPS theorem proving

Legacy names such as `tlaplus-workbench` and `tlaps-workbench` appear in older prompts and discussions, but upstream has since renamed those skills.

Skill reference (`SKILL.md`):

<https://github.com/younes-io/agent-skills/blob/main/skills/tla-check/SKILL.md>

<https://github.com/younes-io/agent-skills/blob/main/skills/tla-proof/SKILL.md>

## Current Upstream Workflow

Install the current upstream skills from `younes-io/agent-skills`:

```bash
npx -y skills add younes-io/agent-skills --skill tla-check
npx -y skills add younes-io/agent-skills --skill tla-proof
```

Current runner artifact directories created by upstream scripts:

- `.tla-check/runs/...` for TLC runs
- `.tla-proof/runs/...` for TLAPS runs
- `.tlacache/` for TLAPS cache files

## Spec-to-Prompt Mapping

### `Mutex.tla`

Prompt:

```text
"$tla-check Model a 2-client mutex protocol. Safety: never two holders at once. Liveness: if lock is free and a client requests, it eventually gets the lock. Use small bounds, write Mutex.tla/Mutex.cfg, run TLC, and iterate until either pass or a real counterexample remains."
```

### `Queue.tla`

Prompt:

```text
"$tla-check Design a bounded message queue with ack/retry. Safety: no message delivered more than once. Include message reordering and drops. Create Queue.tla/Queue.cfg, run the checker, and explain any counterexample step-by-step."
```

### `WalletLedgerAA.tla`

Prompt:

```text
"$tla-check Model a multi-region wallet ledger with active-active writes, idempotency keys, async replication, and compensation for failed transfers. Infer and justify safety/liveness properties yourself, encode them, run TLC, and iterate."
```

### `OfflineFirstSync.tla`

Prompt:

```text
"$tla-check Model cross-device offline-first sync with edits, deletes (tombstones), conflict resolution, and eventual cleanup GC."
```

### `RaftElectionTLAPS.tla`

Prompt:

```text
"$tla-proof Model simplified Raft leader election (terms, votes). Prove leader uniqueness per term and monotonic term growth."
```
