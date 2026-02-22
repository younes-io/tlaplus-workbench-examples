# tlaplus-workbench-examples

This repository contains TLA+ and TLC example specs produced with assistance from Codex CLI and the `tlaplus-workbench` skill.

## Attribution

These specs were authored in this repository using Codex CLI with assistance from the `tlaplus-workbench` skill.

Skill reference (`SKILL.md`):
<https://github.com/younes-io/agent-skills/blob/main/skills/tlaplus-workbench/SKILL.md>

## Spec-to-Prompt Mapping

- `Mutex.tla`
  Prompt: "$tlaplus-workbench Model a 2-client mutex protocol. Safety: never two holders at once. Liveness: if lock is free and a client requests, it eventually gets the lock. Use small bounds, write Mutex.tla/Mutex.cfg, run TLC, and iterate until either pass or a real counterexample remains."
- `Queue.tla`
  Prompt: "$tlaplus-workbench Design a bounded message queue with ack/retry. Safety: no message delivered more than once. Include message reordering and drops. Create Queue.tla/Queue.cfg, run the checker, and explain any counterexample step-by-step."
- `WalletLedgerAA.tla`
  Prompt: "$tlaplus-workbench Model a multi-region wallet ledger with active-active writes, idempotency keys, async replication, and compensation for failed transfers. Infer and justify safety/liveness properties yourself, encode them, run TLC, and iterate."
- `OfflineFirstSync.tla`
  Prompt: "$tlaplus-workbench Model cross-device offline-first sync with edits, deletes (tombstones), conflict resolution, and eventual cleanup GC."
