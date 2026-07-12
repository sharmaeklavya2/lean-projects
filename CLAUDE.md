# About this Repository

This directory is a personal monorepo of Lean 4 projects. Some of the projects use Mathlib.

# About the Environment

The project's directory is expected to be `/workspace` — absolute paths throughout this file (`/workspace/.lake/packages/…`, `/workspace/lean-toolchain`, etc.) assume it, and the shell starts there.

The `.git` folder is read-only. Read-only commands (like `git status`, `git log`, `git diff`) are fine. Commands that write (like `git commit`, `git checkout`, `git add`) will fail.

`AiScratch.lean` is a `.gitignore`d file that you may use as scratch space. Once you are done using it, no need to clear or delete it.

# Building and Checking

* Work in a tight edit-rebuild loop: after each change, rebuild the affected module (e.g. `lake build DataMktOligoHard.SpecialPoints`) before moving on. Rebuilds are incremental and typically take seconds.
* For scratch work / `#print axioms`, put it in `AiScratch.lean` and run `lake build AiScratch`. Its `#print axioms` output appears as `info:` lines.

# Finding Lemmas and APIs

When unsure whether a lemma/identifier exists or what it's called, grep the source immediately instead of reasoning from memory (it's faster and more reliable):

* **Mathlib / Batteries / other deps** → `/workspace/.lake/packages/<pkg>/` (e.g. `mathlib`, `batteries`, `aesop`, `Qq`). Lean *core* is NOT under `.lake`.
* **Lean core** (`Init`, core tactics) → `~/.elan/toolchains/*/src/lean/` (home-relative glob; don't hardcode the version — it derives from `/workspace/lean-toolchain`).
* Recipe: `grep -rn "pattern" --include=*.lean <pkg-dir>` (add `-h` to drop filenames). Point grep at the specific package dir; never scan broadly (no `find /`, `find ~`).

# Reading Lean Files

`scripts/lean-sig.py FILE.lean [FILE.lean …]` prints a Lean file with tactic proofs stripped: every `theorem`/`lemma`/`example` collapses to its signature followed by `:= by sorry /- proof omitted -/`, while `def`/`abbrev`/`instance`/`structure`/`inductive` bodies, docstrings, attributes, `variable`s, imports, and comments are kept verbatim. (Term-mode proofs — `:= <term>`, no `by` — are left intact, since they're usually short.) The output is still syntactically valid Lean.

* **Rationale.** Proofs are often long and rarely relevant when you only need to learn a file's *definitions and theorem statements* (its API surface); reading them raw floods context. Decide per task: if you need the statements/definitions, read via `lean-sig.py`; if you actually need to understand or modify a proof, read the file directly.

* **When explicitly asked to explore a project or subdirectory** (e.g. "explore `BinPack/Harmonic/`"): list its files recursively (`git ls-files 'BinPack/Harmonic/*.lean'` — path scopes it, `*` recurses, gitignored files excluded) and read the `.lean` files via `lean-sig.py`.

# Imports

* Prefer targeted imports (e.g. `import Mathlib.Data.Real.Basic`, `import Mathlib.Tactic.Linarith`) over whole-library `import Mathlib`. `import Mathlib` loads ~1681 MB olean / 8095 modules (~1 min build); a targeted closure is far smaller (e.g. BinPack.lean ~271 MB → ~14s), keeping build-checking viable. On an "Unknown constant", grep `.lake/packages/mathlib` for the lemma's declaring module and add just that import. Statement generality (abstract typeclass vs concrete `ℝ`) usually doesn't change build time.
* **`ℤ`/`ℕ` need Mathlib.** In Mathlib-free files `ℤ` and `ℕ` are undefined (Mathlib-only notation; core carries only a `@[suggest_for …]` hint) — use `Int`/`Nat`, or add `notation "ℤ" => Int` / `notation "ℕ" => Nat`. `autoImplicit` masks the mistake by auto-binding the glyph as a phantom type variable; the error then surfaces later as `failed to synthesize HMul/OfNat`. `set_option autoImplicit false` exposes it immediately as `Unknown identifier`.

# Running Commands and Permissions

Run Bash commands in the simplest natural form so commands match the allowlist / read-only recognition. Don't contort commands to dodge permission prompts — a prompt is a signal to refine the allowlist, not something to engineer around.

* Chaining read-only builtins is fine across any separator (`|`, `&&`, `;`), e.g. `grep ... | head`. Each subcommand is approved independently, so one unapproved step (or a write/exec step) gates the whole line.
* Read-only builtins (`ls`, `cat`, `grep`, `find`, `head`, `tail`, `wc`, `echo`, `diff`, `pwd`, `which`) need no allowlist entry. `lake build`, `lake env lean`, and `rg` are allowlisted. Use the **Edit/Write** tools for file changes, not `sed`.
* **Constructs that always prompt** (can't be statically analyzed — avoid them; no allowlist rule helps): `$(...)` command substitution, and shell control structures like `for … do … done`. Use grep's own `--include`/multiple path args, or separate Read/`cat` calls, instead.
* If a command is denied with a "log it" reason, append it (plus a one-line likely-trigger note) to `/workspace/secret/commands-to-debug.sh`, then retry.
* You can't see the permission-prompt layer: a successful result looks identical whether auto-approved or user-approved, so never claim a command "ran without a prompt" — only the user can confirm that.
