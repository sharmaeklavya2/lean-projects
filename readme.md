# Lean Projects

A personal monorepo of Lean 4 / Mathlib projects.
All projects share a single Mathlib dependency, declared in `lakefile.toml`.

### Project layout

* **Single-file project**: just `ProjectName.lean` at the repo root.
* **Multi-file project**: `ProjectName.lean` at the repo root and
  a `ProjectName/` folder containing the sub-module files.
  Sub-modules are imported as `import ProjectName.SubModule` in `ProjectName.lean`.

Each project must have a corresponding `[[lean_lib]]` entry in `lakefile.toml`.

## Structure

* `lakefile.toml`: Lake package config; declares Mathlib and all library targets.
* `lean-toolchain`: Pins the Lean version (read by `elan` automatically).
* `lake-manifest.json`: Lockfile: exact git commits for Mathlib and its dependencies.
* `.lake/`: Build artefacts and downloaded packages (not committed).

## Setup

Install [`elan`](https://github.com/leanprover/elan), then in this directory:

```bash
lake exe cache get   # download pre-built Mathlib .olean files
lake build           # build all targets
```
