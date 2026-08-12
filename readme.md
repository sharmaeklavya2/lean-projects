# Lean Projects

A personal monorepo of Lean 4 / Mathlib projects.
All projects share a single Mathlib dependency, declared in `lakefile.toml`.
The `lean-toolchain` file pins the Lean version (read by `elan`).

## Project Layout

* **Single-file project**: just `ProjectName.lean` at the repo root.
* **Multi-file project**: `ProjectName.lean` at the repo root and
  a `ProjectName/` folder containing the sub-module files.
  Sub-modules are imported as `import ProjectName.SubModule` in `ProjectName.lean`.

Each project must have a corresponding `[[lean_lib]]` entry in `lakefile.toml`.

## Local Setup

Install [`elan`](https://github.com/leanprover/elan). Then in this directory:

```bash
lake exe cache get   # download pre-built Mathlib .olean files
lake build           # build all targets
```

## VS Code with Docker Dev-container

One can open this repository in a VS code devcontainer.
See <https://code.visualstudio.com/docs/devcontainers/containers> for details.
The container is specified in the `.devcontainer` directory.
This setup runs Lean 4 and Claude Code in a docker container.
