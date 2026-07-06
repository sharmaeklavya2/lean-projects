# About this Repository

This directory is a personal monorepo of Lean 4 projects. Some of the projects use Mathlib.

# About the Environment

The `.git` folder is read-only. Read-only commands (like `git status`, `git log`, `git diff`) are fine. Commands that write (like `git commit`, `git checkout`, `git add`) will fail.

`AiScratch.lean` is a `.gitignore`d file that you may use as scratch space. Once you are done using it, no need to clear or delete it.

# Building and Checking

* Work in a tight edit-rebuild loop: after each change, rebuild the affected module (e.g. `lake build DataMktOligoHard.SpecialPoints`) before moving on. Rebuilds are incremental and typically take seconds.
* For scratch work / `#print axioms`, put it in `AiScratch.lean` and run `lake build AiScratch`. Its `#print axioms` output appears as `info:` lines.
