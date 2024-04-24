# Proof Library

This is a collection of some definitions, results, and proofs written up in LEAN 4. 
Mostly, these are vaguely related to my own research.
I started this project in my free time to get some hands on experience with lean.
While mathlib is imported as a dependency, I built most things from scratch to understand better how things work.

As a first milestone, this repo contains a formalization of the restricted chase in `ProofLibrary/ChaseSequence.lean` 
and a proof that the result of such a sequence is a universal model. (This is a fundamental and well-known result in my field of research.)

## Notes on Setup

Using [`elan`](https://github.com/leanprover/elan) / `lake`:  

- Install `elan`, e.g. via `nix-shell -p elan` if you are using nix.
- Run `lake exe cache get` to download a prebuilt version of mathlib. (Optional) 
- Run `lake build` to build the project. If the build is successful, the proofs are correct :tada:

