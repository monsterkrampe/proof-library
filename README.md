# Existential Rules in Lean

This is a collection of some definitions, results, and proofs around
Existential Rules (aka. Tuple-Generating Dependencies) with disjunctions
and the Chase algorithm
written up in LEAN 4.
Mostly, these the formalizations related to my own research.

As a first milestone, this repo contains a somewhat generalized formalization of the chase on disjunctive existential rules in `ProofLibrary/ChaseSequence`.
The generalized definition captures both the skolem and restricted chase at the same time.
The definition of the chase for disjunctive rules involves (possibly) infinite trees of finite degree.

Some key results around this definition have already been formalized:
- The result of the chase is a universal model set (which is the fundamental property of this algorithm).
- A chase sequence without alternative matches on rules without disjunctions yields a universal model that is a core.
- If a rule set is model-faithful acyclic (MFA), then every chase sequence on every database terminates.

## Notes on Setup

Using [`elan`](https://github.com/leanprover/elan) / `lake`:

- Install `elan`, e.g. via `nix-shell -p elan` or simply `nix develop` if you are using nix.
- Run `lake build` to build the project. If the build is successful, the proofs are correct :tada:

