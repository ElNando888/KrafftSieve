# KrafftSieve

Formal verification of the Krafft sieve architecture for the Twin Prime Conjecture.

## Development process

+ The initial thrust came from my [previous work](https://doi.org/10.5281/zenodo.18758252) on the Krafft form.
+ I used Gemini 3.1 Pro to clarify the ideas and prepare a blueprint of the formal verification process. I also used it to generate precise prompts for the formal prover.
+ Aristotle 0.7.0 was the workhorse for the formal verification process. It also provided useful feedback, on one occasion forcing Gemini and I to reconsider and revise our approach.

I know I have to take entire responsibility for the whole output, but for what it's worth, I consider this a collaborative effort between _all_ three "entities" involved.

## Manuscripts

- First draft completed on 03/24/2026.
- The idea of submitting to AFM was somewhat misguided, so drafting has restarted (04/18/2026).
- Second draft completed on 04/20/2026.

## Challenge Conformance

To present the core theorems of this repository as formal challenges for an AI agent, we have isolated the target theorems into a standalone `Challenge.lean` specification file. This file provides the definitions and statement types with `sorry`ed proofs, using only `Mathlib` imports. 

To verify that our implementation mathematically matches the challenge specification, we use a `Conformance.lean` script populated with `example` checks. This mirrors the community standard used in Kevin Buzzard's Jacobian Challenge.

We explicitly chose this manual conformance architecture over the `leanprover/comparator` AST-checking binary (used in `lean-pool` and `miniF2F`). The `lean-comparator` is currently too fragile for monolithic challenge files: when extracting numeric literals (like `2` and `3`), Lean 4's compiler generates hidden auxiliary proofs (`OfNat` instances like `_proof_1`). Because `Challenge.lean` combines multiple dependencies into a single file, Lean aggressively deduplicates these auxiliary proofs differently than it does when the definitions are spread across multiple source files. As a result, the ASTs inevitably mismatch, causing the comparator to throw `Const does not match` errors even when the definitions are textually identical. The manual conformance approach completely bypasses this micro-syntactic fragility by checking type equality instead of ASTs.
