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
- New "extended" draft completed on 06/22/2026.

## Comparator output

Note: No landrun available on MacOS, so running the "fake" comparator.

```
$ lake env $COMPARATOR_BIN comparator_config.json
Building ComparatorChallenge
WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING exec lake build ComparatorChallenge
⚠ [2235/2236] Built ComparatorChallenge
warning: ComparatorChallenge.lean:133:8: declaration uses `sorry`
Build completed successfully (2236 jobs).
Exporting #[KrafftSieve.mu_min_lt_one_implies_tpc, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList] from ComparatorChallenge
WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING exec /Users/nando/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export ComparatorChallenge -- KrafftSieve.mu_min_lt_one_implies_tpc propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList
Building ComparatorSolution
WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING exec lake build ComparatorSolution
Build completed successfully (2988 jobs).
Exporting #[KrafftSieve.mu_min_lt_one_implies_tpc, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList] from ComparatorSolution
WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING exec /Users/nando/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export ComparatorSolution -- KrafftSieve.mu_min_lt_one_implies_tpc propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Update: I managed to setup a GitHub Actions workflow to run the comparator.
```
[landrun] 2026/06/24 06:17:55 Landlock restrictions applied successfully
[landrun] 2026/06/24 06:17:55 Executing: [lean4export ComparatorSolution -- KrafftSieve.mu_min_lt_one_implies_tpc propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList]
Exporting #[KrafftSieve.mu_min_lt_one_implies_tpc, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList] from ComparatorSolution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Update (07/07/2026): The comparator setup is probably out of sync with the rest of the repo, as we have been advancing with the code. We will fix it when we are done closing all the sorry-ed stubs (5 left as of this writing).
