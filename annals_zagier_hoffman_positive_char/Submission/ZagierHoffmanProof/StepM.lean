import Submission.ZagierHoffmanProof.StepM4
import Submission.ZagierHoffmanProof.StepM5
import Submission.ZagierHoffmanProof.StepM6
import Submission.ZagierHoffmanProof.StepM7
import Submission.ZagierHoffmanProof.StepM8
import Submission.ZagierHoffmanProof.StepM9
import Submission.ZagierHoffmanProof.StepM10

/-!
# Index module for the `q = 2` power-sum degree recursion (`StepM4`–`StepM9`)

* `StepM4`: valuation bookkeeping (constants, powers of `X`, finite sums).
* `StepM5`: the truncated level recursion `P_{d+1}(k) = ∑_{j ≤ N} … + E` (Thakur §3.2).
* `StepM6`: the map `T k = k + 2 ^ v_2(k)` and the exponent `sExp d k = ∑_{i=1}^d T^i(k)`.
* `StepM8`: the odd-form digit estimate of Thakur's §8.1.
* `StepM7`: ★★ `v (P_d k) = exp (−sExp d k)` for fields with `Nat.card F = 2`.
* `StepM9`: corollaries (the classical recursion, the degree jump) and regression tests.
-/
