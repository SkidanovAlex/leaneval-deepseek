import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the prime-sum reduction of `Kf`

`Work.BMF.Kf f x = Σ_{n ≤ x} f n log n`.  Writing `log n = Σ_{d ∣ n} Λ d`, the divisor sum is
split as `n = d * m` and the `d`-sum is reindexed; the resulting terms are

`Tf f N d = Σ_{m ≤ N/d} f (d * m)`.

These definitions are shared with the files proving the individual steps of
`Work.BMF.Kf_primeSum_reduction_abs`.
-/

namespace Work.BMF

open Finset

/-- `Tf f N d = Σ_{m ∈ [1, N/d]} f (d * m)`. -/
noncomputable def Tf (f : ℕ → ℂ) (N d : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (N / d), f (d * m)

end Work.BMF
