import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `β x = √(9/4 − Σ (off (x i))²) ≤ 3/2 = βMax`: the sum of squares of the offsets is
nonnegative, so the radicand is at most `9/4 = (3/2)²`, and `√·` is monotone. -/
theorem beta_le_max (x : E3) : beta x ≤ betaMax := by
  rw [beta, betaMax]
  have hle : (9 : ℝ) / 4 - ∑ i, (off (x i)) ^ 2 ≤ (3 / 2) ^ 2 := by
    have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (off (x i)))
    nlinarith
  calc Real.sqrt ((9 : ℝ) / 4 - ∑ i, (off (x i)) ^ 2)
      ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 3 / 2 := Real.sqrt_sq (by norm_num)

end Work.Cusp
