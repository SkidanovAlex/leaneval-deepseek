import Mathlib
import Submission.Work.RHContract.Corpus

open scoped BigOperators

namespace Work.RHContract.A

/-- The upper bounding function for `θ` used in the `ca_delta_le` estimate:
`U t = 0` for `t < 2`, `U t = t` for `2 ≤ t ≤ 1530`, and `U t = log 3 · t` for `t ≥ 1530`. -/
noncomputable def caU (t : ℝ) : ℝ :=
  if t < 2 then 0 else if t ≤ 1530 then t else Real.log 3 * t

/-- The lower bounding function for `θ` used in the `ca_delta_le` estimate:
`L t = 0` for `t < 3`, `= 0.35 t` for `3 ≤ t < 39`, `= 0.7 t` for `39 ≤ t < 1530`,
and `= 0.9 t` for `t ≥ 1530`. -/
noncomputable def caL (t : ℝ) : ℝ :=
  if t < 3 then 0 else if t < 39 then 0.35 * t else if t < 1530 then 0.7 * t else 0.9 * t

/-- The upper limit `K(ε) = ⌈e^{2/ε}⌉ + 2` of the prime range used in the colossally
abundant product `caNumber ε`. -/
noncomputable def caK (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- `caLevel ε k`: the largest prime `p < K(ε)` with exponent `⌊μ(p,ε)⌋₊ ≥ k`
(so `caLevel ε 1 = caXi ε`), and `0` when this set is empty. -/
noncomputable def caLevel (ε : ℝ) (k : ℕ) : ℕ :=
  ((Finset.range (caK ε)).filter Nat.Prime).filter
    (fun p : ℕ => k ≤ ⌊Work.RHPlan.caMu p ε⌋₊) |>.sup id

end Work.RHContract.A
