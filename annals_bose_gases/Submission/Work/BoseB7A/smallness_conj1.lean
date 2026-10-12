import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.smallness_conj1` — the smallness of `K_L√(μa)·K_H a` at FS's parameters

FS's parameters give `K_L = X^{-21/2}`, `K_H = X^{-549/4}` with `X = (μa³)^{1/323}`,
and `√(μa)·a = √(μa³) = √t = X^{323/2}`; hence

  `K_L·√(μa)·(K_H·a) = X^{-21/2-549/4+323/2} = X^{55/4} = (μa³)^{55/(4·323)}`

**exactly** (no inequality is used in the identification).  The statement below
is therefore the monotone comparison `X ≤ τ ⟹ X^{55/4} ≤ τ^{55/4}` with
`55/4 > 0`, written for the callers of `Submission/Work/BoseB7A/Statements.lean`
(where this product is the overall factor of the `eq:EstimateQ3Tilde4` and
`eq:Q3Cancels` error brackets).

The proof only uses the scalar values of `Work.BoseB7.FSParamsVals`
(`KL_val`, `KH_val`, `mu_pos`, `a_pos`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

/-- **FS's parameter smallness.**  At FS's parameter point the product
`K_L·√(μa)·(K_H·a)` equals `X^{55/4}` with `X = (μa³)^{1/323}`, so it is
dominated by `τ^{55/4}` as soon as `X ≤ τ`. -/
theorem smallness_conj1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) {τ : ℝ}
    (hX : Work.BoseBox.fsXp hv.t 1 ≤ τ) :
    E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) ≤ τ ^ (55 / 4 : ℝ) := by
  have ht : 0 < hv.t := hv.t_pos
  have ha : 0 < E.aScat := hv.a_pos
  have hmu : 0 < E.mu := Work.BoseB7.mu_pos E hv
  have hμa : 0 ≤ E.mu * E.aScat := (mul_pos hmu ha).le
  -- `√(μa)·a = √(μa³) = √t`
  have hsqrt : Real.sqrt (E.mu * E.aScat) * E.aScat = Real.sqrt hv.t := by
    calc Real.sqrt (E.mu * E.aScat) * E.aScat
        = Real.sqrt (E.mu * E.aScat) * Real.sqrt (E.aScat ^ 2) := by
          rw [Real.sqrt_sq ha.le]
      _ = Real.sqrt ((E.mu * E.aScat) * E.aScat ^ 2) := by rw [Real.sqrt_mul hμa]
      _ = Real.sqrt (E.mu * E.aScat ^ 3) := by
          congr 1
          ring
      _ = Real.sqrt hv.t := by rw [hv.mu_eq]
  -- `√t = X^{323/2}`
  have hsqrtX : Real.sqrt hv.t = Work.BoseBox.fsXp hv.t (323 / 2) := by
    rw [Real.sqrt_eq_rpow]
    simp only [Work.BoseBox.fsXp]
    congr 1
    norm_num
  -- the whole product is `X^{55/4}`
  have hEq : E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat)
      = Work.BoseBox.fsXp hv.t (55 / 4) := by
    have h1 : E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat)
        = Work.BoseBox.fsXp hv.t (-(21 / 2)) * Work.BoseBox.fsXp hv.t (-(549 / 4))
            * Real.sqrt hv.t := by
      rw [Work.BoseB7.KL_val E hv, Work.BoseB7.KH_val E hv, ← hsqrt]
      ring
    rw [h1, hsqrtX, Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  calc E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat)
      = Work.BoseBox.fsXp hv.t (55 / 4) := hEq
    _ ≤ τ ^ (55 / 4 : ℝ) := by
        have h1 : Work.BoseBox.fsXp hv.t (55 / 4)
            = (Work.BoseBox.fsXp hv.t 1) ^ (55 / 4 : ℝ) := by
          rw [Work.BoseBox.fsXp_rpow ht.le]
          congr 1
          ring
        rw [h1]
        exact Real.rpow_le_rpow (Work.BoseBox.fsXp_nonneg ht.le) hX (by norm_num)

end Work.BoseB7A
