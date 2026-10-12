import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.smallness_conj6` — `K_H a / ℓ` at FS's parameters

At FS's parameter point (`X = (μa³)^{1/323}`, `K_H = X^{-549/4}`,
`K_ℓ = X^{-3/2}`, `ℓ = K_ℓ(μa)^{-1/2}`, FS `sec:params`, `eq:def_ell`) the
quotient `K_H·a/ℓ` is an explicit monomial in the diluteness:

  `K_H·a/ℓ = X^{-549/4}·X^{3/2}·a(μa)^{1/2} = X^{-549/4+3/2}·(μa³)^{1/2}
            = X^{-549/4+3/2+323/2} = X^{103/4} = (μa³)^{103/(4·323)}`

**exactly** — the chemical potential `μ` cancels (via `a(μa)^{1/2} = (μa³)^{1/2}`
and `μa³ = t`).  The statement below is therefore, exactly as for
`Work.BoseC3QAll.smallness_conj1`, the monotone comparison
`X ≤ τ ⟹ X^{103/4} ≤ τ^{103/4}` with `103/4 > 0`.  This is the quotient that
the small-box/`thm:Control3Q` estimates dominate by `τ^{103/4}`.

The proof only uses the scalar values of `Work.BoseB7.FSParamsVals`
(`Kl_val`, `KH_val`, `mu_pos`, `a_pos`) and the definition `side` of `ℓ`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

/-- **FS's parameter smallness, sixth instance.**  At FS's parameter point the
quotient `K_H·a/ℓ` equals `X^{103/4}` with `X = (μa³)^{1/323}`, so it is
dominated by `τ^{103/4}` as soon as `X ≤ τ`. -/
theorem smallness_conj6 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) {τ : ℝ}
    (hX : Work.BoseBox.fsXp hv.t 1 ≤ τ) :
    E.KH * E.aScat / E.ell ≤ τ ^ (103 / 4 : ℝ) := by
  have ht : 0 < hv.t := hv.t_pos
  have ha : 0 < E.aScat := hv.a_pos
  have hmu : 0 < E.mu := Work.BoseB7.mu_pos E hv
  have hμa : 0 < E.mu * E.aScat := mul_pos hmu ha
  -- FS `eq:def_ell`: `ℓ = K_ℓ(μa)^{-1/2}`
  have hell : E.ell = E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hv.ell_eq, Work.BoseB7.side]
  -- `√(μa)·a = √(μa³) = √t`
  have hsqrt : Real.sqrt (E.mu * E.aScat) * E.aScat = Real.sqrt hv.t := by
    calc Real.sqrt (E.mu * E.aScat) * E.aScat
        = Real.sqrt (E.mu * E.aScat) * Real.sqrt (E.aScat ^ 2) := by rw [Real.sqrt_sq ha.le]
      _ = Real.sqrt ((E.mu * E.aScat) * E.aScat ^ 2) := by rw [Real.sqrt_mul hμa.le]
      _ = Real.sqrt (E.mu * E.aScat ^ 3) := by congr 1; ring
      _ = Real.sqrt hv.t := by rw [hv.mu_eq]
  -- `(μa)^{-1/2} = (√(μa))⁻¹`
  have hpow : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (E.mu * E.aScat))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hμa.le]
  -- hence `a(μa)^{1/2} = √t`, i.e. `a/(μa)^{-1/2} = √t`: `μ` cancels
  have key : E.aScat / (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) = Real.sqrt hv.t := by
    rw [hpow, div_inv_eq_mul, mul_comm, hsqrt]
  -- split the quotient
  have hsplit : E.KH * E.aScat / E.ell
      = (E.KH / E.Kl) * (E.aScat / (E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) := by
    rw [hell, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- `K_H/K_ℓ = X^{-549/4+3/2} = X^{-543/4}`
  have hKH : E.KH / E.Kl = Work.BoseBox.fsXp hv.t (-(543 / 4)) := by
    rw [Work.BoseB7.KH_val E hv, Work.BoseB7.Kl_val E hv, div_eq_mul_inv, Work.BoseBox.fsXp_inv ht,
      Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  -- `√t = X^{323/2}`
  have hsqrtX : Real.sqrt hv.t = Work.BoseBox.fsXp hv.t (323 / 2) := by
    rw [Real.sqrt_eq_rpow]
    simp only [Work.BoseBox.fsXp]
    congr 1
    norm_num
  -- the whole quotient is `X^{103/4}`
  have hEq : E.KH * E.aScat / E.ell = Work.BoseBox.fsXp hv.t (103 / 4) := by
    rw [hsplit, hKH, key, hsqrtX, Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  calc E.KH * E.aScat / E.ell = Work.BoseBox.fsXp hv.t (103 / 4) := hEq
    _ ≤ τ ^ (103 / 4 : ℝ) := by
        have h1 : Work.BoseBox.fsXp hv.t (103 / 4)
            = (Work.BoseBox.fsXp hv.t 1) ^ (103 / 4 : ℝ) := by
          rw [Work.BoseBox.fsXp_rpow ht.le]
          congr 1
          ring
        rw [h1]
        exact Real.rpow_le_rpow (Work.BoseBox.fsXp_nonneg ht.le) hX (by norm_num)

end Work.BoseC3QAll
