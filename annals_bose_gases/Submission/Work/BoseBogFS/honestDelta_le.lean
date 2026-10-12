import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.honestKAP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

set_option linter.unusedVariables false

/-!
# `Work.BoseBogFS.honestDelta_le` — the honest `δ` is `O(dil·(R/a)²)`

`honestDelta v μ R C ρ = 4(2C(R/ℓ)² + 8192 μ (a v)³ (R/a v)²)` with `ℓ = ell v μ`, so the target
is the elementary consequence of the two monomial identities

* `(R/ℓ)² = R²·μ(a v)/K_ℓ²` and `K_ℓ = (μ(a v)³)^{-3/646} ≥ 1` (the hypothesis `hKl`), so
  `(R/ℓ)² ≤ R²·μ(a v) = dil(v,μ)·(R/a v)²`;
* `8192·max 0 μ·(a v)³·(R/a v)² = 8192·dil(v,μ)·(R/a v)²` for `μ ≥ 0`.

Both are pure real arithmetic; `hKl` also forces `μ ≠ 0`, which is what makes `(R/ℓ)²` finite.
-/

/-- The elementary rpow/algebra core: for `ℓ = Kl·m^{-1/2}` with `Kl ≥ 1` and `m > 0`,
`(R/ℓ)² ≤ R²·m`.  (In the application `m = μ·a v` and `Kl = K_ℓ = (μ(a v)³)^{-3/646}`.) -/
private lemma div_sq_le_mul {R Kl m : ℝ} (hKl : 1 ≤ Kl) (hm : 0 < m) :
    (R / (Kl * m ^ (-(1/2) : ℝ))) ^ 2 ≤ R ^ 2 * m := by
  -- `u := m^{-1/2}` satisfies `u² = m⁻¹`
  have hu2 : (m ^ (-(1/2) : ℝ)) ^ 2 = m⁻¹ := by
    rw [← Real.rpow_natCast (m ^ (-(1/2) : ℝ)) 2, ← Real.rpow_mul hm.le]
    norm_num
    exact Real.rpow_neg_one m
  have hKl2 : 1 ≤ Kl ^ 2 := by nlinarith [hKl, sq_nonneg (Kl - 1)]
  rw [div_pow, mul_pow, hu2]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Kl ^ 2 * m⁻¹)]
  rw [show R ^ 2 * m * (Kl ^ 2 * m⁻¹) = R ^ 2 * Kl ^ 2 by field_simp]
  calc R ^ 2 = R ^ 2 * 1 := by ring
    _ ≤ R ^ 2 * Kl ^ 2 := mul_le_mul_of_nonneg_left hKl2 (sq_nonneg R)

theorem honestDelta_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R C μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hKl : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl) :
    Work.BoseBogFS.honestDelta v μ R C ρ
      ≤ 4 * (2 * C + 8192) * Work.BoseFixR.dil v μ * (R / _root_.BoseGases.a v) ^ 2 := by
  -- `μ = 0` is excluded by `hKl` (all parameters of `fsParams 0` vanish)
  have hμpos : 0 < μ := by
    rcases lt_or_eq_of_le hμ with h | h
    · exact h
    · exfalso
      have hKleq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 646) : ℝ) := by
        simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
        norm_num
      rw [← h] at hKl hKleq
      rw [hKleq] at hKl
      rw [zero_mul, Real.zero_rpow (by norm_num)] at hKl
      norm_num at hKl
  -- the box side is `K_ℓ·(μa)^{-1/2}` by definition
  have hell : Work.BoseFixR.ell v μ
      = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (μ * _root_.BoseGases.a v) ^ (-(1/2) : ℝ) := rfl
  -- `(R/ℓ)² ≤ R²·μa`
  have hkey : (R / Work.BoseFixR.ell v μ) ^ 2 ≤ R ^ 2 * (μ * _root_.BoseGases.a v) := by
    rw [hell]
    exact div_sq_le_mul hKl (by positivity)
  -- `R²·μa = dil(v,μ)·(R/a v)²`
  have hdil : R ^ 2 * (μ * _root_.BoseGases.a v)
      = Work.BoseFixR.dil v μ * (R / _root_.BoseGases.a v) ^ 2 := by
    rw [Work.BoseFixR.dil]
    field_simp
  rw [Work.BoseBogFS.honestDelta, Work.BoseBogFS.honestDW, Work.BoseBogFS.honestDD]
  rw [max_eq_right hμ]
  have hL : 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2
      ≤ 2 * C * (Work.BoseFixR.dil v μ * (R / _root_.BoseGases.a v) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [← hdil]
    exact hkey
  have hD : (8192 : ℝ) * μ * (_root_.BoseGases.a v) ^ 3 * (R / _root_.BoseGases.a v) ^ 2
      = 8192 * (Work.BoseFixR.dil v μ * (R / _root_.BoseGases.a v) ^ 2) := by
    rw [Work.BoseFixR.dil]
    ring
  rw [hD]
  nlinarith [hL]

end Work.BoseBogFS
