import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.paramsAt_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FamForm.sideAt_d_powers`

FS's parameter block at the concrete choice `paramsAt μ a = fsParams (μa³)`:

* the box side `ℓ = sideAt μ a = K_ℓ(μa)^{-1/2}` equals `a / s^{163}`;
* the dimensionless parameter `d` is the sixth power of `s`.

Both are pure rewritings in the monomial `fsXp t c = t^{c/323}`.  With the
diluteness `t = μa³`, FS's choice gives `s = t^{1/323}`, `d = t^{6/323}` and
`K_ℓ = t^{-3/646}`, so `d = s⁶` immediately, and

`K_ℓ (μa)^{-1/2} = t^{-3/646}·a·t^{-1/2} = a·t^{-163/323} = a/s^{163}`,

the middle step being `(μa)^{-1/2} = a·(μa³)^{-1/2}` (i.e. `μa = t/a²`).
-/

namespace Work.BoseFixR.FamForm

open scoped Real Topology BigOperators
open Work.BoseBox

/-- `(μa)^{-1/2} = a·(μa³)^{-1/2}` for `μ, a > 0`: the elementary rewriting that
converts the box side's `(μa)^{-1/2}` into powers of the diluteness `μa³`. -/
lemma inv_sqrt_mu_mul_a {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (μ * a) ^ (-(1/2 : ℝ)) = a * (μ * a^3) ^ (-(1/2 : ℝ)) := by
  have ht : 0 < μ * a^3 := by positivity
  have h : μ * a = (μ * a^3) / a^2 := by field_simp
  rw [h, Real.div_rpow (le_of_lt ht) (by positivity : (0:ℝ) ≤ a^2) (-(1/2:ℝ))]
  have ha2 : (a^2 : ℝ) ^ (-(1/2:ℝ)) = a⁻¹ := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    norm_num
    exact Real.rpow_neg_one a
  rw [ha2, div_inv_eq_mul]
  ring

/-- `s = (μa³)^{1/323}` at FS's parameters. -/
lemma paramsAt_s {μ a : ℝ} :
    (paramsAt μ a).s = (μ * a^3) ^ ((1:ℝ)/323) := by
  simp only [paramsAt, fsParams, fsXp]

/-- `d = (μa³)^{6/323}` at FS's parameters. -/
lemma paramsAt_d {μ a : ℝ} :
    (paramsAt μ a).d = (μ * a^3) ^ ((6:ℝ)/323) := by
  simp only [paramsAt, fsParams, fsXp]

/-- `K_ℓ = (μa³)^{-3/646}` at FS's parameters. -/
lemma paramsAt_Kl {μ a : ℝ} :
    (paramsAt μ a).Kl = (μ * a^3) ^ (-(3/646 : ℝ)) := by
  simp only [paramsAt, fsParams, fsXp]
  congr 1
  norm_num

/-- `((μa³)^{1/323})^{163} = (μa³)^{163/323}`. -/
lemma rpow_323_pow_163 {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (((μ * a^3) ^ (1/323:ℝ))^163) = (μ * a^3) ^ (163/323:ℝ) := by
  have ht : 0 < μ * a^3 := by positivity
  rw [← Real.rpow_natCast ((μ * a^3)^(1/323:ℝ)) 163, ← Real.rpow_mul ht.le]
  norm_num

/-- The box side as a monomial in the diluteness: `ℓ = a·(μa³)^{-163/323}`. -/
lemma sideAt_eq {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    sideAt μ a = a * (μ * a^3) ^ (-(163/323 : ℝ)) := by
  have ht : 0 < μ * a^3 := by positivity
  rw [sideAt, boxSide, paramsAt_Kl, inv_sqrt_mu_mul_a hμ ha]
  calc (μ * a^3) ^ (-(3/646:ℝ)) * (a * (μ * a^3) ^ (-(1/2:ℝ)))
      = a * ((μ * a^3) ^ (-(3/646:ℝ)) * (μ * a^3) ^ (-(1/2:ℝ))) := by ring
    _ = a * (μ * a^3) ^ ((-(3/646:ℝ)) + (-(1/2:ℝ))) := by rw [Real.rpow_add ht]
    _ = a * (μ * a^3) ^ (-(163/323:ℝ)) := by
          rw [show (-(3/646:ℝ)) + (-(1/2:ℝ)) = -(163/323) by norm_num]

theorem sideAt_d_powers {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseBox.sideAt μ a = a / (Work.BoseBox.paramsAt μ a).s ^ 163
      ∧ (Work.BoseBox.paramsAt μ a).d = (Work.BoseBox.paramsAt μ a).s ^ 6 := by
  have ht : 0 < μ * a^3 := by positivity
  refine ⟨?_, ?_⟩
  · have hp := rpow_323_pow_163 (μ := μ) (a := a) hμ ha
    calc sideAt μ a
        = a * (μ * a^3) ^ (-(163/323 : ℝ)) := sideAt_eq hμ ha
      _ = a * (((μ * a^3) ^ (163/323:ℝ))⁻¹) := by rw [Real.rpow_neg ht.le]
      _ = a * ((((μ * a^3) ^ (1/323:ℝ))^163)⁻¹) := by rw [hp]
      _ = a / (paramsAt μ a).s^163 := by rw [paramsAt_s, ← div_eq_mul_inv]
  · have h6 : (((μ * a^3) ^ (1/323:ℝ))^6) = (μ * a^3) ^ ((6:ℝ)/323) := by
      rw [← Real.rpow_natCast ((μ * a^3)^(1/323:ℝ)) 6, ← Real.rpow_mul ht.le]
      norm_num
    rw [paramsAt_d, paramsAt_s]
    exact h6.symm

end Work.BoseFixR.FamForm
