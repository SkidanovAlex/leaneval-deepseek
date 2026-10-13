import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.FireFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `cos²θ · sin(2|θ|)^{γ-2}` against a radial indicator

This module proves `Work.FTS.FireFix.Clauses.PsiWt.integrableOn_cos_sq_sin_rpow`:
for `1 < γ ≤ 2` and `L ≥ 0` the function

  `(q : ℝ × ℝ) ↦ cos(q.2)² · sin(2|q.2|)^{γ-2} · 1_{q.1 ≤ L}`

is integrable on the half-strip `(0,∞) × (-π/2, π/2)`.

The function is a product of a one-variable `θ`-factor and the half-line indicator
`1_{(-∞,L]}`; the latter is integrable on `(0,∞)` because `(0,∞) ∩ (-∞,L] = (0,L]` has
finite Lebesgue measure.  The `θ`-factor has only the endpoint singularities of
`sin(2θ)^{γ-2}` at `0` and `±π/2`, both integrable since `-1 < γ - 2`; on the right half
we dominate it by `2^{γ-2} sin^{γ-2}θ` using the identity
`sin(2θ) = 2 sinθ cosθ` together with `cos^γ θ ≤ 1`, then dominate `sin^{γ-2}θ` by a
constant times `θ^{γ-2}` (`sin x ≥ (2/π)x`), and transfer to the left half by evenness.
-/

set_option linter.unusedVariables false

namespace Work.FTS.FireFix.Clauses.PsiWt

open MeasureTheory Set

/-! ### Two elementary integrability facts -/

/-- The indicator of a halfline `(-∞, L]` is integrable on `(0, ∞)`: it is the indicator
of `(0, L]`, a set of finite Lebesgue measure. -/
lemma integrableOn_ite_le_Ioi (L : ℝ) :
    IntegrableOn (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0) (Ioi (0 : ℝ)) := by
  have hEq : (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0)
      = (Iic L).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ≤ L <;> simp [hx]
  rw [hEq, integrableOn_indicator_iff measurableSet_Iic, Iic_inter_Ioi]
  refine integrableOn_const (C := (1 : ℝ)) ?_
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- `sin^r` is integrable on `(0, π/2)` when `-1 < r ≤ 0`: dominated by
`(2/π)^r θ^r` via `sin x ≥ (2/π) x`. -/
lemma integrableOn_sin_rpow_Ioo {r : ℝ} (hr : -1 < r) (hr0 : r ≤ 0) :
    IntegrableOn (fun θ : ℝ => Real.sin θ ^ r) (Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hdom : IntegrableOn (fun θ : ℝ => (2 / Real.pi) ^ r * θ ^ r)
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := r) (t := Real.pi / 2) hpi2).2 hr).const_mul _
  rw [IntegrableOn] at hdom ⊢
  refine hdom.mono' ?_ ?_
  · refine (ContinuousOn.rpow_const Real.continuous_sin.continuousOn ?_).aestronglyMeasurable
      measurableSet_Ioo
    intro x hx
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
      (by linarith [hx.2, Real.pi_pos])))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hsin_nonneg : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hbase : (0 : ℝ) < 2 / Real.pi * x :=
      mul_pos (by positivity) hx.1
    have hle : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx.1.le hx.2.le
    have h1 : Real.sin x ^ r ≤ (2 / Real.pi * x) ^ r :=
      Real.rpow_le_rpow_of_nonpos hbase hle hr0
    have h2 : (2 / Real.pi * x) ^ r = (2 / Real.pi) ^ r * x ^ r :=
      Real.mul_rpow (by positivity) hx.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsin_nonneg _)]
    exact h1.trans (le_of_eq h2)

/-! ### The `θ`-integrand on the right half `(0, π/2)` -/

/-- The bound `cos²θ · sin(2θ)^{γ-2} ≤ 2^{γ-2} sin^{γ-2}θ` for `θ ∈ (0, π/2)`, from
`sin(2θ) = 2 sinθ cosθ` and `cos^γ θ ≤ 1`. -/
lemma cos_sq_mul_sin_two_rpow_le {γ θ : ℝ} (hγ : 1 < γ)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.cos θ ^ 2 * Real.sin (2 * θ) ^ (γ - 2) ≤ (2 : ℝ) ^ (γ - 2) * Real.sin θ ^ (γ - 2) := by
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hgam0 : 0 ≤ γ := by linarith
  -- the `sin(2θ)^{γ-2}` factor, split into powers of `sin θ` and `cos θ`
  have e1 : Real.sin (2 * θ) ^ (γ - 2)
      = (2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ (γ - 2)) := by
    rw [Real.sin_two_mul,
      Real.mul_rpow (by linarith [hsin_pos] : (0 : ℝ) ≤ 2 * Real.sin θ) hcos_pos.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsin_pos.le]
    ring
  -- `cos²θ · cos^{γ-2}θ = cos^γ θ`
  have hC : Real.cos θ ^ 2 * Real.cos θ ^ (γ - 2) = Real.cos θ ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hcos_pos]
    rw [show (((2 : ℕ) : ℝ) + (γ - 2)) = γ by push_cast; ring]
  have key : Real.cos θ ^ 2 * Real.sin (2 * θ) ^ (γ - 2)
      = (2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ γ) := by
    rw [e1]
    calc Real.cos θ ^ 2 * ((2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ (γ - 2)))
        = (2 : ℝ) ^ (γ - 2)
            * (Real.sin θ ^ (γ - 2) * (Real.cos θ ^ 2 * Real.cos θ ^ (γ - 2))) := by ring
      _ = (2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ γ) := by rw [hC]
  rw [key]
  have hcos : Real.cos θ ^ γ ≤ 1 :=
    Real.rpow_le_one hcos_pos.le (Real.cos_le_one θ) hgam0
  have h1 : Real.sin θ ^ (γ - 2) * Real.cos θ ^ γ ≤ Real.sin θ ^ (γ - 2) := by
    simpa using mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg hsin_pos.le _)
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)

/-- **The `θ`-integrand is integrable on the right half.**  Domination by
`2^{γ-2} sin^{γ-2}θ` (whose exponent lies in `(-1, 0]` when `γ ≤ 2`). -/
lemma integrableOn_cos_sq_sin_two_rpow_Ioo {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * θ) ^ (γ - 2))
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hdom : IntegrableOn (fun θ : ℝ => (2 : ℝ) ^ (γ - 2) * Real.sin θ ^ (γ - 2))
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
    (integrableOn_sin_rpow_Ioo (r := γ - 2) (by linarith) (by linarith)).const_mul _
  rw [IntegrableOn] at hdom ⊢
  refine hdom.mono' ?_ ?_
  · refine ((Real.continuous_cos.continuousOn.pow 2).mul ?_).aestronglyMeasurable measurableSet_Ioo
    refine ContinuousOn.rpow_const
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos])))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hsin_nonneg : 0 ≤ Real.sin (2 * x) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg hsin_nonneg _))]
    exact cos_sq_mul_sin_two_rpow_le hγ hx

/-! ### The even `θ`-integrand on the full interval -/

/-- `H θ = cos²θ · sin(2|θ|)^{γ-2}` is integrable on `(0, π/2)` (where `|θ| = θ`). -/
lemma integrableOn_cos_sq_sin_abs_pos {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
  (integrableOn_cos_sq_sin_two_rpow_Ioo hγ hγ2).congr_fun
    (fun x hx => by simp only [abs_of_pos hx.1]) measurableSet_Ioo

/-- `H θ = cos²θ · sin(2|θ|)^{γ-2}` is integrable on `(-π/2, 0)`: `H` is even, so this is
the substitution `θ ↦ -θ` of the previous lemma. -/
lemma integrableOn_cos_sq_sin_abs_neg {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) 0) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hI : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2)) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hpi2.le).2
      (integrableOn_cos_sq_sin_abs_pos hγ hγ2)
  have h2 := (IntervalIntegrable.iff_comp_neg
    (f := fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
    (a := 0) (b := Real.pi / 2)).1 hI
  have h3 : IntervalIntegrable
      (fun x : ℝ => Real.cos (-x) ^ 2 * Real.sin (2 * |-x|) ^ (γ - 2)) volume
      (-(Real.pi / 2)) 0 := by
    simpa using h2.symm
  have h4 : IntegrableOn (fun x : ℝ => Real.cos (-x) ^ 2 * Real.sin (2 * |-x|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) 0) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (show -(Real.pi / 2) ≤ (0 : ℝ) by
      linarith [Real.pi_pos])).1 h3
  exact h4.congr_fun (fun x _ => by simp only [Real.cos_neg, abs_neg]) measurableSet_Ioo

/-- `H θ = cos²θ · sin(2|θ|)^{γ-2}` is integrable on the full interval `(-π/2, π/2)`. -/
lemma integrableOn_cos_sq_sin_abs_Ioo {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hsplit : Ioo (-(Real.pi / 2)) 0 ∪ {0} ∪ Ioo (0 : ℝ) (Real.pi / 2)
      = Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext x
    simp only [mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · rintro ((⟨h1, h2⟩ | h3) | ⟨h4, h5⟩)
      · exact ⟨h1, by linarith [Real.pi_pos]⟩
      · exact ⟨by rw [h3]; linarith [Real.pi_pos], by rw [h3]; linarith [Real.pi_pos]⟩
      · exact ⟨by linarith [Real.pi_pos], h5⟩
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h, h2⟩
  have h1 := integrableOn_cos_sq_sin_abs_neg hγ hγ2
  have h2 : IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      ({0} : Set ℝ) := IntegrableOn.of_measure_zero (by simp)
  have h3 := integrableOn_cos_sq_sin_abs_pos hγ hγ2
  rw [← hsplit]
  exact (h1.union h2).union h3

/-! ### The theorem -/

theorem integrableOn_cos_sq_sin_rpow {γ L : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Real.cos q.2) ^ 2 * (Real.sin (2 * |q.2|)) ^ (γ - 2)
        * (if q.1 ≤ L then (1 : ℝ) else 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hG : IntegrableOn (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0) (Ioi (0 : ℝ)) :=
    integrableOn_ite_le_Ioi L
  have hH : IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := integrableOn_cos_sq_sin_abs_Ioo hγ hγ2
  have hprod : IntegrableOn (fun q : ℝ × ℝ =>
      (if q.1 ≤ L then (1 : ℝ) else 0) * (Real.cos q.2 ^ 2 * Real.sin (2 * |q.2|) ^ (γ - 2)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    have h := hG.mul_prod hH
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  refine hprod.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro q hq
  ring

end Work.FTS.FireFix.Clauses.PsiWt
