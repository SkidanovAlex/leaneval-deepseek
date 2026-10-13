import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open MeasureTheory Set
open scoped Real

/-!
## Non-integrability of `cos θ^{-2} · sin(2θ)^{-η}` at the right endpoint `θ = π/2`

This is the divergence input for `Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`: near `θ = π/2`
the function `θ ↦ cos θ^{-2} · sin(2θ)^{-η}` behaves like
`(π/2 - θ)^{-2-η}`, whose integral over any right neighbourhood of `π/2` diverges because
`2 + η > 1`.

The three ingredients below are proved from scratch:

* `inv_sq_not_integrableOn_Ioo` — `u ↦ 1 / u ^ 2` is not integrable on `(0,t)`, `t > 0`
  (the case `s = -2` of `intervalIntegral.integrableOn_Ioo_rpow_iff`);
* `one_div_sq_le_sin_mul_sin` — the pointwise lower bound
  `1 / u ^ 2 ≤ sin u ^ (-2) · sin(2u) ^ (-η)` on `(0, π/2)` for `η ≥ 0`, from `Real.sin_le`
  and the antitonicity of `x ↦ x ^ (-η)` on `(0,1]`;
* `not_integrableOn_Ioo_sin_mul` — its consequence: `sin u ^ (-2) · sin(2u) ^ (-η)` is not
  integrable on `(0,t)`.

The theorem is then obtained by reflecting the right end `(a, π/2)` of the interval onto
`(0, π/2 - a)` with the substitution `u = π/2 - θ`, using
`IntervalIntegrable.comp_sub_left`; on that interval `cos θ = sin u` and `sin 2θ = sin 2u`.
-/

/-- `u ↦ 1 / u ^ 2` is not integrable on `(0, t)` for `t > 0`: this is the case `s = -2` of
`intervalIntegral.integrableOn_Ioo_rpow_iff`, together with `1 / u ^ 2 = u ^ (-2)`. -/
private theorem inv_sq_not_integrableOn_Ioo {t : ℝ} (ht : 0 < t) :
    ¬ MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Set.Ioo 0 t) := by
  intro h
  have h' : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ioo 0 t) := by
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioo
    simp only []
    rw [one_div, Real.rpow_neg (le_of_lt hu.1) 2]
    norm_num
  have h2 := (intervalIntegral.integrableOn_Ioo_rpow_iff ht).mp h'
  linarith

/-- Pointwise lower bound: on `(0, π/2)`, `1 / u ^ 2 ≤ sin u ^ (-2) · sin(2u) ^ (-η)` for
`η ≥ 0`.  Indeed `sin u ≤ u` gives `u ^ (-2) ≤ (sin u) ^ (-2)` (the exponent `-2` is `≤ 0`),
while `0 < sin(2u) ≤ 1` and `-η ≤ 0` give `sin(2u) ^ (-η) ≥ 1`. -/
private theorem one_div_sq_le_sin_mul_sin {η u : ℝ} (hη : 0 ≤ η)
    (hu : u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 / u ^ 2 ≤ (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η) := by
  have hu0 : 0 < u := hu.1
  have hult : u < Real.pi / 2 := hu.2
  have hsin_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos, hult])
  have hle : Real.sin u ≤ u := Real.sin_le hu0.le
  have h1 : u ^ (-2 : ℝ) ≤ (Real.sin u) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hsin_pos hle (by norm_num)
  have hu2 : 1 / u ^ 2 = u ^ (-2 : ℝ) := by
    rw [one_div, Real.rpow_neg hu0.le 2]; norm_num
  have h1' : 1 / u ^ 2 ≤ (Real.sin u) ^ (-2 : ℝ) := by rw [hu2]; exact h1
  have h2u0 : 0 < 2 * u := by linarith
  have h2ult : 2 * u < Real.pi := by linarith
  have hsin2_pos : 0 < Real.sin (2 * u) := Real.sin_pos_of_pos_of_lt_pi h2u0 h2ult
  have h2 : 1 ≤ (Real.sin (2 * u)) ^ (-η) := by
    have h := Real.rpow_le_rpow_of_nonpos hsin2_pos (Real.sin_le_one (2 * u))
      (by linarith : -η ≤ 0)
    rwa [Real.one_rpow] at h
  calc 1 / u ^ 2 = 1 / u ^ 2 * 1 := (mul_one _).symm
    _ ≤ (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η) :=
        mul_le_mul h1' h2 zero_le_one (le_of_lt (Real.rpow_pos_of_pos hsin_pos _))

/-- `u ↦ sin u ^ (-2) · sin(2u) ^ (-η)` is not integrable on `(0, t)`, `t > 0`, for `η ≥ 0`:
it dominates `1 / u ^ 2`, which is not integrable at `0`. -/
private theorem not_integrableOn_Ioo_sin_mul {η t : ℝ} (hη : 0 ≤ η) (ht : 0 < t) :
    ¬ MeasureTheory.IntegrableOn
        (fun u : ℝ => (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η))
        (Set.Ioo 0 t) := by
  intro h
  have hp : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have ht' : 0 < min t (Real.pi / 2) := lt_min ht hp
  have hmono : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η))
      (Set.Ioo 0 (min t (Real.pi / 2))) :=
    h.mono_set (Set.Ioo_subset_Ioo_right (min_le_left t (Real.pi / 2)))
  have hInt : MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u ^ 2)
      (Set.Ioo 0 (min t (Real.pi / 2))) := by
    refine hmono.mono' (measurable_const.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one (sq_nonneg u))]
    exact one_div_sq_le_sin_mul_sin hη ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_right _ _)⟩
  exact inv_sq_not_integrableOn_Ioo ht' hInt

/-- **`cos θ^{-2}·sin(2θ)^{-η}` is not integrable near `θ = π/2`.**  For `0 < a < π/2` and
`0 ≤ η < 1`, the function `θ ↦ cos θ^{-2}·sin(2θ)^{-η}` is not integrable on `(a, π/2)`.
Route: substitute `u = π/2 - θ` (so `cos θ = sin u`, `sin 2θ = sin(2u)`), apply
`intervalIntegral.integral_comp_sub_left` (or the `IntervalIntegrable`-level version), and dominate
`sin u^{-2}·sin(2u)^{-η} ≥ π^{-η}·u^{-2}` for `u ∈ (0, π/2)` using `Real.sin_le` and the
antitonicity of `x ↦ x^{-η}` on `(0,∞)`; then use
`intervalIntegral.integrableOn_Ioo_rpow_iff` (`u^{-2}` is not integrable at `0`).
Consumed by `Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem not_integrableOn_cos_sq_mul_sin_rpow {a η : ℝ} (ha : 0 < a) (ha' : a < Real.pi / 2)
    (hη : 0 ≤ η) (hη1 : η < 1) :
    ¬ MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.cos θ) ^ (-2 : ℝ) * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo a (Real.pi / 2)) := by
  have _ha : 0 < a := ha
  have _hη1 : η < 1 := hη1
  intro h
  -- `h` is an integral over `a..π/2`; reflect the right end onto `0..π/2 - a`
  have hII : IntervalIntegrable
      (fun θ : ℝ => (Real.cos θ) ^ (-2 : ℝ) * (Real.sin (2 * θ)) ^ (-η))
      volume a (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt ha')).mpr h
  have hII' : IntervalIntegrable
      (fun u : ℝ =>
        (Real.cos (Real.pi / 2 - u)) ^ (-2 : ℝ) * (Real.sin (2 * (Real.pi / 2 - u))) ^ (-η))
      volume (Real.pi / 2 - a) (Real.pi / 2 - Real.pi / 2) :=
    hII.comp_sub_left (Real.pi / 2)
  have hIIs : IntervalIntegrable
      (fun u : ℝ =>
        (Real.cos (Real.pi / 2 - u)) ^ (-2 : ℝ) * (Real.sin (2 * (Real.pi / 2 - u))) ^ (-η))
      volume 0 (Real.pi / 2 - a) := by
    simpa [sub_self] using hII'.symm
  have ht0 : (0 : ℝ) ≤ Real.pi / 2 - a := by linarith [ha']
  have hIoo : MeasureTheory.IntegrableOn
      (fun u : ℝ =>
        (Real.cos (Real.pi / 2 - u)) ^ (-2 : ℝ) * (Real.sin (2 * (Real.pi / 2 - u))) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2 - a)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht0).mp hIIs
  -- substitute `cos (π/2 - u) = sin u`, `sin (2 (π/2 - u)) = sin (2u)`
  have hIoo' : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Real.sin u) ^ (-2 : ℝ) * (Real.sin (2 * u)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2 - a)) := by
    refine hIoo.congr_fun (fun u _ => ?_) measurableSet_Ioo
    simp only []
    simp only [Real.cos_pi_div_two_sub]
    rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub]
  exact not_integrableOn_Ioo_sin_mul hη (by linarith [ha']) hIoo'

end Work.FTS_EllLimOK.ProducerH
