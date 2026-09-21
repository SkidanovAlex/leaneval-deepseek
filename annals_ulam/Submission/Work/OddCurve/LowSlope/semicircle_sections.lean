import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs

/-!
# The section integrals of the semicircle

For the unit semicircle (`f = Work.OddEnvelope.semicircle t = √(1-t²)`, `x = y = profileX`) the
chord of slope `s` is the interval `(-c, c)` with `c = profileX s = (√(1+s²))⁻¹`, the radicand is
`rad0 semicircle s t = 1 - (1+s²)t²`, and the two section integrals are the ball's:

* `centIntegral n semicircle profileX profileX s = 0` (odd integrand on a symmetric interval);
* `(1+s²)^{3/2} · inertiaIntegral n semicircle profileX profileX s = ballInertiaConst n`
  (substitute `t = c u`).

These are the reference values of the low-slope step: `(cmass)` and `(i1)` for the ball.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

theorem semicircle_section_integrals (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    centIntegral n Work.OddEnvelope.semicircle Work.OddEnvelope.profileX
        Work.OddEnvelope.profileX s = 0 ∧
      (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
        inertiaIntegral n Work.OddEnvelope.semicircle Work.OddEnvelope.profileX
          Work.OddEnvelope.profileX s
        = ballInertiaConst n := by
  set c : ℝ := Work.OddEnvelope.profileX s with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcpos : 0 < c := by rw [hc, Work.OddEnvelope.profileX]; positivity
  have hclt : c < 1 := by
    rw [hc, Work.OddEnvelope.profileX, div_lt_one hspos]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [hs, sq_nonneg s])
  have hc2 : c ^ 2 * (1 + s ^ 2) = 1 := by
    rw [hc, Work.OddEnvelope.profileX]; field_simp; rw [Real.sq_sqrt (by positivity)]
  have hcueq : ∀ u : ℝ, (1 + s ^ 2) * (c * u) ^ 2 = u ^ 2 := by
    intro u
    calc (1 + s ^ 2) * (c * u) ^ 2 = (c ^ 2 * (1 + s ^ 2)) * u ^ 2 := by ring
      _ = u ^ 2 := by rw [hc2, one_mul]
  have hrad : ∀ t ∈ Set.uIcc (-c) c,
      rad0 Work.OddEnvelope.semicircle s t = 1 - (1 + s ^ 2) * t ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le (show -c ≤ c by linarith)] at ht
    have ht2 : t ^ 2 ≤ c ^ 2 := by nlinarith [ht.1, ht.2]
    have h1t : 0 ≤ 1 - t ^ 2 := by nlinarith [ht2, hclt, sq_nonneg t]
    rw [rad0, Work.OddEnvelope.semicircle, Real.sq_sqrt h1t]; ring
  have hcubic : (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) * c ^ 3 = 1 := by
    have hprodc : c * Real.sqrt (1 + s ^ 2) = 1 := by
      rw [hc, Work.OddEnvelope.profileX]
      exact div_mul_cancel₀ 1 (ne_of_gt hspos)
    have h1 : c ^ 3 * (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) = 1 := by
      rw [show c ^ 3 * (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) =
        (c ^ 2 * (1 + s ^ 2)) * (c * Real.sqrt (1 + s ^ 2)) from by ring]
      rw [hc2, hprodc, mul_one]
    rwa [show (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) * c ^ 3 =
      c ^ 3 * (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) from by ring]
  -- the two integrands of the chord integral
  set F : ℝ → ℝ := fun t => t * (1 - (1 + s ^ 2) * t ^ 2) ^ (n - 1) *
    Real.sqrt (1 - (1 + s ^ 2) * t ^ 2) with hF
  set G : ℝ → ℝ := fun t => t ^ 2 * (1 - (1 + s ^ 2) * t ^ 2) ^ (n - 1) *
    Real.sqrt (1 - (1 + s ^ 2) * t ^ 2) with hG
  have hcent : centIntegral n Work.OddEnvelope.semicircle Work.OddEnvelope.profileX
      Work.OddEnvelope.profileX s = ∫ t in (-c)..c, F t := by
    rw [centIntegral]
    exact intervalIntegral.integral_congr (fun t ht => by rw [hrad t ht])
  have hiner : inertiaIntegral n Work.OddEnvelope.semicircle Work.OddEnvelope.profileX
      Work.OddEnvelope.profileX s = ∫ t in (-c)..c, G t := by
    rw [inertiaIntegral]
    exact intervalIntegral.integral_congr (fun t ht => by rw [hrad t ht])
  -- oddness of `F`
  have hoddF : ∀ t : ℝ, F (-t) = - F t := by
    intro t
    have h1 : (1 - (1 + s ^ 2) * (-t) ^ 2) = (1 - (1 + s ^ 2) * t ^ 2) := by ring
    simp only [hF, h1]
    ring
  have hsym : (∫ t in (-c)..c, F (-t)) = ∫ t in (-c)..c, F t := by
    simpa using (intervalIntegral.integral_comp_neg (a := -c) (b := c) (f := F))
  have hneg : (∫ t in (-c)..c, F (-t)) = -(∫ t in (-c)..c, F t) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun t _ => hoddF t)
  have hFzero : (∫ t in (-c)..c, F t) = 0 := by linarith [hsym, hneg]
  -- the substitution for `G`
  have hcont : ContinuousOn (fun u : ℝ => c * u) (Set.uIcc (-1 : ℝ) 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => c * u) c x := by
    intro x _
    simpa using (hasDerivAt_id x).const_mul c
  have hnonneg : ∀ x ∈ Set.Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1), 0 ≤ (c : ℝ) :=
    fun x _ => le_of_lt hcpos
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (-1 : ℝ)) (b := 1) (f := fun u : ℝ => c * u) (f' := fun _ => c) (g := G)
    hcont hderiv hnonneg
  rw [show c * (-1) = -c from by ring, mul_one] at hsub
  have hinner : (∫ x in (-1 : ℝ)..1, (G ∘ fun u : ℝ => c * u) x) =
      c ^ 2 * ∫ u in (-1 : ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp only [Function.comp_apply, hG]
    have h1 : (1 - (1 + s ^ 2) * (c * u) ^ 2) = (1 - u ^ 2) := by rw [hcueq u]
    rw [h1]
    ring
  have hGval : (∫ t in (-c)..c, G t) = c ^ 3 * ballInertiaConst n := by
    rw [← hsub, intervalIntegral.integral_mul_const, hinner, ballInertiaConst]
    ring
  refine ⟨?_, ?_⟩
  · rw [hcent, hFzero]
  · rw [hiner, hGval]
    have h4 : (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) * (c ^ 3 * ballInertiaConst n) =
        ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2) * c ^ 3) * ballInertiaConst n := by ring
    rw [h4, hcubic, one_mul]

end

end Work.OddCurve.LowSlope
