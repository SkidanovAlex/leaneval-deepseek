import Mathlib
import Submission.Work.Core.Torus

/-!
# The length of a closed curve is at least twice its diameter

For a closed (periodic) curve `γ` with parameter interval `[0, 2π]`, every two points of the
curve bound two arcs whose lengths `d₁`, `d₂` add up to the total length `L`.  Both arcs are at
least as long as the Euclidean distance of their endpoints, so each of those distances is at most
`min (d₁, d₂) ≤ L / 2`.  Hence `2 * diam (range γ) ≤ L`.

The main content is the elementary estimate `dist (γ a) (γ b) ≤ ∫ u in a..b, ‖γ' u‖` (the
fundamental theorem of calculus plus the triangle inequality for integrals), together with the
periodicity of the speed `‖γ'‖`, which lets us shift the interval of integration by whole periods.
-/

namespace Work.Distortion

open LeanEval.KnotTheory.PardonDistortion
open Set MeasureTheory
open scoped ENNReal

namespace LengthGeTwiceDiam

/-- The speed `‖γ'‖` of a `2π`-periodic curve is again `2π`-periodic. -/
lemma speed_periodic (K : Knot) : Function.Periodic (speed K) (2 * Real.pi) := by
  intro x
  unfold speed
  rw [← deriv_comp_add_const (f := K.curve) (a := 2 * Real.pi),
    show (fun y : ℝ => K.curve (y + 2 * Real.pi)) = K.curve from funext K.periodic]

/-- The speed of a smooth knot is continuous. -/
lemma continuous_speed (K : Knot) : Continuous (speed K) := by
  unfold speed
  exact (K.smooth.continuous_deriv (by simp)).norm

/-- The total arclength is the (nonnegative) integral of the speed over one period. -/
lemma totalArcLength_eq_integral (K : Knot) :
    totalArcLength K = ∫ u in 0..2 * Real.pi, speed K u := by
  rw [totalArcLength, parameterArcLength, abs_of_nonneg]
  exact intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun u _ => norm_nonneg _)

/-- The total arclength is nonnegative. -/
lemma totalArcLength_nonneg (K : Knot) : 0 ≤ totalArcLength K := by
  rw [totalArcLength, parameterArcLength]
  exact abs_nonneg _

/-- The integral of the speed over any full period equals the total arclength. -/
lemma integral_speed_period (K : Knot) (s : ℝ) :
    ∫ u in s..s + 2 * Real.pi, speed K u = totalArcLength K := by
  rw [(speed_periodic K).intervalIntegral_add_eq s 0, zero_add, totalArcLength_eq_integral]

/-- Fundamental estimate: the Euclidean distance of two points of the curve is at most the
arclength of the parameter interval between them. -/
lemma dist_le_integral_speed (K : Knot) {a b : ℝ} (hab : a ≤ b) :
    dist (K.curve a) (K.curve b) ≤ ∫ u in a..b, speed K u := by
  have hint : IntervalIntegrable (fun u => deriv K.curve u) volume a b :=
    (K.smooth.continuous_deriv (by simp)).intervalIntegrable a b
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt K.curve (deriv K.curve x) x :=
    fun x _ => (K.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hkey : ∫ u in a..b, deriv K.curve u = K.curve b - K.curve a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc dist (K.curve a) (K.curve b)
      = ‖K.curve b - K.curve a‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ = ‖∫ u in a..b, deriv K.curve u‖ := by rw [hkey]
    _ ≤ ∫ u in a..b, ‖deriv K.curve u‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ u in a..b, speed K u := rfl

/-- Every point of a `2π`-periodic curve occurs with a parameter in the fundamental interval
`[0, 2π)`. -/
lemma range_curve_eq_image_Ico (K : Knot) :
    Set.range K.curve = K.curve '' Set.Ico 0 (2 * Real.pi) := by
  have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  apply Set.Subset.antisymm
  · rintro x ⟨s, rfl⟩
    obtain ⟨n, hn, _⟩ := existsUnique_add_zsmul_mem_Ico (a := 2 * Real.pi)
      (by linarith [Real.pi_pos]) s 0
    exact ⟨s + n • (2 * Real.pi), by rw [zero_add] at hn; exact hn, hper.zsmul n s⟩
  · exact Set.image_subset_range _ _

/-- For two parameters `s ≤ t` of the fundamental interval, the two complementary arcs of the
curve have lengths `∫ u in s..t, speed` and `∫ u in t..s + 2π, speed`, which add up to the total
arclength; the distance of the two points is bounded by both of them. -/
lemma dist_le_half_of_le (K : Knot) {s t : ℝ} (hs : s ∈ Set.Ico 0 (2 * Real.pi))
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (hst : s ≤ t) :
    dist (K.curve s) (K.curve t) ≤ totalArcLength K / 2 := by
  have hlt : t ≤ s + 2 * Real.pi := by linarith [ht.2, hs.1]
  have h1 : dist (K.curve s) (K.curve t) ≤ ∫ u in s..t, speed K u := dist_le_integral_speed K hst
  have h2 : dist (K.curve s) (K.curve t) ≤ ∫ u in t..(s + 2 * Real.pi), speed K u := by
    have h3 := dist_le_integral_speed K hlt
    rw [K.periodic s, dist_comm] at h3
    exact h3
  have hsum : (∫ u in s..t, speed K u) + ∫ u in t..(s + 2 * Real.pi), speed K u
      = totalArcLength K := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      ((continuous_speed K).intervalIntegrable s t) ((continuous_speed K).intervalIntegrable t _),
      integral_speed_period]
  linarith

end LengthGeTwiceDiam

open LengthGeTwiceDiam

/-- The total arclength of a closed curve is at least twice its diameter. -/
theorem length_ge_twice_diam (K : LeanEval.KnotTheory.PardonDistortion.Knot) :
    2 * Metric.diam (Set.range K.curve) ≤ LeanEval.KnotTheory.PardonDistortion.totalArcLength K := by
  have hdiam : Metric.diam (Set.range K.curve) ≤ totalArcLength K / 2 := by
    rw [range_curve_eq_image_Ico K]
    refine Metric.diam_le_of_forall_dist_le (by linarith [totalArcLength_nonneg K]) ?_
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    rcases le_total s t with h | h
    · exact dist_le_half_of_le K hs ht h
    · rw [dist_comm]; exact dist_le_half_of_le K ht hs h
  linarith

end Work.Distortion
