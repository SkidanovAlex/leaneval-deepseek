import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.StandardCurve.injOn_coprime
import Submission.Work.Distortion.length_diameter
import Submission.Work.Distortion.length_ge_twice_diam

/-!
# The distortion of the standard `(p,q)`-torus curve is at least `min p q / 160`

This file proves `Work.StandardCurve.distortion_bound`: if the curve of a smooth
knot `K` *is* (not merely is isotopic to) the explicit standard `(p,q)`-torus
curve `c_{p,q}` of `ChallengeDeps`, then

`(1/160 : ℝ≥0∞) * (min p q : ℝ≥0∞) ≤ distortion K`.

The estimate is very far from sharp for the standard parametrisation, and the
proof is elementary.  The ingredients are

* the total arclength of the curve is at least `4 * min p q`: on each of the
  `2p` parameter intervals `[kπ/p, (k+1)π/p]` the longitude angle `p t`
  advances by exactly `π`, so the two endpoints have *antipodal* projections to
  the `xy`-plane and their distance is at least the sum `(2 + cos φ) +
  (2 + cos φ') ≥ 2` of the two meridian radii.  Summing the fundamental
  estimate "chord ≤ arclength of the parameter interval"
  (`Work.Distortion.LengthGeTwiceDiam.dist_le_integral_speed`) over the `2p`
  intervals gives `4p ≤ totalArcLength K`, hence `4 min p q ≤ totalArcLength K`.
* the diameter of the image is at most `8`: every point of the standard torus of
  revolution with major radius `2` and minor radius `1` has norm at most `4`.
* `Work.Distortion.length_diameter`: the distortion of a closed curve is at
  least `length / (2 * diameter)` (the antipodal-arclength argument).

Putting these together, `distortion K ≥ (4 min p q) / 16 = min p q / 4`, and
`1/160 ≤ 1/4` gives the claim.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.StandardCurve

/-- **The half-period chord bound.**  Two points of the standard `(p,q)`-torus
curve whose parameters differ by `π/p` have antipodal projections on the
`xy`-plane, so their distance is at least the sum of the two meridian radii,
which is at least `2`. -/
lemma chord_ge_half_period (p q : ℕ) (hp : 0 < p) (t : ℝ) :
    2 ≤ dist (standardTorusCurve p q t)
      (standardTorusCurve p q (t + Real.pi / (p : ℝ))) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpa : (p : ℝ) * (t + Real.pi / (p : ℝ)) = (p : ℝ) * t + Real.pi := by
    field_simp
  have hnormsq : ‖standardTorusCurve p q t - standardTorusCurve p q (t + Real.pi / (p : ℝ))‖ ^ 2
      = ((2 + Real.cos ((q : ℝ) * t)) * Real.cos ((p : ℝ) * t)
          - (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))) * (-Real.cos ((p : ℝ) * t)))^2
      + ((2 + Real.cos ((q : ℝ) * t)) * Real.sin ((p : ℝ) * t)
          - (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))) * (-Real.sin ((p : ℝ) * t)))^2
      + (Real.sin ((q : ℝ) * t) - Real.sin ((q : ℝ) * (t + Real.pi / (p : ℝ))))^2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
    rw [curve_apply_zero, curve_apply_one, curve_apply_two,
        curve_apply_zero, curve_apply_one, curve_apply_two,
        hpa, Real.cos_add_pi, Real.sin_add_pi]
  have hkey : ((2 + Real.cos ((q : ℝ) * t)) * Real.cos ((p : ℝ) * t)
          - (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))) * (-Real.cos ((p : ℝ) * t)))^2
      + ((2 + Real.cos ((q : ℝ) * t)) * Real.sin ((p : ℝ) * t)
          - (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))) * (-Real.sin ((p : ℝ) * t)))^2
      = (2 + Real.cos ((q : ℝ) * t)
          + (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))))^2 := by
    linear_combination ((2 + Real.cos ((q : ℝ) * t)
        + (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))))^2)
      * Real.cos_sq_add_sin_sq ((p : ℝ) * t)
  have hbase : 2 ≤ 2 + Real.cos ((q : ℝ) * t)
      + (2 + Real.cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))) := by
    linarith [Real.neg_one_le_cos ((q : ℝ) * t),
      Real.neg_one_le_cos ((q : ℝ) * (t + Real.pi / (p : ℝ)))]
  have hbig : 4 ≤ ‖standardTorusCurve p q t
      - standardTorusCurve p q (t + Real.pi / (p : ℝ))‖ ^ 2 := by
    rw [hnormsq, hkey]
    nlinarith [sq_nonneg (Real.sin ((q : ℝ) * t)
      - Real.sin ((q : ℝ) * (t + Real.pi / (p : ℝ))))]
  have hnn := norm_nonneg (standardTorusCurve p q t
    - standardTorusCurve p q (t + Real.pi / (p : ℝ)))
  rw [dist_eq_norm]
  nlinarith [hbig, hnn]

/-- Every point of the standard torus of revolution with major radius `2` and
minor radius `1` has norm at most `4`. -/
lemma norm_standardTorusCurve_le (p q : ℕ) (t : ℝ) :
    ‖standardTorusCurve p q t‖ ≤ 4 := by
  have hsq : ‖standardTorusCurve p q t‖ ^ 2
      = (2 + Real.cos ((q : ℝ) * t))^2 + Real.sin ((q : ℝ) * t)^2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [curve_apply_zero, curve_apply_one, curve_apply_two]
    linear_combination ((2 + Real.cos ((q : ℝ) * t))^2) * Real.cos_sq_add_sin_sq ((p : ℝ) * t)
  have h1 : (2 + Real.cos ((q : ℝ) * t))^2 ≤ 9 := by
    nlinarith [Real.neg_one_le_cos ((q : ℝ) * t), Real.cos_le_one ((q : ℝ) * t)]
  have h2 : Real.sin ((q : ℝ) * t)^2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin ((q : ℝ) * t), Real.sin_le_one ((q : ℝ) * t)]
  have h3 : ‖standardTorusCurve p q t‖^2 ≤ 16 := by rw [hsq]; linarith
  nlinarith [norm_nonneg (standardTorusCurve p q t)]

/-- Two points of the standard `(p,q)`-torus curve are at distance at most `8`. -/
lemma dist_standard_le_eight (p q : ℕ) (s t : ℝ) :
    dist (standardTorusCurve p q s) (standardTorusCurve p q t) ≤ 8 := by
  rw [dist_eq_norm]
  calc ‖standardTorusCurve p q s - standardTorusCurve p q t‖
      ≤ ‖standardTorusCurve p q s‖ + ‖standardTorusCurve p q t‖ := norm_sub_le _ _
    _ ≤ 4 + 4 := add_le_add (norm_standardTorusCurve_le p q s) (norm_standardTorusCurve_le p q t)
    _ = 8 := by norm_num

/-- **The length bound.**  A knot whose curve is the standard `(p,q)`-torus
curve has total arclength at least `4p`. -/
lemma four_mul_le_totalArcLength (p q : ℕ) (hp : 0 < p) (K : Knot)
    (hK : ∀ t, K.curve t = standardTorusCurve p q t) :
    4 * (p : ℝ) ≤ totalArcLength K := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hδpos : (0 : ℝ) < Real.pi / (p : ℝ) := by positivity
  have hscont : Continuous (speed K) := Work.Distortion.LengthGeTwiceDiam.continuous_speed K
  have hkey : ∀ n : ℕ,
      2 * (n : ℝ) ≤ ∫ x in (0 : ℝ)..((n : ℝ) * (Real.pi / (p : ℝ))), speed K x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [add_mul, one_mul]
      have hle : (n : ℝ) * (Real.pi / (p : ℝ))
          ≤ (n : ℝ) * (Real.pi / (p : ℝ)) + Real.pi / (p : ℝ) := by linarith
      have hdist := Work.Distortion.LengthGeTwiceDiam.dist_le_integral_speed K hle
      rw [hK ((n : ℝ) * (Real.pi / (p : ℝ))),
        hK ((n : ℝ) * (Real.pi / (p : ℝ)) + Real.pi / (p : ℝ))] at hdist
      have hchord : 2 ≤ dist (standardTorusCurve p q ((n : ℝ) * (Real.pi / (p : ℝ))))
          (standardTorusCurve p q ((n : ℝ) * (Real.pi / (p : ℝ)) + Real.pi / (p : ℝ))) :=
        chord_ge_half_period p q hp _
      have hint := intervalIntegral.integral_add_adjacent_intervals
        (hscont.intervalIntegrable (μ := volume) (0 : ℝ) ((n : ℝ) * (Real.pi / (p : ℝ))))
        (hscont.intervalIntegrable (μ := volume) ((n : ℝ) * (Real.pi / (p : ℝ)))
          ((n : ℝ) * (Real.pi / (p : ℝ)) + Real.pi / (p : ℝ)))
      linarith
  have h2p := hkey (2 * p)
  have h2peq : ((2 * p : ℕ) : ℝ) * (Real.pi / (p : ℝ)) = 2 * Real.pi := by
    push_cast
    field_simp
  have h4 : 2 * (((2 * p : ℕ)) : ℝ) = 4 * (p : ℝ) := by push_cast; ring
  rw [h2peq, h4] at h2p
  have htot : totalArcLength K = ∫ x in (0 : ℝ)..2 * Real.pi, speed K x :=
    Work.Distortion.LengthGeTwiceDiam.totalArcLength_eq_integral K
  rw [htot]
  exact h2p

/-- The image of a knot whose curve is the standard `(p,q)`-torus curve is
bounded. -/
lemma isBounded_range (p q : ℕ) (K : Knot)
    (hK : ∀ t, K.curve t = standardTorusCurve p q t) :
    Bornology.IsBounded (Set.range K.curve) := by
  rw [Metric.isBounded_range_iff]
  exact ⟨8, fun s t => by rw [hK s, hK t]; exact dist_standard_le_eight p q s t⟩

/-- The diameter of the image of the standard `(p,q)`-torus curve is at
most `8`. -/
lemma diam_le_eight (p q : ℕ) (K : Knot)
    (hK : ∀ t, K.curve t = standardTorusCurve p q t) :
    Metric.diam (Set.range K.curve) ≤ 8 := by
  refine Metric.diam_le_of_forall_dist_le (by norm_num) ?_
  rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩
  rw [hK s, hK t]
  exact dist_standard_le_eight p q s t

/-- The diameter of the image of the standard `(p,q)`-torus curve is
positive: the points with parameters `0` and `π/(2q)` differ in their third
coordinate by `1`. -/
lemma diam_pos (p q : ℕ) (hq : 0 < q) (K : Knot)
    (hK : ∀ t, K.curve t = standardTorusCurve p q t) :
    0 < Metric.diam (Set.range K.curve) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hbdd := isBounded_range p q K hK
  set t₁ : ℝ := Real.pi / (2 * (q : ℝ)) with ht₁
  have hcoord : (K.curve 0 - K.curve t₁) 2 = -1 := by
    rw [hK 0, hK t₁]
    simp only [PiLp.sub_apply, curve_apply_two]
    have he : (q : ℝ) * t₁ = Real.pi / 2 := by rw [ht₁]; field_simp
    rw [he, Real.sin_pi_div_two, mul_zero, Real.sin_zero]
    ring
  have hnorm := PiLp.norm_apply_le (x := K.curve 0 - K.curve t₁) 2
  rw [Real.norm_eq_abs, hcoord, abs_neg, abs_one] at hnorm
  have hdist : (1 : ℝ) ≤ dist (K.curve 0) (K.curve t₁) := by
    rw [dist_eq_norm]; exact hnorm
  have hmem0 : K.curve 0 ∈ Set.range K.curve := ⟨0, rfl⟩
  have hmem1 : K.curve t₁ ∈ Set.range K.curve := ⟨t₁, rfl⟩
  have := Metric.dist_le_diam_of_mem hbdd hmem0 hmem1
  linarith

/-- The key real inequality: `min p q / 160 ≤ length / (2 * diameter)` for a
knot carrying the standard `(p,q)` curve. -/
lemma real_bound (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (K : Knot)
    (hK : ∀ t, K.curve t = standardTorusCurve p q t) :
    (1 / 160 : ℝ) * (Nat.min p q : ℝ)
      ≤ totalArcLength K / (2 * Metric.diam (Set.range K.curve)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hL : 4 * (p : ℝ) ≤ totalArcLength K := four_mul_le_totalArcLength p q hp K hK
  have hD8 : Metric.diam (Set.range K.curve) ≤ 8 := diam_le_eight p q K hK
  have hDpos : 0 < Metric.diam (Set.range K.curve) := diam_pos p q hq K hK
  have hm : (Nat.min p q : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.min_le_left p q
  have hcomp : 4 * (p : ℝ) / 16
      ≤ totalArcLength K / (2 * Metric.diam (Set.range K.curve)) := by
    refine div_le_div₀ (by linarith) hL (by linarith) (by linarith)
  have h1 : (1 / 160 : ℝ) * (Nat.min p q : ℝ) ≤ (1 / 160 : ℝ) * (p : ℝ) :=
    mul_le_mul_of_nonneg_left hm (by norm_num)
  have h2 : (1 / 160 : ℝ) * (p : ℝ) ≤ 4 * (p : ℝ) / 16 := by nlinarith
  linarith

/-- The conversion of the real inequality into `ℝ≥0∞`. -/
lemma ennreal_bound (p q : ℕ) (m : ℝ)
    (h : (1 / 160 : ℝ) * (Nat.min p q : ℝ) ≤ m) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ ENNReal.ofReal m := by
  have h160 : ENNReal.ofReal (1 / 160 : ℝ) = (1 / 160 : ℝ≥0∞) := by
    rw [show (1 / 160 : ℝ) = (160 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 160)]
    rw [show ENNReal.ofReal (160 : ℝ) = (160 : ℝ≥0∞) from ENNReal.ofReal_natCast 160,
      one_div]
  have hA : (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞)
      = ENNReal.ofReal ((1 / 160 : ℝ) * (Nat.min p q : ℝ)) := by
    rw [← h160, ← ENNReal.ofReal_natCast (Nat.min p q),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 160)]
  rw [hA]
  exact ENNReal.ofReal_le_ofReal h

theorem distortion_bound (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (hK : ∀ t, K.curve t = LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q t) :
    (1 / 160 : ENNReal) * (Nat.min p q : ENNReal) ≤
      LeanEval.KnotTheory.PardonDistortion.distortion K := by
  have h1 : (1 / 160 : ENNReal) * (Nat.min p q : ENNReal)
      ≤ ENNReal.ofReal (totalArcLength K / (2 * Metric.diam (Set.range K.curve))) :=
    ennreal_bound p q _ (real_bound p q hp hq K hK)
  exact le_trans h1 (Work.Distortion.length_diameter K)

end Work.StandardCurve
