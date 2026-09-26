import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.Coarea
import Submission.Work.Sweep.SqDist.hasDerivAt_sqDist

/-!
# The coarea formula for the spheres of a concentric family

This file applies the abstract one-dimensional coarea inequality
(`Submission.Work.Sweep.Coarea`) to the distance function along the knot, giving
the integral-geometric estimate underlying the sweep argument:

* `lintegral_sphereCount_le`: the integral over `r ∈ [R/2, R]` of the number of
  intersections of the knot with the sphere of radius `r` centred at `x` is at
  most the arclength of the portion of the knot inside the closed ball of radius
  `R` about `x`.

The distance function is not differentiable at a point of the curve where it
meets the centre `x`, so the coarea formula is applied to the *squared* distance
along the curve, which is smooth; the change of variables `y = r²` (a monotone
substitution, `Real.sqrt`) converts the level integral over `y` into the integral
over the radii `r`.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

/-- The squared distance from the point `x` along the curve. -/
def sqDist (K : Knot) (x : R3) (t : ℝ) : ℝ := ‖K.curve t - x‖ ^ 2

/-- The derivative of the squared distance along the curve. -/
def sqDistDeriv (K : Knot) (x : R3) (t : ℝ) : ℝ :=
  2 * inner ℝ (K.curve t - x) (deriv K.curve t)

/-- The squared distance along the curve is differentiable everywhere, with the
derivative `sqDistDeriv`. -/
lemma sqDist_hasDerivAt (K : Knot) (x : R3) (t : ℝ) :
    HasDerivAt (sqDist K x) (sqDistDeriv K x t) t :=
  SqDist.hasDerivAt_sqDist K x t

/-- The derivative of the squared distance is continuous. -/
lemma sqDist_continuousOn_deriv (K : Knot) (x : R3) :
    ContinuousOn (sqDistDeriv K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  have h : Continuous (fun t : ℝ => inner ℝ (K.curve t - x) (deriv K.curve t)) :=
    (K.smooth.continuous.sub continuous_const).inner
      (K.smooth.continuous_deriv (by simp))
  exact (continuous_const.mul h).continuousOn

/-- The squared distance is the square of the distance to `x`. -/
lemma sqDist_eq_dist_sq (K : Knot) (x : R3) (t : ℝ) :
    sqDist K x t = dist (K.curve t) x ^ 2 := by
  rw [sqDist, dist_eq_norm]

/-- The level set of the squared distance at the positive level `r ^ 2` is the
intersection of the curve with the sphere of radius `r`. -/
lemma levelCount_sqDist_eq_sphereCount (K : Knot) (x : R3) {r : ℝ} (hr : 0 < r) :
    levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) (r ^ 2) = sphereCount K x r := by
  have hset : (Set.Icc (0 : ℝ) (2 * Real.pi) ∩ (sqDist K x) ⁻¹' {r ^ 2}) =
      (Set.Icc (0 : ℝ) (2 * Real.pi) ∩ K.curve ⁻¹' Metric.sphere x r) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ht, hsq⟩
      rw [sqDist_eq_dist_sq] at hsq
      refine ⟨ht, ?_⟩
      rw [Metric.mem_sphere]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · exact absurd (h ▸ dist_nonneg : (0:ℝ) ≤ -r) (by linarith)
    · rintro ⟨ht, hd⟩
      rw [Metric.mem_sphere] at hd
      exact ⟨ht, by rw [sqDist_eq_dist_sq, hd]⟩
  unfold levelCount sphereCount sphereParamSet
  rw [hset, Set.inter_comm]

/-- The pointwise estimate which turns the coarea formula for the squared
distance into the arclength estimate: the derivative of the squared distance,
weighted by `1 / (2 √(squared distance))`, is at most the speed. -/
lemma sqDistDeriv_mul_inv_sqrt_le (K : Knot) (x : R3) (t : ℝ) :
    ENNReal.ofReal |sqDistDeriv K x t| *
      (ENNReal.ofReal (2 * Real.sqrt (sqDist K x t)))⁻¹ ≤ ENNReal.ofReal (speed K t) := by
  by_cases h0 : K.curve t - x = 0
  · have hsq : sqDist K x t = 0 := by simp [sqDist, h0]
    have hder : sqDistDeriv K x t = 0 := by simp [sqDistDeriv, h0]
    rw [hsq, hder]
    simp
  · have hpos : (0:ℝ) < ‖K.curve t - x‖ := norm_pos_iff.mpr h0
    have hsqrt : Real.sqrt (sqDist K x t) = ‖K.curve t - x‖ := by
      rw [sqDist, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hbound : |sqDistDeriv K x t| * (2 * ‖K.curve t - x‖)⁻¹ ≤ speed K t := by
      have hcs := abs_real_inner_le_norm (K.curve t - x) (deriv K.curve t)
      rw [sqDistDeriv, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      calc 2 * |inner ℝ (K.curve t - x) (deriv K.curve t)| * (2 * ‖K.curve t - x‖)⁻¹
          = |inner ℝ (K.curve t - x) (deriv K.curve t)| * ‖K.curve t - x‖⁻¹ := by
            field_simp
        _ ≤ (‖K.curve t - x‖ * speed K t) * ‖K.curve t - x‖⁻¹ :=
            mul_le_mul_of_nonneg_right hcs (by positivity)
        _ = speed K t := by
            rw [mul_comm (‖K.curve t - x‖) (speed K t), mul_assoc,
              mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
    rw [hsqrt]
    have heq : ENNReal.ofReal |sqDistDeriv K x t| *
        (ENNReal.ofReal (2 * ‖K.curve t - x‖))⁻¹ =
        ENNReal.ofReal (|sqDistDeriv K x t| * (2 * ‖K.curve t - x‖)⁻¹) := by
      have h1 : ENNReal.ofReal (|sqDistDeriv K x t| * (2 * ‖K.curve t - x‖)⁻¹) =
          ENNReal.ofReal |sqDistDeriv K x t| *
            ENNReal.ofReal ((2 * ‖K.curve t - x‖)⁻¹) :=
        ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ |sqDistDeriv K x t|)
      have h2 : ENNReal.ofReal ((2 * ‖K.curve t - x‖)⁻¹) =
          (ENNReal.ofReal (2 * ‖K.curve t - x‖))⁻¹ :=
        ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < 2 * ‖K.curve t - x‖)
      rw [h1, h2]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal hbound

/-- The interval `[R²/4, R²]` of squared radii is the image of `[R/2, R]` under
squaring. -/
lemma image_sq_Icc {R : ℝ} (hR : 0 < R) :
    (fun r : ℝ => r ^ 2) '' Set.Icc (R / 2) R = Set.Icc (R ^ 2 / 4) (R ^ 2) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := mul_self_le_mul_self (show (0:ℝ) ≤ R / 2 by positivity) hr.1
      nlinarith [h]
    · have h := mul_self_le_mul_self (show (0:ℝ) ≤ r by linarith [hr.1, hR]) hr.2
      nlinarith [h]
  · rintro ⟨hy1, hy2⟩
    have hy0 : (0:ℝ) ≤ y := by
      have h : (0:ℝ) < R ^ 2 / 4 := by positivity
      linarith [hy1, h]
    refine ⟨Real.sqrt y, ⟨?_, ?_⟩, ?_⟩
    · refine (Real.le_sqrt (x := R / 2) (by positivity) hy0).mpr ?_
      nlinarith [hy1]
    · exact Real.sqrt_le_iff.mpr ⟨le_of_lt hR, hy2⟩
    · exact Real.sq_sqrt hy0

/-- The interval `[R/2, R]` of radii is the image of `[R²/4, R²]` under the square
root. -/
lemma image_sqrt_Icc {R : ℝ} (hR : 0 < R) :
    Real.sqrt '' Set.Icc (R ^ 2 / 4) (R ^ 2) = Set.Icc (R / 2) R := by
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : (0:ℝ) ≤ y := by
      have h : (0:ℝ) < R ^ 2 / 4 := by positivity
      linarith [hy.1, h]
    refine ⟨?_, ?_⟩
    · refine (Real.le_sqrt (x := R / 2) (by positivity) hy0).mpr ?_
      nlinarith [hy.1]
    · exact Real.sqrt_le_iff.mpr ⟨le_of_lt hR, hy.2⟩
  · rintro ⟨hr1, hr2⟩
    have hr0 : (0:ℝ) ≤ r := by linarith [hr1, hR]
    refine ⟨r ^ 2, ⟨?_, ?_⟩, ?_⟩
    · have h := mul_self_le_mul_self (show (0:ℝ) ≤ R / 2 by positivity) hr1
      nlinarith [h]
    · have h := mul_self_le_mul_self hr0 hr2
      nlinarith [h]
    · rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr0]

/-- **Coarea formula over the concentric spheres.**

For a point `x` and a radius `R > 0`, the integral over `r ∈ [R/2, R]` of the
number of parameters at which the knot meets the sphere of radius `r` about `x`
is at most the arclength of the part of the knot inside the closed ball of radius
`R` about `x`. -/
theorem lintegral_sphereCount_le (K : Knot) (x : R3) {R : ℝ} (hR : 0 < R) :
    ∫⁻ r in Set.Icc (R / 2) R, sphereCount K x r ≤
      arclengthIn K (paramSetIn K (Metric.closedBall x R)) := by
  classical
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hSmeas : MeasurableSet (paramSetIn K (Metric.closedBall x R)) :=
    (measurableSet_closedBall.preimage K.smooth.continuous.measurable).inter measurableSet_Icc
  -- the weight implementing the change of variables `y = r ^ 2`
  set W : ℝ → ENNReal := fun y =>
    (ENNReal.ofReal (2 * Real.sqrt y))⁻¹ *
      (Set.Icc (R ^ 2 / 4) (R ^ 2)).indicator (fun _ => (1 : ENNReal)) y with hWdef
  have hWmeas : AEMeasurable W := by
    rw [hWdef]
    measurability
  -- the abstract coarea inequality
  have hcoa := lintegral_mul_levelCount_le (0 : ℝ) (2 * Real.pi) hπ.le (sqDist K x)
    (sqDistDeriv K x) W hWmeas (fun t _ => sqDist_hasDerivAt K x t)
    (sqDist_continuousOn_deriv K x)
  -- the right-hand side is bounded by the arclength in the closed ball
  have hRHS : ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal |sqDistDeriv K x t| * W (sqDist K x t) ≤
      arclengthIn K (paramSetIn K (Metric.closedBall x R)) := by
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal |sqDistDeriv K x t| * W (sqDist K x t) ≤
        ENNReal.ofReal (speed K t) *
          (paramSetIn K (Metric.closedBall x R)).indicator (fun _ => (1 : ENNReal)) t := by
      intro t htI
      by_cases ht : dist (K.curve t) x ≤ R
      · have hWle : W (sqDist K x t) ≤
            (ENNReal.ofReal (2 * Real.sqrt (sqDist K x t)))⁻¹ := by
          simp only [hWdef]
          by_cases hmem : sqDist K x t ∈ Set.Icc (R ^ 2 / 4) (R ^ 2)
          · rw [Set.indicator_of_mem hmem, mul_one]
          · rw [Set.indicator_of_notMem hmem, mul_zero]
            exact bot_le
        calc ENNReal.ofReal |sqDistDeriv K x t| * W (sqDist K x t)
            ≤ ENNReal.ofReal |sqDistDeriv K x t| *
                (ENNReal.ofReal (2 * Real.sqrt (sqDist K x t)))⁻¹ := by
              gcongr
            _ ≤ ENNReal.ofReal (speed K t) := sqDistDeriv_mul_inv_sqrt_le K x t
            _ = ENNReal.ofReal (speed K t) *
                (paramSetIn K (Metric.closedBall x R)).indicator (fun _ => (1 : ENNReal)) t := by
              rw [Set.indicator_of_mem]
              · rw [mul_one]
              · exact ⟨Metric.mem_closedBall.mpr ht, htI⟩
      · push_neg at ht
        have hgt : R ^ 2 < sqDist K x t := by
          rw [sqDist_eq_dist_sq]
          nlinarith [ht, hR]
        have hnot : sqDist K x t ∉ Set.Icc (R ^ 2 / 4) (R ^ 2) := by
          intro hmem
          exact absurd hmem.2 (not_le.mpr hgt)
        have hW0 : W (sqDist K x t) = 0 := by
          simp only [hWdef]
          rw [Set.indicator_of_notMem hnot, mul_zero]
        have hnotS : t ∉ paramSetIn K (Metric.closedBall x R) := by
          intro hmem
          exact absurd (Metric.mem_closedBall.mp hmem.1) (not_le.mpr ht)
        rw [hW0, mul_zero, Set.indicator_of_notMem hnotS, mul_zero]
    calc ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal |sqDistDeriv K x t| * W (sqDist K x t)
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (speed K t) *
              (paramSetIn K (Metric.closedBall x R)).indicator (fun _ => (1 : ENNReal)) t :=
          setLIntegral_mono
            ((ENNReal.measurable_ofReal.comp
              ((K.smooth.continuous_deriv (by simp)).norm.measurable)).mul
                (measurable_const.indicator hSmeas)) hpt
      _ = ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi),
            (paramSetIn K (Metric.closedBall x R)).indicator
              (fun t => ENNReal.ofReal (speed K t)) t := by
          refine lintegral_congr fun t => ?_
          by_cases ht : t ∈ paramSetIn K (Metric.closedBall x R) <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
      _ = ∫⁻ t in paramSetIn K (Metric.closedBall x R) ∩ Set.Icc (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (speed K t) := by
          rw [setLIntegral_indicator hSmeas]
      _ = arclengthIn K (paramSetIn K (Metric.closedBall x R)) := by
          have hset : paramSetIn K (Metric.closedBall x R) ∩ Set.Icc (0 : ℝ) (2 * Real.pi) =
              paramSetIn K (Metric.closedBall x R) := by
            ext t
            constructor
            · intro h; exact h.1
            · intro h; exact ⟨h, h.2⟩
          rw [arclengthIn, hset]
  -- the left-hand side is the integral of the sphere counts
  have hLHS : ∫⁻ y, W y * levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) y =
      ∫⁻ r in Set.Icc (R / 2) R, sphereCount K x r := by
    have h1 : ∫⁻ y, W y * levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) y =
        ∫⁻ y in Set.Icc (R ^ 2 / 4) (R ^ 2),
          (ENNReal.ofReal (2 * Real.sqrt y))⁻¹ *
            levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) y := by
      rw [← lintegral_indicator measurableSet_Icc]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ Set.Icc (R ^ 2 / 4) (R ^ 2) <;>
        simp [hWdef, Set.indicator_of_mem, Set.indicator_of_notMem, hy]
    have h2 : ∫⁻ y in Set.Icc (R ^ 2 / 4) (R ^ 2),
          (ENNReal.ofReal (2 * Real.sqrt y))⁻¹ *
            levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) y =
        ∫⁻ r in Set.Icc (R / 2) R, sphereCount K x r := by
      have hsub := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
        (f := fun r : ℝ => r ^ 2) (f' := fun r : ℝ => 2 * r)
        (s := Set.Icc (R / 2) R) measurableSet_Icc
        (fun r _ => by simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt)
        (fun a ha b hb hab => by
          have ha0 : (0:ℝ) ≤ a := by linarith [ha.1, hR]
          have h := mul_self_le_mul_self ha0 hab
          nlinarith [h])
        (fun y => (ENNReal.ofReal (2 * Real.sqrt y))⁻¹ *
          levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) y)
      rw [image_sq_Icc hR] at hsub
      rw [hsub]
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      have hr0 : (0:ℝ) < r := by linarith [hr.1, hR]
      have hsqrt : Real.sqrt (r ^ 2) = r := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hr0)]
      have hlevel : levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) (r ^ 2) =
          sphereCount K x r := levelCount_sqDist_eq_sphereCount K x hr0
      rw [hlevel, hsqrt, ← mul_assoc, ENNReal.mul_inv_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top, one_mul]
    rw [h1, h2]
  calc ∫⁻ r in Set.Icc (R / 2) R, sphereCount K x r
      = ∫⁻ y, W y * levelCount (sqDist K x) (Set.Icc (0 : ℝ) (2 * Real.pi)) y := hLHS.symm
    _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal |sqDistDeriv K x t| * W (sqDist K x t) := hcoa
    _ ≤ arclengthIn K (paramSetIn K (Metric.closedBall x R)) := hRHS

end Work.Sweep
