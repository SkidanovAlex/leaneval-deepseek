import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chi_sq_bounds` — the two quantitative bounds on the corpus bump `χ`

`Submission/CubicChi.lean` defines the localization bump of the corpus as

    `chiBase x = chiBump x`,   `chiBump : ContDiffBump (0 : ℝ³)` with `rIn = 1/4`, `rOut = 1/2`,
    `chiNormSq  = ∫ x, (chiBase x)²`,
    `chi x      = chiBase x / √chiNormSq`.

The only information about `chiBase` that a proof can use is the `ContDiffBump` API:
`0 ≤ chiBase ≤ 1`, `chiBase = 1` on `ball 0 (1/4)` (whence `chiBase 0 = 1`), and `chiBase = 0`
off `ball 0 (1/2)`.  Those three facts give *both* bounds of this file, sharply:

* off `ball 0 (1/2)` the integrand `chiBase²` vanishes and on it `chiBase² ≤ 1`, so
  `chiNormSq ≤ volume (ball 0 (1/2)) = π/6`, hence `chiNormSq⁻¹ ≥ 6/π`;
* on `ball 0 (1/4)` the integrand is `1`, so `chiNormSq ≥ volume (ball 0 (1/4)) = π/48`,
  hence `chiNormSq⁻¹ ≤ 48/π`.

Since `chi 0 = 1/√chiNormSq` and `0 ≤ chi x ≤ chi 0` for every `x` (`chi x = chiBase x/√chiNormSq`
with `0 ≤ chiBase x ≤ 1 = chiBase 0`), the two constants are exactly the bounds on the supremum
of `χ²`: `6/π ≤ χ(0)²` and `χ(x)² ≤ 48/π`.  This is the "sharp-`χ`" fact behind the Bessel bound
`bessel_honest` (BF2 of `BOSE_BOXFOCK_LEAD.md`) and behind the falsity of the `Cn = 1` conjunct
of `RViewFS`.

The two integral estimates are proved here on top of Mathlib's volume of a ball in `ℝ³`
(`EuclideanSpace.volume_ball_fin_three`, through the corpus's `volume_ball_open_r3`), so the file
is self-contained over `Submission.Work.BoseBoxFock.Defs`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseBoxFock

open Submission.BoseGases

set_option autoImplicit false

/-- `chiBase` is the `ContDiffBump 0` with `rOut = 1/2`, so its square vanishes off
`ball 0 (1/2)`. -/
lemma chiSqBounds_chiBase_sq_eq_zero_of_half_le_norm {x : EuclideanSpace ℝ (Fin 3)}
    (hx : (1 : ℝ) / 2 ≤ ‖x‖) : (chiBase x) ^ 2 = 0 := by
  have h0 : chiBase x = 0 :=
    chiBump.zero_of_le_dist (by simpa [chiBump, dist_eq_norm] using hx)
  rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- **Upper bound for the `L²`-mass**: `∫ chiBase² ≤ volume (ball 0 (1/2)) = π/6`. -/
lemma chiSqBounds_chiNormSq_le : chiNormSq ≤ Real.pi / 6 := by
  have hzero : ∀ x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2),
      (chiBase x) ^ 2 = 0 := by
    intro x hx
    apply chiSqBounds_chiBase_sq_eq_zero_of_half_le_norm
    simp only [Metric.mem_ball, dist_eq_norm, not_lt, sub_zero] at hx
    exact hx
  have hEq : chiNormSq =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (chiBase x) ^ 2 := by
    rw [chiNormSq]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hmono : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (chiBase x) ^ 2) ≤
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (1 : ℝ) := by
    apply MeasureTheory.setIntegral_mono_ae
    · exact (chiBase_sq_continuous.integrable_of_hasCompactSupport
        chiBase_sq_hasCompactSupport).integrableOn
    · exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
    · filter_upwards with x
      rw [pow_two]
      nlinarith [chiBase_nonneg x, chiBase_le_one x]
  have hval : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (1 : ℝ)) =
      Real.pi / 6 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.Measure.real_def, volume_ball_open_r3 (1 / 2) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  calc chiNormSq =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (chiBase x) ^ 2 := hEq
    _ ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (1 : ℝ) := hmono
    _ = Real.pi / 6 := hval

/-- **Lower bound for the `L²`-mass**: `volume (ball 0 (1/4)) = π/48 ≤ ∫ chiBase²`, because
`chiBase = 1` on that ball. -/
lemma chiSqBounds_chiNormSq_ge : Real.pi / 48 ≤ chiNormSq := by
  have hf_int : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (chiBase x) ^ 2) :=
    chiBase_sq_continuous.integrable_of_hasCompactSupport chiBase_sq_hasCompactSupport
  have hcongr : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4), (chiBase x) ^ 2) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4), (1 : ℝ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
    intro x hx
    refine chiBase_sq_eq_one_of_norm_le ?_
    have h := Metric.mem_ball.mp hx
    simpa [dist_eq_norm] using le_of_lt h
  have hval : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4), (1 : ℝ)) =
      Real.pi / 48 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.Measure.real_def, volume_ball_open_r3 (1 / 4) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hzero : ∀ x ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2),
      (chiBase x) ^ 2 = 0 := by
    intro x hx
    apply chiSqBounds_chiBase_sq_eq_zero_of_half_le_norm
    simp only [Metric.mem_ball, dist_eq_norm, not_lt, sub_zero] at hx
    exact hx
  have hEq : chiNormSq =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (chiBase x) ^ 2 := by
    rw [chiNormSq]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  calc Real.pi / 48 =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4), (1 : ℝ) := hval.symm
    _ = ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4), (chiBase x) ^ 2 :=
        hcongr.symm
    _ ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), (chiBase x) ^ 2 := by
        apply MeasureTheory.setIntegral_mono_set
        · exact hf_int.integrableOn
        · filter_upwards with x
          positivity
        · filter_upwards with x hx
          exact Metric.ball_subset_ball (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2) hx
    _ = chiNormSq := hEq.symm

/-- The normalisation makes `chi 0 = 1/√chiNormSq`, so `χ(0)² = chiNormSq⁻¹`. -/
lemma chiSqBounds_chi_zero_sq :
    chi (0 : EuclideanSpace ℝ (Fin 3)) ^ 2 = chiNormSq⁻¹ := by
  have hsq : (Real.sqrt chiNormSq) ^ 2 = chiNormSq := Real.sq_sqrt (le_of_lt chiNormSq_pos)
  rw [chi, chiBase_zero, div_pow, hsq, one_pow, one_div]

/-- `0 ≤ chiBase ≤ 1` gives `0 ≤ χ x ≤ 1/√chiNormSq`, hence `χ(x)² ≤ chiNormSq⁻¹ = χ(0)²`. -/
lemma chiSqBounds_chi_sq_le (x : EuclideanSpace ℝ (Fin 3)) : chi x ^ 2 ≤ chiNormSq⁻¹ := by
  have hZ : 0 < chiNormSq := chiNormSq_pos
  have hs : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr hZ
  have hx0 : 0 ≤ chi x := chi_nonneg x
  have hxle : chi x ≤ (Real.sqrt chiNormSq)⁻¹ := by
    rw [chi, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr hs.le) (chiBase_le_one x)
  calc chi x ^ 2 ≤ ((Real.sqrt chiNormSq)⁻¹) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self hx0 hxle
    _ = chiNormSq⁻¹ := by
        rw [inv_pow, Real.sq_sqrt (le_of_lt hZ)]

theorem chi_sq_bounds : 6 / Real.pi ≤ Submission.BoseGases.chi 0 ^ 2 ∧
    (∀ x, Submission.BoseGases.chi x ^ 2 ≤ 48 / Real.pi) := by
  have hlow : (6 / Real.pi : ℝ) ≤ chiNormSq⁻¹ := by
    have h := (inv_le_inv₀ (by positivity : (0 : ℝ) < Real.pi / 6) chiNormSq_pos).mpr
      chiSqBounds_chiNormSq_le
    simpa [inv_div] using h
  have hhigh : chiNormSq⁻¹ ≤ 48 / Real.pi := by
    have h := (inv_le_inv₀ chiNormSq_pos (by positivity : (0 : ℝ) < Real.pi / 48)).mpr
      chiSqBounds_chiNormSq_ge
    simpa [inv_div] using h
  refine ⟨?_, ?_⟩
  · rw [chiSqBounds_chi_zero_sq]
    exact hlow
  · intro x
    exact le_trans (chiSqBounds_chi_sq_le x) hhigh

end Work.BoseBoxFock
