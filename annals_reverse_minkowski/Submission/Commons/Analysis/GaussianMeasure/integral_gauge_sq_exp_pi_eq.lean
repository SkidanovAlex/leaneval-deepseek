import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory

theorem integral_gauge_sq_exp_pi_eq {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hcvx : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K) (A : Matrix (Fin m) (Fin m) ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin m), (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) = (((2 * Real.pi) ^ ((m : ℝ) / 2)) * (2 * Real.pi))⁻¹ * ∫ x : EuclideanSpace ℝ (Fin m), (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by
  have _ : Convex ℝ K := hcvx
  have _ : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K := hK0
  set R : ℝ := Real.sqrt (2 * Real.pi) with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * Real.pi := by rw [hRdef]; exact Real.sq_sqrt (by positivity)
  have hpow : R ^ m = (2 * Real.pi) ^ ((m : ℝ) / 2) := by
    have he : (1 : ℝ) / 2 * (m : ℝ) = (m : ℝ) / 2 := by ring
    rw [hRdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), he]
  set F : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) with hF
  set G : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) with hG
  have key : ∀ x : EuclideanSpace ℝ (Fin m), F (R • x) = (2 * Real.pi) * G x := by
    intro x
    change (gauge K (Matrix.toLpLin 2 2 A (R • x))) ^ 2 * Real.exp (-‖R • x‖ ^ 2 / 2)
      = (2 * Real.pi) * ((gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
    have hg : gauge K (Matrix.toLpLin 2 2 A (R • x)) = R * gauge K (Matrix.toLpLin 2 2 A x) := by
      rw [LinearMap.map_smul, gauge_smul_of_nonneg hRnn, smul_eq_mul]
    have hn : ‖R • x‖ ^ 2 = (2 * Real.pi) * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg hRnn, mul_pow, hR2]
    have he : (-‖R • x‖ ^ 2 / 2 : ℝ) = -Real.pi * ‖x‖ ^ 2 := by
      rw [hn]; ring
    rw [hg, he, mul_pow, hR2]
    ring
  have hInt := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := volume) F R (hR := hRnn)
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp [EuclideanSpace, PiLp]
  have hLHS : (∫ x, F (R • x)) = (2 * Real.pi) * ∫ x, G x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall key)
  have hmain : (2 * Real.pi) * (∫ x, G x) = (R ^ m)⁻¹ * (∫ x, F x) := by
    rw [hfin] at hInt
    rw [hLHS] at hInt
    simpa [smul_eq_mul] using hInt
  have hfinal : (∫ x, G x) = ((2 * Real.pi) * R ^ m)⁻¹ * (∫ x, F x) := by
    have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    calc (∫ x, G x) = (2 * Real.pi)⁻¹ * ((2 * Real.pi) * ∫ x, G x) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = (2 * Real.pi)⁻¹ * ((R ^ m)⁻¹ * ∫ x, F x) := by rw [hmain]
      _ = ((2 * Real.pi) * R ^ m)⁻¹ * (∫ x, F x) := by rw [← mul_assoc, ← mul_inv]
  have hfin2 : ((2 * Real.pi) * R ^ m)⁻¹ = (((2 * Real.pi) ^ ((m : ℝ) / 2)) * (2 * Real.pi))⁻¹ := by
    rw [mul_comm (2 * Real.pi) (R ^ m), hpow]
  rw [hfinal, hfin2]

end Commons.Analysis.GaussianMeasure