import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Interchanging a Bochner integral with a phase series

`Work.BoseBoxFock.integral_tsum_phase`: for a (complex-valued) integrable `W` on
`EuclideanSpace ℝ (Fin 3)` and an absolutely summable family `c : ι → ℂ` with arbitrary
frequencies `k i`, one may interchange the Lebesgue integral with the series of modulated
phase factors:

`∫ W(y) (∑' i, c i e^{-i ⟪k i, y⟫}) = ∑' i, c i ∫ e^{-i ⟪k i, y⟫} W(y)`.

The only analytic input is that the phase factor has modulus `1` (`norm_exp_phase`), which
makes `∑' i, ‖c i‖ ‖W y‖` an integrable dominating function (it is
`(∑' i, ‖c i‖) ∫ ‖W‖`, finite by `hc` and `hWi`). The interchange itself is
`MeasureTheory.integral_tsum_of_summable_integral_norm`.
-/

namespace Work.BoseBoxFock

/-- The phase factor `exp (-(I * ⟪k, y⟫))` has modulus `1`. -/
private lemma norm_exp_phase (k y : EuclideanSpace ℝ (Fin 3)) :
    ‖Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))‖ = 1 := by
  have h : -(Complex.I * (inner ℝ k y : ℂ)) = ((-(inner ℝ k y) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem integral_tsum_phase {ι : Type*} [Countable ι] {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ))
      MeasureTheory.volume)
    {c : ι → ℂ} (hc : Summable (fun i => ‖c i‖)) {k : ι → EuclideanSpace ℝ (Fin 3)} :
    (∫ y : EuclideanSpace ℝ (Fin 3), (W y : ℂ)
        * (∑' i : ι, c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))))
      = ∑' i : ι, c i * ∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ))) * (W y : ℂ) := by
  classical
  have hW_meas : MeasureTheory.AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin 3) => (W y : ℂ)) MeasureTheory.volume :=
    hWi.aestronglyMeasurable
  have hWnorm_int : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => ‖(W y : ℂ)‖) MeasureTheory.volume := hWi.norm
  have hnorm_eq : ∀ (i : ι) (y : EuclideanSpace ℝ (Fin 3)),
      ‖(c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ)‖
        = ‖c i‖ * ‖(W y : ℂ)‖ := by
    intro i y
    rw [norm_mul, norm_mul, norm_exp_phase (k i) y, mul_one]
  -- each summand is integrable, dominated by `‖c i‖ ‖W‖`
  have hF_int : ∀ i : ι, MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      (c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ))
      MeasureTheory.volume := by
    intro i
    refine MeasureTheory.Integrable.mono' (hWnorm_int.const_mul ‖c i‖) ?_ ?_
    · have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
          c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) := by fun_prop
      exact hcont.aestronglyMeasurable.mul hW_meas
    · filter_upwards with y
      exact le_of_eq (hnorm_eq i y)
  -- the values of the integrals of the norms
  have hF_norm_val : ∀ i : ι, ∫ y : EuclideanSpace ℝ (Fin 3),
      ‖(c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ)‖
      = ‖c i‖ * ∫ y : EuclideanSpace ℝ (Fin 3), ‖(W y : ℂ)‖ := by
    intro i
    rw [← MeasureTheory.integral_const_mul (‖c i‖)
      (fun y : EuclideanSpace ℝ (Fin 3) => ‖(W y : ℂ)‖)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    exact hnorm_eq i y
  have hF_sum : Summable (fun i : ι => ∫ y : EuclideanSpace ℝ (Fin 3),
      ‖(c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ)‖) := by
    have h := hc.mul_right (∫ y : EuclideanSpace ℝ (Fin 3), ‖(W y : ℂ)‖)
    simpa only [hF_norm_val] using h
  -- the interchange of integral and series
  have hFub : (∫ y : EuclideanSpace ℝ (Fin 3), ∑' i : ι,
      (c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ))
      = ∑' i : ι, ∫ y : EuclideanSpace ℝ (Fin 3),
          (c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ) :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
  have hterm : ∀ i : ι, (∫ y : EuclideanSpace ℝ (Fin 3),
      (c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ))
      = c i * ∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ))) * (W y : ℂ) := by
    intro i
    rw [← MeasureTheory.integral_const_mul (c i)
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ))) * (W y : ℂ))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    ring
  calc (∫ y : EuclideanSpace ℝ (Fin 3), (W y : ℂ)
        * (∑' i : ι, c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))))
      = ∫ y : EuclideanSpace ℝ (Fin 3), ∑' i : ι,
          (c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        rw [tsum_mul_right]
        ring
      _ = ∑' i : ι, ∫ y : EuclideanSpace ℝ (Fin 3),
          (c i * Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ)))) * (W y : ℂ) := hFub
      _ = ∑' i : ι, c i * ∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * (inner ℝ (k i) y : ℂ))) * (W y : ℂ) :=
        tsum_congr (fun i => hterm i)

end Work.BoseBoxFock
