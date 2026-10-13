import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-- `∫_{Iθ} f² · sEta` is finite as soon as `f` is continuous on the open angular interval and
bounded there: the weight `sEta θ = sin(2θ)^{-η}` (with `η = 99/100 < 1`) is integrable on `Iθ`,
so `C² · sEta` is an integrable dominating function. -/
lemma integrableOn_sq_mul_sEta_of_bdd {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  obtain ⟨C, hC0, hCb⟩ := hbdd
  -- The two endpoints of `Iθ` are null, so we may work on the open interval `(0, π/2)`.
  have key : MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) := by
    -- `sEta` is continuous where its base `sin (2θ)` is positive, hence on the open interval
    have hS : ContinuousOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      fun θ hθ => (continuousAt_sEta hθ).continuousWithinAt
    have hprod : ContinuousOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := (hf.pow 2).mul hS
    have haesm := hprod.aestronglyMeasurable (μ := MeasureTheory.volume)
      isOpen_Ioo.measurableSet
    -- the dominating function: `C ^ 2 * sEta`, integrable on the open interval
    have hEta : MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_sEta_and_integral_le.1.mono_set Set.Ioo_subset_Icc_self
    have hdom : MeasureTheory.IntegrableOn (fun θ => C ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := hEta.const_mul (C ^ 2)
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict isOpen_Ioo.measurableSet] with θ hθ
    have hEtaθ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
      sEta_nonneg_of_mem_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (f θ) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hCb θ hθ) 2
    have hnn : 0 ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_nonneg (sq_nonneg _) hEtaθ
    rw [Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right hsq hEtaθ
  refine (integrableOn_Icc_iff_integrableOn_Ioo (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)).mpr ?_
  exact key

end Work.FTS.EllipticEst.H2W
