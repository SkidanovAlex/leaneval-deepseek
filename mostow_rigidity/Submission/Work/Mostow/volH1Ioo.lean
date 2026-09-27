import Mathlib
import Submission.Work.Mostow.gapA.volH1Ico
import Submission.Work.Mostow.gapA.slabDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

/-- The chart coordinate of `x • single 0 1` in `E 1`. -/
private lemma volH1Ioo_smul_single_apply (x : ℝ) :
    (((x • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E 1)) : E 1) 0) = x := by
  simp

/-- The hyperbolic volume density at `x • single 0 1`. -/
private lemma volH1Ioo_hdens_smul (x : ℝ) :
    hdens ((x • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E 1)) : E 1)
      = ENNReal.ofReal ((Real.sqrt (1 + x ^ 2))⁻¹) := by
  rw [hdens, tpart]
  congr 2
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, sq_abs]

/-- `x ↦ x • single 0 1` is a measure preserving parametrisation of `E 1 = ℍ¹`. -/
private lemma volH1Ioo_measurePreserving :
    MeasurePreserving (fun x : ℝ => x • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E 1))
      (volume : Measure ℝ) (volume : Measure (E 1)) := by
  have hv : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E 1) ≠ 0 := by
    intro h
    have h2 := congrArg (fun v : E 1 => v.ofLp 0) h
    simp at h2
  have h := volume_eq_of_finrank_eq_one (E := E 1) finrank_euclideanSpace_fin hv
  rw [show ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E 1)‖ₑ = 1 by
        simp [enorm_eq_nnnorm], one_smul] at h
  exact ⟨by fun_prop, h.symm⟩

theorem volH1Ioo (A B : ℝ) (hAB : A ≤ B) :
    (Submission.Mostow.volH 1) {v : Submission.Mostow.E 1 | v 0 ∈ Set.Ioo A B}
      = ENNReal.ofReal (Real.arsinh B - Real.arsinh A) := by
  have hs : MeasurableSet {v : E 1 | v 0 ∈ Set.Ioo A B} := by
    have hcont : Continuous fun v : E 1 => v.ofLp (0 : Fin 1) :=
      PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
    exact measurableSet_Ioo.preimage hcont.measurable
  -- Step 1: transport `volH 1` to Lebesgue measure on `ℝ` along `x ↦ x • single 0 1`.
  have hstep : (Submission.Mostow.volH 1) {v : E 1 | v 0 ∈ Set.Ioo A B}
      = ∫⁻ x in Set.Ioo A B, ENNReal.ofReal ((Real.sqrt (1 + x ^ 2))⁻¹)
          ∂(volume : Measure ℝ) := by
    rw [volHApply 1 hs, ← lintegral_indicator hs (hdens (n := 1))]
    rw [← volH1Ioo_measurePreserving.lintegral_comp
      ((measurable_hdens (n := 1)).indicator hs)]
    have hpt : (fun x : ℝ => ({v : E 1 | v 0 ∈ Set.Ioo A B}).indicator (hdens (n := 1))
          ((fun x : ℝ => x • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E 1)) x))
        = fun x : ℝ => (Set.Ioo A B).indicator
            (fun y => ENNReal.ofReal ((Real.sqrt (1 + y ^ 2))⁻¹)) x := by
      funext x
      by_cases hx : x ∈ Set.Ioo A B
      · rw [Set.indicator_of_mem hx,
          Set.indicator_of_mem (by simpa [volH1Ioo_smul_single_apply] using hx),
          volH1Ioo_hdens_smul]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (by simpa [volH1Ioo_smul_single_apply] using hx)]
    rw [hpt, lintegral_indicator measurableSet_Ioo]
  rw [hstep]
  -- Step 2: the `ofReal`/lintegral bridge and the explicit one-dimensional integral.
  have hg_cont : Continuous (fun x : ℝ => (Real.sqrt (1 + x ^ 2))⁻¹) := by
    refine Continuous.inv₀ ?_ ?_
    · fun_prop
    · intro x; positivity
  have hg_nonneg : ∀ x : ℝ, 0 ≤ (Real.sqrt (1 + x ^ 2))⁻¹ := by
    intro x; positivity
  have hInt : IntegrableOn (fun x : ℝ => (Real.sqrt (1 + x ^ 2))⁻¹) (Set.Ioo A B)
      (volume : Measure ℝ) :=
    hg_cont.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set
      Set.Ioo_subset_Icc_self
  have hofreal := ofReal_integral_eq_lintegral_ofReal
      (μ := (volume : Measure ℝ).restrict (Set.Ioo A B))
      (f := fun x : ℝ => (Real.sqrt (1 + x ^ 2))⁻¹) hInt
      (Filter.Eventually.of_forall hg_nonneg)
  rw [← hofreal]
  congr 1
  have hae : Set.Ioo A B =ᵐ[(volume : Measure ℝ)] Set.Ioc A B := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (measure_empty)
      intro x hx
      exact hx.2 ⟨hx.1.1, hx.1.2.le⟩
    · refine measure_mono_null ?_ (Real.volume_singleton (a := B))
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_Ioc, Set.mem_singleton_iff] at hx ⊢
      exact le_antisymm hx.1.2 (le_of_not_gt (fun hB => hx.2 ⟨hx.1.1, hB⟩))
  rw [setIntegral_congr_set hae, ← intervalIntegral.integral_of_le hAB]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_arsinh x)
    (hg_cont.intervalIntegrable A B)

end

end Work.Mostow
