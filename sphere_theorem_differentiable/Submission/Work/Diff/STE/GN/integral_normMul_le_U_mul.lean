import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.lp_mono_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Work.Diff.STE.GN

/-- The half-open unit cube sits inside the closed unit cube `[0,1]^ι`, which is compact. -/
lemma unitCube_subset_Icc_cube {ι : Type*} [Fintype ι] :
    Work.Diff.STE.unitCube (ι := ι) ⊆ Set.Icc (0 : ι → ℝ) 1 := by
  intro x hx
  simp only [Set.mem_Icc, Pi.le_def]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact le_of_lt (Set.mem_Ioc.mp (hx i (Set.mem_univ i))).1
  · exact (Set.mem_Ioc.mp (hx i (Set.mem_univ i))).2

theorem integral_normMul_le_U_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (ψ : (ι → ℝ) → ℝ) (U : ℝ)
    (hU : ∀ x : ι → ℝ, ‖f x‖ ≤ U) (hf : Continuous f) (hψ : Continuous ψ)
    (hψ0 : ∀ x : ι → ℝ, 0 ≤ ψ x) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ * ψ x
      ≤ U * ∫ x in Work.Diff.STE.unitCube (ι := ι), ψ x := by
  have hsub := unitCube_subset_Icc_cube (ι := ι)
  -- both integrands are continuous, hence integrable on the compact closed cube, hence on the
  -- (half-open) unit cube
  have hint1 : IntegrableOn (fun x : ι → ℝ => ‖f x‖ * ψ x)
      (Work.Diff.STE.unitCube (ι := ι)) volume :=
    ((hf.norm.mul hψ).continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hint2 : IntegrableOn (fun x : ι → ℝ => ψ x)
      (Work.Diff.STE.unitCube (ι := ι)) volume :=
    (hψ.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  -- pointwise `‖f x‖ * ψ x ≤ U * ψ x`, and `∫ U * ψ = U * ∫ ψ`
  have hmono : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ * ψ x
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), U * ψ x :=
    integral_mono_ae hint1 (hint2.const_mul U)
      (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_right (hU x) (hψ0 x))
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

end Work.Diff.STE.GN
