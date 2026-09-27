import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLEntJacobs.Hcond_kernel
import Submission.Work.EKLEntJacobs.fiber_inv

/-!
# `Work.EKLC6Core.lintegral_le_of_condKernel_bound`

If a non-negative (a.e. measurable) function `F` on a standard Borel probability space has
conditional expectations `x ↦ ∫⁻ y, F y ∂(condExpKernel μ (invariants T) x)` bounded by a constant
`C` `μ`-a.e., then `∫⁻ y, F y ∂μ ≤ C`.

This is the *disintegration identity* for the conditional kernel: the conditional measures
`κ x = condExpKernel μ (invariants T) x` are a disintegration of `μ` in the sense that

`∫⁻ y, F y ∂μ = ∫⁻ x, (∫⁻ y, F y ∂ κ x) ∂μ`  (`lintegral_eq_lintegral_condExpKernel_invariants`),

which is `ProbabilityTheory.condExpKernel_comp_trim` (i.e. `κ ∘ₘ μ.trim hm = μ`) combined with
`Measure.lintegral_bind` and `lintegral_trim`.  Monotonicity of the integral then finishes.

The identity is stated with the σ-algebra written as `invariants T` (rather than with the
sub-σ-algebra as a binder variable) so that the only `MeasurableSpace Ω` instance at play is the
ambient one.
-/

namespace Work.EKLC6Core

open MeasureTheory ProbabilityTheory

open scoped ENNReal

/-- **Disintegration identity for the conditional kernel.** For a finite measure `μ` on a standard
Borel space and a self-map `T`, the integral of an a.e. measurable `ℝ≥0∞`-valued function `F`
against `μ` equals the integral of its conditional expectations with respect to the invariant
σ-algebra of `T`. -/
theorem lintegral_eq_lintegral_condExpKernel_invariants {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (T : Ω → Ω)
    {F : Ω → ENNReal} (hF : AEMeasurable F μ) :
    ∫⁻ y, F y ∂μ
      = ∫⁻ x, (∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants T) x)) ∂μ := by
  -- Replace `F` by a measurable representative.
  obtain ⟨F', hF'm, hF'eq⟩ : ∃ F' : Ω → ENNReal, Measurable F' ∧ F =ᵐ[μ] F' :=
    ⟨hF.mk, hF.measurable_mk, hF.ae_eq_mk⟩
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace Ω› := MeasurableSpace.invariants_le T
  -- `x ↦ ∫⁻ y, F' y ∂κ x` is measurable for the invariant σ-algebra, hence for the ambient one.
  have hg'm : @Measurable Ω ENNReal (MeasurableSpace.invariants T) ENNReal.measurableSpace
      (fun x => ∫⁻ y, F' y ∂(ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x)) :=
    Measurable.lintegral_kernel_prod_right
      (κ := ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T))
      (f := fun _ b => F' b) (hF'm.comp measurable_snd)
  -- `κ ∘ₘ μ.trim hm = μ`.
  have hcomp : (μ.trim hm).bind
        (⇑(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T))) = μ :=
    ProbabilityTheory.condExpKernel_comp_trim hm
  -- `F` and `F'` have the same conditional expectations `(μ.trim hm)`-a.e.
  have hae : (fun x => ∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x))
      =ᵐ[μ.trim hm] (fun x => ∫⁻ y, F' y ∂(ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x)) := by
    have h1 : ∀ᵐ x ∂(μ.trim hm), ∀ᵐ y ∂(ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants T) x), F y = F' y :=
      Measure.ae_ae_of_ae_bind (m := μ.trim hm)
        (f := ⇑(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T)))
        (p := fun y => F y = F' y)
        (ProbabilityTheory.Kernel.aemeasurable _ (μ := μ.trim hm))
        (by rw [hcomp]; exact hF'eq)
    filter_upwards [h1] with x hx
    exact lintegral_congr_ae hx
  have hAe : AEMeasurable (fun x => ∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x)) (μ.trim hm) := ⟨_, hg'm, hae⟩
  calc ∫⁻ y, F y ∂μ
      = ∫⁻ y, F' y ∂μ := lintegral_congr_ae hF'eq
    _ = ∫⁻ y, F' y ∂(μ.trim hm).bind
          (⇑(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T))) := by rw [hcomp]
    _ = ∫⁻ x, (∫⁻ y, F' y ∂(ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants T) x)) ∂(μ.trim hm) :=
          Measure.lintegral_bind (ProbabilityTheory.Kernel.aemeasurable _
            (μ := μ.trim hm)) hF'm.aemeasurable
    _ = ∫⁻ x, (∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants T) x)) ∂(μ.trim hm) := lintegral_congr_ae hae.symm
    _ = ∫⁻ x, (∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants T) x)) ∂μ := lintegral_trim_ae hm hAe

theorem lintegral_le_of_condKernel_bound {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    (t : Fin 3 → ℝ)
    (F : Work.EKLContract.X3 → ENNReal) (hF : AEMeasurable F μ) (C : ENNReal)
    (h : ∀ᵐ x ∂μ, ∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x) ≤ C) :
    ∫⁻ y, F y ∂μ ≤ C := by
  rw [lintegral_eq_lintegral_condExpKernel_invariants μ
    (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) hF]
  calc ∫⁻ x, (∫⁻ y, F y ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)) ∂μ
      ≤ ∫⁻ x, C ∂μ := MeasureTheory.lintegral_mono_ae h
    _ = C := by rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

end Work.EKLC6Core
