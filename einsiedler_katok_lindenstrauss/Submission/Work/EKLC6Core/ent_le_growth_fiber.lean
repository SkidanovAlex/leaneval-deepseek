import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLC6Core.ent_le_growth_of_aerg
import Submission.Work.EKLC6Core.condExpKernel_quasiErgodic
import Submission.Work.EKLC6Core.fiber_leafwise_thm
import Submission.Work.EKLEntJacobs.fiber_inv

/-!
# `Work.EKLC6Core.ent_le_growth_fiber` — Pisa 7.19–7.24 (the per-component bound)

For a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the single diagonal map
`T = (aDiag t ·)`, with a leaf-wise system `ν` for the full contracted horospherical subgroup
`U = Uminus t`, the entropy of `T` *at each ergodic component* `κ x = condExpKernel μ (invariants T) x`
is bounded by that component's integral of the growth function:

`ent (κ x) T ≤ ofReal (∫ growthFun (Uminus t) ν t d(κ x))`  for `μ`-a.e. `x`.

This is the per-fibre form of Pisa Theorem 7.6(ii)/7.24: by Jacobs' theorem
`ent μ T = ∫⁻ x, ent (κ x) T ∂μ`, and by the ergodic decomposition of `μ` over `invariants T`,
`μ = ∫ x, κ x ∂μ`.  The conclusion is proved by applying the `T`-ergodic case
(`Work.EKLC6Core.ent_le_growth_of_aerg`) to the fibre `κ x`, which is `T`-invariant
(`Work.EKLEntJacobs.fiber_inv`), `T`-ergodic (`Work.EKLC6Core.condExpKernel_quasiErgodic`) and
carries `ν` as a leaf-wise system (`Work.EKLC6Core.fiber_leafwise_thm`, Pisa 7.22); the two
remaining hypotheses of the `T`-ergodic case (conullity of `X''` and integrability of the growth
function under `κ x`) are transferred from `μ` by `MeasureTheory.Integrable.condExpKernel_ae` and
the fact that `μ`-null sets are `κ x`-null for a.e. `x`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- If `B` is `μ`-null, then the conditional measures of the invariant σ-algebra of a
measure-preserving `T` vanish on `B` almost everywhere. -/
private theorem condExpKernel_eq_zero_of_null {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace X3]
    {T : X3 → X3} (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    {B : Set X3} (hBmeas : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B = 0 := by
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace X3) :=
    MeasurableSpace.invariants_le T
  have hind : B.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] (0 : X3 → ℝ) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine le_antisymm ?_ bot_le
    refine le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hB0)
    intro x hx
    by_contra hxc
    exact hx (by simp [Set.indicator_of_notMem hxc])
  have h2 : μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] =ᵐ[μ]
      (0 : X3 → ℝ) := by
    have h := MeasureTheory.condExp_congr_ae (μ := μ) (m := MeasurableSpace.invariants T) hind
    rwa [MeasureTheory.condExp_zero] at h
  have hreal : (fun x => (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x).real B)
      =ᵐ[μ] (0 : X3 → ℝ) :=
    (ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
      (m := MeasurableSpace.invariants T) hm hBmeas).trans h2
  filter_upwards [hreal] with x hx
  haveI : IsProbabilityMeasure (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.is_probability_measure' x
  have hfin : ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ B)) ?_
    rw [MeasureTheory.measure_univ]
    exact ENNReal.one_lt_top
  rw [MeasureTheory.measureReal_def] at hx
  rcases (ENNReal.toReal_eq_zero_iff _).mp hx with h | h
  · exact h
  · exact absurd h (ne_of_lt hfin)

/-- **Pisa 7.19–7.24, per ergodic component.** -/
theorem ent_le_growth_fiber {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    ∀ᵐ x ∂μ,
      Work.EKLContract.ent
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≤
      ENNReal.ofReal (∫ y, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t y
        ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)) := by
  let T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag t • x
  have hT : Measurable T := (continuous_const_smul (Work.EKLContract.aDiag t)).measurable
  -- `X''` is conull for the conditional measures
  have hX''fib : ∀ᵐ x ∂μ,
      ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x (X''ᶜ) = 0 := by
    obtain ⟨B, hXB, hBmeas, hB0⟩ := MeasureTheory.exists_measurable_superset_of_null hX''
    filter_upwards [condExpKernel_eq_zero_of_null hT hmp hBmeas hB0] with x hx
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hXB) (le_of_eq hx)) bot_le
  -- the growth function is integrable for the conditional measures
  have hintfib : ∀ᵐ x ∂μ,
      MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t)
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    hint.condExpKernel_ae
  filter_upwards [Work.EKLEntJacobs.fiber_inv μ T hT hmp,
      condExpKernel_quasiErgodic μ T hT hmp,
      fiber_leafwise_thm (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hmp hL hcov hX'',
      hX''fib, hintfib] with x hinv hqerg hLx hX''x hintx
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.is_probability_measure' x
  exact ent_le_growth_of_aerg (μ := ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
    t hinv hqerg hLx hcov hX''x hmeas hintx

end Work.EKLC6Core

end
