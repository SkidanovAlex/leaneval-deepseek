import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompSetup.X2Aux

/-!
# The maximal-inequality set `X₂` (EKL §4.2, "Construction of `X₂`")

`X₂` is the set of points `x` of the conull set `X''` whose leafwise measure gives the plaque
`ballU R` at least `(1-ε²)` of its mass to the Luzin compact set `X₁`, for **every** radius `R > 0`;
it is shown here to have measure `> 1 - C ε²`.

The argument is in `X2Aux`: the maximal inequality for leafwise measures (hypothesis `hML`, the
frozen component `P_MaxLeaf`) is applied to the complement `f = 1 - 1_{X₁}` of `X₁` with
`α = ε²`.  For `x ∈ X''` outside `X₂` the complement of `X₁` occupies more than an `ε²`-fraction
of `ballU R`, hence `x` belongs to the maximal set, whose measure is at most
`C · (∫ f dμ)/ε² ≤ C ε⁴/ε² = C ε²` because `X₁` has measure `> 1 - ε⁴`.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace Work.EKLCompSetup

theorem exists_X2
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' X₁ : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hX''meas : MeasurableSet X'') (hX''sub : X'' ⊆ X') (hX''conull : μ X''ᶜ = 0)
    (hX₁meas : MeasurableSet X₁)
    (hleaf : ∀ R : ℝ, Measurable fun x => (Work.EKLComp.leafMass ν X₁ R x).toReal)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX₁ : 1 - ε^4 ≤ (μ X₁).toReal)
    (hML : ∀ (f : Work.EKLContract.X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
      MeasureTheory.Integrable f μ →
      ∀ α : ℝ, 0 < α →
        μ {x | x ∈ X' ∧ ∃ r : ℝ, 0 < r ∧
            α * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 r)).toReal
              < ∫ g in Work.EKLContract.ballU Work.EKLComp.h01 r, f (g • x) ∂(ν x)}
          ≤ ENNReal.ofReal (C * (∫ x, f x ∂μ) / α)) :
    ∃ X₂ : Set Work.EKLContract.X3, MeasurableSet X₂ ∧
      (∀ x, x ∈ X₂ ↔ x ∈ X'' ∧ ∀ R : ℝ, 0 < R →
        (1 - ε^2) * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal
          ≤ (Work.EKLComp.leafMass ν X₁ R x).toReal) ∧
      1 - C * ε^2 ≤ (μ X₂).toReal := by
  refine ⟨X'' ∩ X₂set ν X₁ ε, hX''meas.inter (measurableSet_X₂set hL hν hleaf ε), ?_, ?_⟩
  · intro x
    rw [Set.mem_inter_iff, mem_X₂set_iff hν hX₁meas x]
  · exact measure_X₂set_ge hL hν hX''meas hX''sub hX''conull hX₁meas hleaf hC hε hX₁ hML

end Work.EKLCompSetup
