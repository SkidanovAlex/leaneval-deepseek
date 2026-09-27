import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.LeafNuFields
import Submission.Work.EKLC7.LeafNuCondExp
import Submission.Work.EKLC7.measurable_nu
import Submission.Work.EKLC7.FlowerFamExists
import Submission.Work.EKLC7.OrbitCoord
import Submission.Work.EKLComp.plaque_propor
import Submission.Work.EKLC7.nu_equivariant

/-!
# `Work.EKLC7.LeafwiseHoro` — the existence half of C5

`Work.EKLC7.P_LeafwiseEx` (Pisa Theorem 6.3: existence of leafwise measures for every
horospherical subgroup of an `A`-invariant probability measure), assembled from the
construction of `Submission/Work/EKLC7/LeafNu*.lean`:

* `Work.EKLC7.FlowerFamExists` — the flower family `F : FlowerFam U μ` (Pisa 6.7 + 6.9–6.15),
  which is proved in this workspace from `Work.EKLComp.prove_X3` and
  `Work.EKLRelCross.flower_local_exists`;
* `Work.EKLC7.FlowerFam.exists_good` — the conull good set `X'`;
* `Work.EKLC7.OrbitCoord` — the measurable leaf coordinate;
* `Work.EKLC7.FlowerFam.radon`, `.carried`, `.normalised`, `.pos` (`LeafNuFields`),
  `.condexp_nu` (`LeafNuCondExp`) and `Work.EKLC7.measurable_nu` (`measurable_nu`) — seven of the
  nine fields of the frozen structure `Work.EKLContract.IsLeafwise`.

The remaining field `equivariant` (Pisa 6.3(iii)) is isolated as the hypothesis `EquivAt` of
`isLeafwise_nu` below; it is being proved as `Work.EKLC7.nu_equivariant`
(`Submission/Work/EKLC7/nu_equivariant.lean`) and as `Work.EKLC7.equivariant_nu`
(`Submission/Work/EKLC7/equivariant_nu.lean`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- The `equivariant` field of `Work.EKLContract.IsLeafwise` (Pisa 6.3(iii)) for a system `ν` on
a set `X'`: right translation of the leafwise measure by `u ∈ U` corresponds to moving the base
point by `u`, up to a finite non-zero constant. -/
def EquivField (U : Subgroup SL3) (ν : X3 → Measure SL3) (X' : Set X3) : Prop :=
  ∀ x ∈ X', ∀ u ∈ U, u • x ∈ X' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ν x = c • (ν (u • x)).map (fun g => g * u)

/-- **The leafwise system built from a flower family is a leafwise system** (Pisa Theorem 6.3),
given the `equivariant` field. -/
theorem isLeafwise_nu (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
    (hprop : Work.EKLC7.FlowerFam.ProporHyp U μ) (coord : X3 → X3 → SL3)
    (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
    (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
      y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
    {X' : Set X3} (hX' : F.Good X') (heq : EquivField U (F.nu coord X') X') :
    IsLeafwise μ U (F.nu coord X') X' where
  meas_dom := hX'.meas
  conull := hX'.null
  radon := fun x hx => F.radon hU coord hcoordm hcsub hX' hx
  carried := fun x hx => F.carried hU coord hcoordm hcsub hX' hx
  normalised := fun x hx => F.normalised hU coord hcoordm hcsub hX' hx
  measurable := fun f => measurable_nu F hU coord hcoordm hX' f
  pos := fun x hx δ hδ => F.pos hU coord hcoordm hcsub hX' hx hδ
  equivariant := fun x hx u hu hux => heq x hx u hu hux
  condexp := fun Z m hm f hf hfb =>
    F.condexp_nu hU hprop coord hcoordm hcsub hX' Z ⟨m⟩ hm f hf hfb

/-- **`P_LeafwiseEx` from the `equivariant` field of the constructed system.** -/
theorem LeafwiseHoro_of_equivariant
    (heq : ∀ (U : Subgroup SL3) (μ : Measure X3), [IsProbabilityMeasure μ] → IsHoro U →
      ∀ (F : FlowerFam U μ) (coord : X3 → X3 → SL3)
        (hcoordm : Measurable (fun p : X3 × X3 => coord p.1 p.2))
        (hcsub : ∀ x y, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
          y ∈ (fun u : SL3 => u • x) '' (U : Set SL3) → coord x y ∈ U ∧ coord x y • x = y)
        (X' : Set X3), F.Good X' → EquivField U (F.nu coord X') X') :
    P_LeafwiseEx := by
  intro μ hprob hAinv U hU
  haveI := hprob
  obtain ⟨F⟩ := FlowerFamExists U hU μ hAinv
  have hprop : Work.EKLC7.FlowerFam.ProporHyp U μ := fun Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂ =>
    Work.EKLComp.plaque_propor U μ Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂
  obtain ⟨X', hX'⟩ := F.exists_good hU hAinv hprop
  obtain ⟨coord, hcoordm, hcsub⟩ := OrbitCoord U hU.1
  exact ⟨F.nu coord X', X', isLeafwise_nu F hU hprop coord hcoordm hcsub hX'
    (heq U μ hU F coord hcoordm hcsub X' hX')⟩

/-- **Pisa Theorem 6.3 (existence of leafwise measures)**, in the form requested for the
frozen contract: for every `A`-invariant probability measure `μ` on `X3 = SL₃(ℝ)/SL₃(ℤ)` and
every horospherical subgroup `U ≤ SL₃(ℝ)` there is a system `ν` of leafwise measures on a
conull subset `X'`, satisfying the nine clauses of `Work.EKLContract.IsLeafwise`. -/
theorem LeafwiseHoro :
    ∀ (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ],
      Work.EKLContract.IsAInvariant μ →
      ∀ (U : Subgroup Work.EKLContract.SL3), Work.EKLContract.IsHoro U →
        ∃ (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
          (X' : Set Work.EKLContract.X3), Work.EKLContract.IsLeafwise μ U ν X' :=
  LeafwiseHoro_of_equivariant (fun U μ _ hU F coord hcoordm hcsub X' hX' =>
    nu_equivariant F hU coord hcoordm hcsub hX')

end Work.EKLC7
