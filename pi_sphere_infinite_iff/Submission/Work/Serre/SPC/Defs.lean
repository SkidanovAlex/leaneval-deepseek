import Mathlib
import Submission.Work.Serre.cellStepDefs
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.Fibrations

set_option synthInstance.maxHeartbeats 400000


/-!
# Interfaces for the assembly of `Work.Serre.serrePairComparison`

The pair comparison of the Serre exact sequence in the stable range is assembled from three
analytic inputs, stated here as `Prop`-valued definitions so that the tower induction can be
stated and proved independently of them:

* `CellStepHyp` — the (strengthened) cell step: for a Serre fibration `q : X → Γ'` over a space
  `Γ'` obtained from `Γ` by attaching cells of dimension `D ≥ 2`, with fibres homologically
  `φ`-connected, the map of pairs `(X, q⁻¹Γ) → (Γ', Γ)` is an isomorphism in degrees `< D + φ`
  **and surjective in degree `D + φ`**.
* `FibreTransport` — the fibre homology of a Serre fibration is independent of the base point
  along a path (the integral transport statement).
* `CellStepHyp` and `FibreTransport` together with the two comparison theorems
  (`Work.Serre.Assembly.pairMapOf_isIso`, `Work.Serre.Assembly.pullbackPairMap_isIso`) and the CW
  model `Work.Serre.CWModel.exists_model` yield `Work.Serre.serrePairComparison`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- **The (strengthened) cell step.** -/
def CellStepHyp : Prop :=
  ∀ (D : ℕ) (_hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (_hq : Work.StemsB.IsSerreFibration q) (φ : ℕ)
    (_hfib : ∀ (y : Work.RatHurewicz.attachCells (D - 2) Γ ι f), ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (_h0 : ∀ y : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ))),
    (∀ i : ℕ, i < D + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.cellStepAttachMap D Γ ι f X q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.cellStepAttachMap D Γ ι f X q) (D + φ)).hom

/-- **Transport of the fibre data of a Serre fibration along a path in the base.** -/
def FibreTransport : Prop :=
  ∀ {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ] (q : C(X, Γ))
    (_hq : Work.StemsB.IsSerreFibration q) (φ : ℕ) (x₀ x₁ : Γ) (γ : C(unitInterval, Γ))
    (_hγ0 : γ 0 = x₀) (_hγ1 : γ 1 = x₁),
    (∀ j : ℕ, 0 < j → j < φ → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q x₀))).homology j)) →
    CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q x₀))
      (ModuleCat.of ℤ ℤ)) →
    (∀ j : ℕ, 0 < j → j < φ → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q x₁))).homology j)) ∧
    CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q x₁))
      (ModuleCat.of ℤ ℤ))

end

end Work.Serre.SPC
