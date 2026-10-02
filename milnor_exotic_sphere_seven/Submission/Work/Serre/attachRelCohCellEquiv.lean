import Mathlib
import Submission.Work.Serre.attachRelCohVanishing
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.CsrSharp.cellStepSharpIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative rational cohomology of a cell attachment in the top cell degree

Let `Z = attachCells (D-2) Γ ι f` be the space obtained from `Γ` by attaching `D`-cells along the
attaching maps `f i : S^{D-1} → Γ`, and let `Y' = Set.range (attachIncl (D-2) Γ ι f) ⊆ Z` be the
old part.  This file computes the relative rational cohomology of the pair `(Z, Y')` in the cell
degree:

`attachRelCohCellEquiv` — `H^D(Z, Y'; ℚ) ≅ ∏_{i : ι} ℚ`.

**Proof route.**  The sharp rational cell step
(`Work.Serre.CsrSharp.cellStepSharpIso`, applied to the identity fibration `Z → Z`, whose fibres
over the cell centres are one-point spaces) computes the relative *homology* of the pair as the
direct sum of the homology of the fibres:

`H_D(Z, Y'; ℚ) ≅ ⨁_{i : ι} H_0(pt; ℚ) ≅ ⨁_{i : ι} ℚ`.

The relative Kronecker pairing over the field `ℚ` (`Work.Serre.relKronEquiv`, the universal
coefficient theorem over a field) identifies the relative cohomology with the `ℚ`-dual of the
relative homology; the dual of a direct sum is the product of the duals
(`dualDirectSumEquiv` below) and the dual of `ℚ` is `ℚ`, which gives `∏_{i : ι} ℚ`.

(As in `Work.Serre.attachRelCohVanishing`, the path-connectedness hypothesis `hΓ` on `Γ` is not
needed for the computation; it belongs to the interface of the surrounding construction.)
-/

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## Two linear-algebra inputs -/

/-- **The dual of a direct sum is the product of the duals**: a linear functional on `⨁ᵢ Vᵢ` is
exactly a family of linear functionals on the summands.  This is the universal property of the
direct sum. -/
def dualDirectSumEquiv {κ : Type} [DecidableEq κ] (V : κ → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] :
    Module.Dual ℚ (DirectSum κ V) ≃ₗ[ℚ] (∀ i, Module.Dual ℚ (V i)) where
  toFun f := fun i => f.comp (DirectSum.lof ℚ κ V i)
  invFun g := DirectSum.toModule ℚ κ ℚ g
  left_inv f := by
    apply LinearMap.ext
    intro x
    exact (DirectSum.toModule.unique (R := ℚ) f x).symm
  right_inv g := by
    funext i
    apply LinearMap.ext
    intro x
    exact DirectSum.toModule_lof ℚ i x
  map_add' f g := by
    funext i
    apply LinearMap.ext
    intro x
    rfl
  map_smul' a f := by
    funext i
    apply LinearMap.ext
    intro x
    rfl

/-- **The `ℚ`-dual of `ℚ` is `ℚ`** (evaluation at `1`). -/
def ratDualSelfEquiv : Module.Dual ℚ ℚ ≃ₗ[ℚ] ℚ :=
  LinearMap.ringLmapEquivSelf ℚ ℚ ℚ

/-! ## The main computation -/

theorem attachRelCohCellEquiv (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
    (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) :
    Nonempty (Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)) ≅
      ModuleCat.of ℚ (∀ _ : ι, ℚ)) := by
  classical
  -- The space obtained by attaching the cells, and the old part.
  set Z := Work.RatHurewicz.attachCells (D - 2) Γ ι f with hZ
  set Y' : Set Z := Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f) with hY'
  -- The cells' centres, and the fibre of the identity map over a centre: a one-point space.
  let ctr : ι → Z := fun i => Work.Serre.csrCentre (D - 2) Γ ι f i
  let H0 : ι → ModuleCat ℚ := fun i => (Work.Cohomology.singularChains ℚ
    (TopCat.of (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)))).homology 0
  have hpc : ∀ i : ι, PathConnectedSpace (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)) :=
    fun i => ⟨⟨⟨ctr i, rfl⟩⟩, fun x y => by
      have h : x = y := Subtype.ext (x.2.trans y.2.symm)
      exact h ▸ Joined.refl x⟩
  -- (1) The sharp rational cell step for the identity fibration `Z → Z`.
  obtain ⟨eHraw⟩ := Work.Serre.CsrSharp.cellStepSharpIso (D - 2) Γ ι f
    (ContinuousMap.id Z) Work.StemsB.isSerreFibration_id 0
  -- (2) The fibre of the identity map over a cell centre is a point, so its `H₀` is `ℚ`.
  have hfib : ∀ i : ι, Nonempty (H0 i ≅ ModuleCat.of ℚ ℚ) :=
    fun i => @Work.Serre.ratH_zero_of_pathConnected _ _ (hpc i)
  -- (3) Re-index the cell step (`0 + ((D-2)+2) = D`).
  have hidx : 0 + (D - 2 + 2) = D := by omega
  have eH : ((Work.StemsB.relChainsR ℚ (TopCat.of Z) Y').homology D) ≅
      ModuleCat.of ℚ (DirectSum ι (fun i => ↥(H0 i))) :=
    (eqToIso (congrArg (fun k => (Work.StemsB.relChainsR ℚ (TopCat.of Z) Y').homology k)
      hidx)).symm ≪≫ eHraw
  -- (4) The relative Kronecker pairing identifies relative cohomology with the dual of relative
  -- homology.
  obtain ⟨eK⟩ := Work.Serre.relKronEquiv (TopCat.of Z) Y' D
  -- (5) Assemble: dualise the homology computation, distribute the dual over the direct sum and
  -- use that the dual of `ℚ` is `ℚ`.
  have F1 : ↥(Work.Thom.RelCoh ℚ D Z Y') ≃ₗ[ℚ]
      Module.Dual ℚ ↥((Work.StemsB.relChainsR ℚ (TopCat.of Z) Y').homology D) := eK
  have F2 : Module.Dual ℚ ↥((Work.StemsB.relChainsR ℚ (TopCat.of Z) Y').homology D) ≃ₗ[ℚ]
      Module.Dual ℚ (DirectSum ι (fun i => ↥(H0 i))) :=
    (LinearEquiv.dualMap eH.toLinearEquiv).symm
  have F3 : Module.Dual ℚ (DirectSum ι (fun i => ↥(H0 i))) ≃ₗ[ℚ]
      (∀ i, Module.Dual ℚ ↥(H0 i)) :=
    dualDirectSumEquiv (fun i => ↥(H0 i))
  have F4 : (∀ i, Module.Dual ℚ ↥(H0 i)) ≃ₗ[ℚ] (∀ _ : ι, ℚ) :=
    LinearEquiv.piCongrRight (fun i =>
      (LinearEquiv.dualMap (Classical.choice (hfib i)).toLinearEquiv).symm.trans
        ratDualSelfEquiv)
  have F : ↥(Work.Thom.RelCoh ℚ D Z Y') ≃ₗ[ℚ] (∀ _ : ι, ℚ) :=
    F1.trans (F2.trans (F3.trans F4))
  exact ⟨LinearEquiv.toModuleIso F⟩

end

end Work.Serre
