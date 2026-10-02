import Mathlib
import Submission.Work.Serre.DiscPair.cellStepVanishing
import Submission.Work.Serre.attachRelCohVanishing
import Submission.Work.Serre.CsrSharp.cellStepSharpIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the relative rational cohomology above the cell dimension

Let `Z = Work.RatHurewicz.attachCells (D-2) Γ ι f` be the space obtained from `Γ` by attaching
`D`-cells along the attaching maps `f i : S^{D-1} → Γ`, and let
`Y' = Set.range (attachIncl (D-2) Γ ι f) ⊆ Z` be the old part.

The relative rational (co)homology of the pair `(Z, Y')` is concentrated in the single degree `D`:
below it this is `Work.Serre.attachRelCohVanishing`, above it is the present statement,

`attachRelCohVanishingHigh` — `H^m(Z, Y'; ℚ) = 0` for every `m > D`.

The proof is the high-degree half of the sharp rational cell step
(`Work.Serre.CsrSharp.cellStepSharpIso`, applied to the identity fibration `Z → Z`, whose fibres
over the cell centres are one-point spaces): the relative homology is the direct sum of the
homologies of the fibres,

`H_m(Z, Y'; ℚ) ≅ ⨁_{i : ι} H_{m-D}(pt; ℚ)`  (`m ≥ D`),

and a one-point space has vanishing homology in every positive degree
(`Work.Cohomology.homologyContractible_ring`).  Since `m - D > 0`, the direct sum vanishes, and the
relative Kronecker pairing over the field `ℚ` (`Work.Serre.relKronEquiv`, the universal coefficient
theorem over a field) turns this into the vanishing of the relative cohomology
(`Work.Serre.isZero_relCoh_of_isZero_relHomology`).

(As in `Work.Serre.attachRelCohVanishing`, no path-connectedness hypothesis on `Γ` is needed for
this computation.)
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

theorem attachRelCohVanishingHigh (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (m : ℕ) (hm : D < m) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m
      (Work.RatHurewicz.attachCells (D-2) Γ ι f)
      (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))) := by
  classical
  -- the space obtained by attaching the cells and the old part
  set Z := Work.RatHurewicz.attachCells (D - 2) Γ ι f with hZ
  set Y' : Set Z := Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f) with hY'
  -- it suffices to kill the relative rational homology in degree `m`
  refine isZero_relCoh_of_isZero_relHomology Y' m ?_
  -- the centres of the attached cells
  let ctr : ι → Z := fun i => Work.Serre.csrCentre (D - 2) Γ ι f i
  have hk : 0 < m - D := by omega
  -- the fibre of the identity fibration over a cell centre is a one-point space, so its homology
  -- vanishes in the positive degree `m - D`
  have hzero : ∀ i : ι, CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
      (TopCat.of (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)))).homology (m - D)) := by
    intro i
    haveI : Subsingleton (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)) :=
      ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
    haveI : Nonempty (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)) := ⟨⟨ctr i, rfl⟩⟩
    exact Work.Cohomology.homologyContractible_ring ℚ (m - D) hk
  -- the sharp rational cell step for the identity fibration `Z → Z`
  obtain ⟨eHraw⟩ := Work.Serre.CsrSharp.cellStepSharpIso (D - 2) Γ ι f
    (ContinuousMap.id Z) Work.StemsB.isSerreFibration_id (m - D)
  -- a coproduct of zero modules is zero, and the direct sum is such a coproduct
  have hcop : CategoryTheory.Limits.IsZero (∐ fun i => (Work.Cohomology.singularChains ℚ
      (TopCat.of (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)))).homology (m - D)) :=
    Work.Serre.DiscPair.isZero_coprod_of_isZero _ hzero
  have hdir : CategoryTheory.Limits.IsZero (ModuleCat.of ℚ (DirectSum ι (fun i =>
      ↥((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre (ContinuousMap.id Z) (ctr i)))).homology (m - D))))) :=
    CategoryTheory.Limits.IsZero.of_iso hcop (ModuleCat.coprodIsoDirectSum _).symm
  -- transport along the cell step and re-index `(m - D) + ((D-2)+2) = m`
  have hsharp : CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of Z) Y').homology
      (m - D + (D - 2 + 2))) := CategoryTheory.Limits.IsZero.of_iso hdir eHraw
  have hidx : m - D + (D - 2 + 2) = m := by omega
  simpa only [hidx] using hsharp

end

end Work.Serre
