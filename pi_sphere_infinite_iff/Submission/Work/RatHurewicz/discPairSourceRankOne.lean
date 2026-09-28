import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.oldPartIdentification
import Submission.Work.Serre.DiscPair.discPairCohVanishing
import Submission.Work.Serre.DiscPair.isZero_relCoh_discPairNewCells_lt
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.ratCoh_ratH_iso_rat
import Submission.Work.Serre.CWModelThomAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

theorem discPairSourceRankOne (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) (hrN : r ≤ N) {Γ : Type}
    [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Set.range (Work.Serre.cylIncl q)) ≅ ModuleCat.of ℚ ℚ) := by
  classical
  set A : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q) with hA
  set Nw : Set (Work.Serre.cyl q) :=
    (Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f) ∪ A
    with hNw
  -- concentration of the fibre pairs at the cell centres
  have hcone : ∀ i : ι, ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
        {x | (x : Work.Serre.cyl q) ∈ A}) := by
    intro i j hj hjne
    exact Work.Serre.DiscPair.isZero_conePairRelCoh D hD Γ ι f q hq r N hr i
      (hpc (Work.Serre.csrCentre (D - 2) Γ ι f i))
      (hvan (Work.Serre.csrCentre (D - 2) Γ ι f i))
      (hgen (Work.Serre.csrCentre (D - 2) Γ ι f i)) j hj hjne
  -- the new-cell groups vanish in the two degrees `r+1` and `r+2`
  have hnew : ∀ m : ℕ, (m = r + 1 ∨ m = r + 2) →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q) Nw) := by
    intro m hm
    by_cases hDm : D ≤ m
    · refine Work.Serre.DiscPair.isZero_relCoh_discPairNewCells D hD Γ ι f q hq
        (fun i => (hpc (Work.Serre.csrCentre (D - 2) Γ ι f i)).nonempty) r N hcone m hDm ?_ ?_
      · omega
      · rcases hm with h | h <;> omega
    · exact Work.Serre.DiscPair.isZero_relCoh_discPairNewCells_lt D hD Γ ι f q hq m (by omega)
  -- the restriction `H^{r+1}(M,A) → H^{r+1}(Nw,A)` is an isomorphism
  have hAB : A ⊆ Nw := Set.subset_union_right
  haveI hiso1 : IsIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥Nw, Work.Serre.cyl q)) {x : ↥Nw | (x : Work.Serre.cyl q) ∈ A} A
      (fun x hx => hx) ℚ (r + 1)) :=
    Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero (TopCat.of (Work.Serre.cyl q)) A Nw hAB
      (r + 1) (hnew (r + 1) (Or.inl rfl)) (hnew (r + 2) (Or.inr rfl))
  let e1 := asIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥Nw, Work.Serre.cyl q)) {x : ↥Nw | (x : Work.Serre.cyl q) ∈ A} A
      (fun x hx => hx) ℚ (r + 1))
  -- the old part `(Nw, A)` is the disc pair of the restricted fibration
  obtain ⟨e2⟩ := oldPartIdentification D hD ι f q (r + 1)
  -- the source of the old part is a line: the induction hypothesis in degree `0`
  let qo := Work.Serre.restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))
  obtain ⟨U, hU⟩ := IH
  haveI hU0 : IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl qo)) 0 (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract qo) ℚ 0).hom)) := hU 0 (by omega)
  have hsource : Nonempty (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl qo)
      (Set.range (Work.Serre.cylIncl qo)) ≅ ModuleCat.of ℚ ℚ) := by
    have h1 : (0 + r + 1) = r + 1 := by omega
    have hSpc : PathConnectedSpace ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)) :=
      Work.Serre.CWThom.pathConnectedSpace_of_homeo
        (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι f) hΓ
    haveI := hSpc
    have eC : Work.Thom.Coh ℚ 0 ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)) ≅
        ModuleCat.of ℚ ℚ :=
      Classical.choice ((Work.Serre.ratCoh_ratH_iso_rat
        (TopCat.of ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) 0).mpr
        (Work.Serre.ratH_zero_of_pathConnected
          ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
    exact ⟨(eqToIso (congrArg (fun n => Work.Thom.RelCoh ℚ n (Work.Serre.cyl qo)
        (Set.range (Work.Serre.cylIncl qo))) h1)).symm
      ≪≫ (asIso (ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl qo)) 0 (r + 1)).flip U) ∘ₗ
          (Work.Thom.CohMap (Work.Serre.cylRetract qo) ℚ 0).hom))).symm ≪≫ eC⟩
  obtain ⟨e3⟩ := hsource
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

end

end Work.RatHurewicz
