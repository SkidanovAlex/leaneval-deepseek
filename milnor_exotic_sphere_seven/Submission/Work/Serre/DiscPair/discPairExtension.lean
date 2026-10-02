import Mathlib
import Submission.Work.Serre.DiscPair.discPairCohVanishing
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.DiscPair.isZero_relCoh_discPairNewCells_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The extension of a relative class across an attachment (the relative Thom class)

For `Γ' = attachCells (D-2) Γ ι f` and a Serre fibration `q : X → Γ'` whose fibres over the cell
centres are path connected and have the rational homology of `S^r` through degree `N`, the pullback
of relative cohomology

  `H^{r+1}(cyl q, (cylRetract q)⁻¹Γ ∪ range (cylIncl q))  ⟶  H^{r+1}(cyl q, (cylRetract q)⁻¹Γ)`

is an **isomorphism**: a relative class over the old part extends uniquely over the attached cells.
This is the first half of the cellular step of the CW-model Thom case: the relative Thom class over
the new stage is the (unique) preimage of the relative Thom class over the old stage.  The proof
combines

* `Work.Serre.DiscPair.isZero_relCoh_discPairNewCells` — the new-cell groups vanish in degrees `r+1`
  and `r+2` (the *obstruction* to the extension vanishes, and the extension is unique), with
* `Work.Serre.DiscPair.isZero_conePairRelCoh` — the fibre pair over a cell centre is concentrated in
  degree `r+1` (so the per-cell vanishings hold), and
* `Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero` — the general "extension" lemma for the
  cohomology of a triple.
-/

set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

/-- The old part of the base of an attachment, pulled back to the mapping cylinder. -/
abbrev discPairOld (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)

/-- The old part together with the new spheres: the set whose relative complex is the
"new-cell" complex of the disc-pair bundle. -/
abbrev discPairNew (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  discPairOld D Γ ι f X q ∪ Set.range (Work.Serre.cylIncl q)

/-- The inclusion of the new-cell pair into the disc pair, as a continuous map. -/
def discPairInclMap (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : C(↥(discPairNew D Γ ι f X q), Work.Serre.cyl q) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **The extension of the relative Thom class across an attachment**, from the two vanishing
statements of the new-cell groups.  The vanishings are supplied by
`Work.Serre.DiscPair.isZero_relCoh_discPairNewCells` (for `D ≤ m ≤ N+1+D`,
`m ≠ D + r + 1`, in the range where all the fibres have the `S^r` homology) and by
`Work.Serre.DiscPair.isZero_relCoh_discPairNewCells_lt` (for `m < D`, with no fibre hypothesis at
all); in the application `r + 1 ≠ D + r + 1` and `r + 2 ≠ D + r + 1` because `D ≥ 2`. -/
theorem isIso_relCohMap_discPair_of_isZero (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (h₁ : CategoryTheory.Limits.IsZero
      (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (discPairNew D Γ ι f X q)))
    (h₂ : CategoryTheory.Limits.IsZero
      (Work.Thom.RelCoh ℚ (r + 2) (Work.Serre.cyl q) (discPairNew D Γ ι f X q))) :
    CategoryTheory.IsIso (Work.Thom.relCohMap
      (discPairInclMap D Γ ι f X q)
      {x : ↥(discPairNew D Γ ι f X q) | (x : Work.Serre.cyl q) ∈ discPairOld D Γ ι f X q}
      (discPairOld D Γ ι f X q) (fun x hx => hx) ℚ (r + 1)) :=
  isIso_relCohMap_incl_of_isZero (TopCat.of (Work.Serre.cyl q))
    (discPairOld D Γ ι f X q) (discPairNew D Γ ι f X q) Set.subset_union_left (r + 1) h₁ h₂

/-- **The extension of the relative Thom class across an attachment** (the theorem form: the
pullback `H^{r+1}(cyl q, discPairNew) → H^{r+1}(cyl q, discPairOld)` is an isomorphism), from the
fibre data at the cell centres.  This is the "the old relative Thom class extends uniquely over the
attached cells" half of the cellular step of the CW-model Thom case. -/
theorem isIso_relCohMap_discPair (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D-2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D-2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D-2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hrN : r ≤ N) :
    CategoryTheory.IsIso (Work.Thom.relCohMap
      (discPairInclMap D Γ ι f X q)
      {x : ↥(discPairNew D Γ ι f X q) | (x : Work.Serre.cyl q) ∈ discPairOld D Γ ι f X q}
      (discPairOld D Γ ι f X q) (fun x hx => hx) ℚ (r + 1)) := by
  classical
  have hnefib : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)) :=
    fun i => (hpc _).nonempty
  have hcone : ∀ i : ι, ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 → CategoryTheory.Limits.IsZero
      (Work.Thom.RelCoh ℚ j
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) :=
    fun i j hj hjne => isZero_conePairRelCoh D hD Γ ι f q hq r N hr i
      (hpc _) (hvan _) (hgen _) j hj hjne
  have key : ∀ m : ℕ, m ≤ N + 1 + D → m ≠ D + r + 1 →
      CategoryTheory.Limits.IsZero
        (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q) (discPairNew D Γ ι f X q)) := by
    intro m hm hne
    rcases lt_or_ge m D with hlt | hge
    · exact isZero_relCoh_discPairNewCells_lt D hD Γ ι f q hq m hlt
    · exact isZero_relCoh_discPairNewCells D hD Γ ι f q hq hnefib r N hcone m hge hm hne
  exact isIso_relCohMap_discPair_of_isZero r N D hr hD Γ ι f q hq
    (key (r + 1) (by omega) (by omega)) (key (r + 2) (by omega) (by omega))

end

end Work.Serre.DiscPair
