import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.DiscPair.discCellStepCoh
import Submission.Work.Serre.DiscPair.cellStepVanishing
import Submission.Work.Serre.DiscPair.cylPairCofibre
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.DiscPair.subPairMapQuasiIso
import Submission.Work.Serre.RatTower.Defs

/-!
# The disc-pair cell groups vanish below the cell dimension

For `Γ' = attachCells (D-2) Γ ι f` and any Serre fibration `q : X → Γ'` (no hypothesis on the
fibres!), the relative cohomology of the disc-pair bundle

  `(cyl q, (cylRetract q)⁻¹Γ ∪ range (cylIncl q))`

vanishes in every degree `m < D`.  This is the purely homotopy theoretic part of the vanishing of
the new-cell groups (`Work.Serre.DiscPair.isZero_relCoh_discPairNewCells` covers the range
`D ≤ m ≤ N+1+D` and needs the fibre hypothesis; below `D` no hypothesis is needed).

The proof is the long exact sequence of the triple `U ⊆ A₂ ⊆ cyl q`, where

* `H_m(cyl q, U) ≅ H_m(Γ', Γ)` (the retraction is a homotopy equivalence of pairs), which vanishes
  for `m < D` because `Γ'` is obtained from `Γ` by attaching `D`-cells
  (`Work.Serre.DiscPair.isZero_relChainsR_homology_self_of_lt`);
* `H_j(A₂, U) ≅ H_j(X, q⁻¹Γ)` (`Work.Serre.DiscPair.subPairMapQuasiIso`), which vanishes for
  `j < D` because `q` is a fibration over a space built from `Γ` by attaching `D`-cells
  (`Work.Serre.DiscPair.isZero_relChainsR_homology_preimage_of_lt`).

Both vanishings feed `CategoryTheory.ShortComplex.ShortExact.exactAt_X₃`, which needs an
`Epi` of the first map of the triple sequence in degree `m` (from `H_m(cyl q, U) = 0`) and a `Mono`
of it in degree `m-1` (from `H_{m-1}(A₂, U) = 0`).  This also disposes of the degree `m = 0` case,
where no relation `(ComplexShape.down ℕ).Rel 0 j` exists and the `Mono` requirement is vacuous.
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

/-- A quasi-isomorphism of `ℚ`-chain complexes transfers the vanishing of the homology of its
target to its source. -/
theorem isZero_homology_of_quasiIso {C₁ C₂ : ChainComplex (ModuleCat ℚ) ℕ} (φ : C₁ ⟶ C₂) (n : ℕ)
    (hIso : IsIso (HomologicalComplex.homologyMap φ n)) (h : IsZero (C₂.homology n)) :
    IsZero (C₁.homology n) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  have hb : Function.Injective (HomologicalComplex.homologyMap φ n) :=
    ((ConcreteCategory.isIso_iff_bijective (HomologicalComplex.homologyMap φ n)).mp hIso).1
  exact ⟨fun a b => hb (Subsingleton.elim _ _)⟩

/-- A quasi-isomorphism of `ℚ`-chain complexes transfers the vanishing of the homology of its
source to its target. -/
theorem isZero_homology_of_quasiIso' {C₁ C₂ : ChainComplex (ModuleCat ℚ) ℕ} (φ : C₁ ⟶ C₂) (n : ℕ)
    (hIso : IsIso (HomologicalComplex.homologyMap φ n)) (h : IsZero (C₁.homology n)) :
    IsZero (C₂.homology n) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  have hs : Function.Surjective (HomologicalComplex.homologyMap φ n) :=
    ((ConcreteCategory.isIso_iff_bijective (HomologicalComplex.homologyMap φ n)).mp hIso).2
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hs a
    obtain ⟨b', rfl⟩ := hs b
    rw [Subsingleton.elim a' b']⟩

/-- The old part `(cylRetract q)⁻¹Γ' ⊆ cyl q` of the base of an attachment, pulled back to the
mapping cylinder. -/
abbrev relCohLtOld (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)

/-- The old part together with the bottom copy of the source: the second member of the disc pair. -/
abbrev relCohLtNew (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  relCohLtOld D Γ ι f X q ∪ Set.range (Work.Serre.cylIncl q)

theorem isZero_relCoh_discPairNewCells_lt (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (m : ℕ) (hm : m < D) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q)
      ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
        Set.range (Work.Serre.cylIncl q))) := by
  classical
  -- the relative cohomology is the dual of the relative homology
  refine isZero_relCoh_of_isZero_relH _ m ?_
  show CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
    (TopCat.of (Work.Serre.cyl q)) (relCohLtNew D Γ ι f X q)).homology m)
  -- the triple `U ⊆ B ⊆ cyl q` and its long exact sequence
  have hsub : relCohLtOld D Γ ι f X q ⊆ relCohLtNew D Γ ι f X q := Set.subset_union_left
  let S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
    Work.Serre.RatTower.tripleShortR (TopCat.of (Work.Serre.cyl q))
      (relCohLtOld D Γ ι f X q) (relCohLtNew D Γ ι f X q) hsub
  have hS : S.ShortExact := Work.Serre.RatTower.tripleShortR_shortExact _ _ _ _
  -- `H_m(cyl q, U)` vanishes for `m < D`, being `H_m(Γ', Γ)`
  have hZY : IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
      (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))).homology m) :=
    isZero_relChainsR_homology_self_of_lt (D - 2) Γ ι f m (by omega)
  have hXU : IsZero (S.X₂.homology m) :=
    isZero_homology_of_quasiIso
      (Work.Serre.relChainsRPairMap (relCohLtOld D Γ ι f X q)
        (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
        (Work.Serre.cylRetract q)
        (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      m (axCylRetractPairIso (D := D) (Γ := Γ) (ι := ι) (f := f) q m) hZY
  -- `H_j(B,U)` vanishes for `j < D`, being `H_j(X, q⁻¹Γ)`
  have hBU : ∀ j : ℕ, j < D → IsZero (S.X₁.homology j) := by
    intro j hj
    have hXA : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X)
        (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)).homology j) :=
      isZero_relChainsR_homology_preimage_of_lt (D - 2) Γ ι f q hq j (by omega)
    exact isZero_homology_of_quasiIso'
      (Aux.cylΦ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) j
      (Aux.isIso_cylΦ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q j) hXA
  -- exactness at `X₃` gives the result
  have hExact : S.X₃.ExactAt m :=
    ShortComplex.ShortExact.exactAt_X₃ hS m (IsZero.epi hXU _)
      (fun j hj => IsZero.mono (hBU j (by have hj' : j + 1 = m := hj; omega)) _)
  exact hExact.isZero_homology

end

end Work.Serre.DiscPair
