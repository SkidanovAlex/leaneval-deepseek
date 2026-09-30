import Mathlib
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.cellClassMapCell_isIso
import Submission.Work.DeltaHomology.relHomology_cell_splitting
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.exists_deformationRetract_punctSkel
import Submission.Work.Homology.Basic
import Submission.Work.DeltaHomology.simplexGenMap_isIso
import Submission.Work.HomologyExtra.Main
import Submission.Work.DeltaHomology.relHomology_punctSkel_succ_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The classes of the top cells are a basis of `H_{k+1}(X^{k+1}, punctSkel (k+1))`

This file proves `Work.DeltaHomology.isIso_fold_cellClassMap`: for a realized `Δ`-complex,
the fold map
`∐_σ H_{k+1}(Δ^{k+1}, ∂Δ^{k+1}) ⟶ H_{k+1}(X^{k+1}, punctSkel (k+1))`
whose `σ`-th component is `cellClassMap R (k+1) σ` (the class of the characteristic map `χ σ`)
is an isomorphism, i.e. the classes `[χ σ]` are a basis.

## The proof

Write `n = k+1`, `Y = Xⁿ` and `A = punctSkel n ⊆ Y`.  For each `n`-simplex `σ` let
`Q_σ := H_n(Y, Y ∖ {b_σ})` be the *local group* at the barycentre `b_σ` of its cell, and let
`q_σ : H_n(Y, A) ⟶ Q_σ` be the map induced by the inclusion of pairs (the "local projection").
Two computations about the cell class `g_σ := cellClassMap R n σ : H_n(Δⁿ,∂Δⁿ) ⟶ H_n(Y,A)` are
needed:

* `g_σ ≫ q_σ` is an isomorphism.  Factoring the characteristic map through the closed cell,
  this is the statement that the inclusion of pairs `(cell_σ, punctCell_σ) → (Y, Y∖{b_σ})` is
  an isomorphism on relative homology in degree `n` (the local degree of a top cell is `±1`),
  proved here as `fold_isIso_cellIntoNeighbourhood` by two open-cover excisions — inside the
  cell and inside the skeleton — to the common middle pair
  `(intCell_σ, intCell_σ ∖ {b_σ})`, which are identified by the identity on `X`;
* `g_τ ≫ q_σ = 0` for `τ ≠ σ`, since `χ τ` maps into `cell_τ ⊆ Y ∖ {b_σ}`, so its class already
  comes from a chain of the smaller subspace and dies in the relative complex
  (`fold_relHomologyMap_eq_zero_of_mapsTo`).

From these two facts, and nothing else, the theorem follows by pure diagram chasing: the map
`s_σ := q_σ ≫ (g_σ ≫ q_σ)⁻¹` is a left inverse of `g_σ` and kills the other components, so
`s := lift s_σ` satisfies `m ≫ s = 𝟙`.  Thus `m = desc g` is a split monomorphism.  The
remaining (purely module-theoretic) input `s ≫ m = 𝟙` is supplied by the *Hopfian* property of
finitely generated `ℤ`-modules: `f := s ≫ e` is a surjective endomorphism of `H_n(Y,A)` (here
`e` is the rank isomorphism `H_n(Y,A) ≅ ∐_σ ℤ` of `relHomology_punctSkel_succ_iso`), hence
injective, hence bijective; from `IsIso f` we deduce that `s` has a right inverse `r`, and then
`m = m ≫ 𝟙 = m ≫ s ≫ r = r`, so `s ≫ m = 𝟙`.  Hence `m` is an isomorphism with inverse `s`.

Note that no rank/independence analysis of the individual classes is needed: injectivity and
surjectivity of the fold map are both consequences of the two local computations above.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-! ## The four pairs intervening in the local computation -/

namespace DeltaRealization

/-- The punctured `n`-skeleton `Xⁿ ∖ {barycentres}`, viewed as a subset of the `n`-skeleton. -/
abbrev punctSkelPiece (R : DeltaRealization K X) (n : ℕ) :
    Set ↥(R.toDeltaSimplexMap.skelSet n) :=
  {x | (x : X) ∈ R.toDeltaSimplexMap.punctSkel n}

/-- The complement of the barycentre `b_σ` inside the `n`-skeleton. -/
abbrev punctNeighbourhood (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    Set ↥(R.toDeltaSimplexMap.skelSet n) :=
  {x | (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ}

/-- The barycentre of an `n`-simplex is not in the punctured `n`-skeleton. -/
theorem cellBarycenter_not_mem_punctSkel (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) :
    R.toDeltaSimplexMap.cellBarycenter n σ ∉ R.toDeltaSimplexMap.punctSkel n := by
  rw [DeltaSimplexMap.punctSkel, Set.mem_sdiff]
  exact fun h => h.2 (Set.mem_range_self σ)

/-- The *local projection* `H_n(Xⁿ, punctSkel n) ⟶ H_n(Xⁿ, Xⁿ ∖ {b_σ})` given by the identity
of `Xⁿ`: the map to the local homology at the barycentre `b_σ`. -/
def punctSkelToNeighbourhood (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    PairHom (TopCat.of (R.toDeltaSimplexMap.skelSet n))
      (TopCat.of (R.toDeltaSimplexMap.skelSet n))
      (R.punctSkelPiece n) (R.punctNeighbourhood n σ) :=
  pairHomOfSubset fun x hx => by
    intro hb
    exact hx.2 (hb ▸ Set.mem_range_self σ)

/-- **The closed cell of `σ` inside the complement of its own barycentre.**  The pair
`(cell_σ, punctCell_σ)` maps into the pair `(Xⁿ, Xⁿ ∖ {b_σ})` by inclusion; `H_n` of this map is
the local degree of the top cell `σ`. -/
def cellIntoNeighbourhood (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    PairHom (TopCat.of (R.toDeltaSimplexMap.cell n σ))
      (TopCat.of (R.toDeltaSimplexMap.skelSet n))
      {x : ↥(R.toDeltaSimplexMap.cell n σ) | (x : X) ∈ R.toDeltaSimplexMap.punctCell n σ}
      (R.punctNeighbourhood n σ) where
  hom := TopCat.ofHom ⟨fun x => ⟨(x : X), R.toDeltaSimplexMap.cell_subset_skelSet σ x.2⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩
  mapsTo := by
    rintro x ⟨hx, -⟩
    intro hb
    exact hx.2 (hb ▸ Set.mem_range_self σ)

/-- The open `n`-cell `intCell_σ`, viewed inside the `n`-skeleton. -/
abbrev intCellPiece (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    Set ↥(R.toDeltaSimplexMap.skelSet n) :=
  {x | (x : X) ∈ R.toDeltaSimplexMap.intCell n σ}

end DeltaRealization

/-! ## Elementary consequences of the realization axioms -/

/-- Two maps of pairs with the same underlying continuous map are equal (the `mapsTo` field lives
in a proposition). -/
theorem fold_pairHom_ext_of_hom_eq {X Y : TopCat} {A : Set X} {B : Set Y}
    {Φ Ψ : PairHom X Y A B} (h : Φ.hom = Ψ.hom) : Φ = Ψ := by
  obtain ⟨f, hf⟩ := Φ
  obtain ⟨g, hg⟩ := Ψ
  subst h
  rw [Subsingleton.elim hf hg]

/-- The barycentre of an `n`-cell is not a point of any *other* closed `n`-cell. -/
theorem fold_cellBarycenter_not_mem_cell_of_ne (R : DeltaRealization K X) (k : ℕ)
    {σ τ : Fin (K.card (k + 1))} (h : σ ≠ τ) :
    R.cellBarycenter (k + 1) σ ∉ R.cell (k + 1) τ := by
  intro hmem
  have hnot : R.cellBarycenter (k + 1) σ ∉ R.skelSet k :=
    DeltaSimplexMap.cellBarycenter_not_mem_skelSet_of_lt R (Nat.lt_succ_self k) σ
  have hkey := mem_intCell_of_mem_cell_of_not_mem_skelSet R k τ hmem hnot
  exact Set.disjoint_left.mp (intCell_disjoint R (k + 1) h)
    (DeltaSimplexMap.cellBarycenter_mem_intCell R (k + 1) σ) hkey

/-! ## A map of pairs whose image lies in the relative part kills relative chains -/

/-- **A map of pairs carrying every point into the relative part kills relative chains.**  If
`Φ : (X,A) → (Y,B)` is a map of pairs such that *every* point of `X` is carried into `B`, then
the induced map on relative chain complexes is zero: on chains `Φ` factors through the inclusion
`C_*(B) → C_*(Y)`, which the projection to the relative complex kills. -/
theorem fold_relChainMap_eq_zero_of_mapsTo {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) (h : ∀ x : X, Φ.hom x ∈ B) :
    relChainMap ZMod Φ = 0 := by
  have hcont : Continuous (fun x : X => Φ.hom x) :=
    (ConcreteCategory.hom Φ.hom).continuous
  have hfact : Φ.hom = TopCat.ofHom ⟨fun x => ⟨Φ.hom x, h x⟩,
      Continuous.subtype_mk hcont h⟩ ≫ incl B := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hzero : singChainMap ZMod Φ.hom ≫ relProj ZMod Y B = 0 := by
    rw [hfact, singChainMap_comp, Category.assoc, cokernel.condition, comp_zero]
  apply (cancel_epi (relProj ZMod X A)).1
  rw [← relChainMap_comp_relProj, hzero, comp_zero]

/-- The same statement on relative homology. -/
theorem fold_relHomologyMap_eq_zero_of_mapsTo {X Y : TopCat} {A : Set X} {B : Set Y}
    (Φ : PairHom X Y A B) (h : ∀ x : X, Φ.hom x ∈ B) (n : ℕ) :
    relHomologyMap ZMod n Φ = 0 := by
  rw [relHomologyMap, fold_relChainMap_eq_zero_of_mapsTo Φ h]
  simp

/-! ## The characteristic map factors through the cell -/

/-- The composite `(Δⁿ, ∂Δⁿ) → (Xⁿ, Xⁿ ∖ {b_σ})` induced by `χ σ` goes through the closed
cell `cell_σ` in the same way whether one uses `skelPunctPairHom` or `cellPairHomPunct`. -/
theorem punctSkelToNeighbourhood_comp_skelPunctPairHom (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) :
    (R.punctSkelToNeighbourhood n σ).comp (R.skelPunctPairHom n σ) =
      (R.cellIntoNeighbourhood n σ).comp (R.cellPairHomPunct n σ) := by
  refine fold_pairHom_ext_of_hom_eq ?_
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  rfl

theorem cellClassMap_comp_punctSkelToNeighbourhood (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) :
    cellClassMap R n σ ≫ relHomologyMap ZMod n (R.punctSkelToNeighbourhood n σ) =
      cellClassMapCell R n σ ≫ relHomologyMap ZMod n (R.cellIntoNeighbourhood n σ) := by
  have hfac := punctSkelToNeighbourhood_comp_skelPunctPairHom R n σ
  simp only [cellClassMap, cellClassMapCell]
  rw [Category.assoc, Category.assoc]
  congr 1
  rw [← Work.HomologyExtra.relHomologyMap_comp, hfac,
    Work.HomologyExtra.relHomologyMap_comp]

/-- **A cell other than `σ` dies in the local group at `b_σ`**: the class of `χ τ` is killed by
the local projection `q_σ` whenever `τ ≠ σ`, because `χ τ` maps into `cell_τ ⊆ Xⁿ ∖ {b_σ}`. -/
theorem cellClassMap_comp_punctSkelToNeighbourhood_eq_zero (R : DeltaRealization K X) (k : ℕ)
    {σ τ : Fin (K.card (k + 1))} (h : τ ≠ σ) :
    cellClassMap R (k + 1) τ ≫
      relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ) = 0 := by
  have hz : relHomologyMap ZMod (k + 1)
      ((R.punctSkelToNeighbourhood (k + 1) σ).comp (R.skelPunctPairHom (k + 1) τ)) = 0 := by
    refine fold_relHomologyMap_eq_zero_of_mapsTo _ (fun w => ?_) (k + 1)
    intro hb
    have hmem : R.cellBarycenter (k + 1) σ ∈ R.cell (k + 1) τ := by
      rw [← hb]
      exact Set.mem_range_self w
    exact fold_cellBarycenter_not_mem_cell_of_ne R k (Ne.symm h) hmem
  simp only [cellClassMap]
  rw [Category.assoc, ← Work.HomologyExtra.relHomologyMap_comp, hz, comp_zero]

/-! ## The local degree of a top cell -/

/-- **The local degree of a top cell is `±1`.**  For an `(k+1)`-simplex `σ` of a realized
`Δ`-complex, the inclusion of pairs `(cell_σ, punctCell_σ) → (X^{k+1}, X^{k+1} ∖ {b_σ})` is an
isomorphism on relative homology in degree `k+1`.

Both relative homology groups are computed by excising the closed `k`-skeleton: inside the
closed cell `cell_σ` the pair `(cell_σ, punctCell_σ)` has the same relative homology as its
open piece `(intCell_σ, intCell_σ ∖ {b_σ})` (`isIso_relHomologyMap_inclOpenCover_cell`), and
inside the skeleton `X^{k+1}` the pair `(X^{k+1}, X^{k+1} ∖ {b_σ})` has the same relative
homology as the same open piece (`isIso_relHomologyMap_inclOpenCover`, using that
`intCell_σ ∪ (X^{k+1} ∖ {b_σ}) = X^{k+1}` with both sets open).  The two middle pairs are
identified by the identity of `X`, which is a homeomorphism of pairs
(`isIso_relHomologyMap_pairHomOfHomeomorph`).  The two ways of composing the excisions agree
(`hcomp`), and cancelling the isomorphism on the left exhibits the map as a composite of three
isomorphisms. -/
theorem fold_isIso_cellIntoNeighbourhood (R : DeltaRealization K X) (k : ℕ)
    (σ : Fin (K.card (k + 1))) :
    IsIso (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)) := by
  classical
  haveI : T2Space X := R.t2
  -- ## openness of the open piece inside the skeleton
  have hUYeq : R.intCellPiece (k + 1) σ =
      (fun y : ↥(R.skelSet (k + 1)) => (y : X)) ⁻¹'
        ((R.skelSet k)ᶜ ∩
          (⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ}, R.cell (k + 1) τ.1)ᶜ) := by
    ext y
    constructor
    · intro h
      refine ⟨fun hk => h.2 k (Nat.lt_succ_self k) hk, ?_⟩
      rintro (hc : (y : X) ∈ ⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ}, R.cell (k + 1) τ.1)
      obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hc
      exact Set.disjoint_left.mp (intCell_disjoint R (k + 1) (Ne.symm τ.2))
        h (mem_intCell_of_mem_cell_of_not_mem_skelSet R k τ.1 hτ
          (h.2 k (Nat.lt_succ_self k)))
    · rintro ⟨hk, hc⟩
      have hmem : (y : X) ∈ skelDiff R k := ⟨y.2, hk⟩
      obtain ⟨τ, hτ⟩ := exists_intCell_of_mem_skelDiff R k hmem
      by_cases hστ : τ = σ
      · subst hστ; exact hτ
      · exact absurd (Set.mem_iUnion.mpr ⟨⟨τ, hστ⟩, R.intCell_subset_cell (k + 1) τ hτ⟩) hc
  have hUY : IsOpen (R.intCellPiece (k + 1) σ) := by
    rw [hUYeq]
    have hcl : IsClosed (⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ}, R.cell (k + 1) τ.1) :=
      isClosed_iUnion_of_finite
        (fun τ => (isCompact_range (R.toDeltaSimplexMap.cls (k + 1) τ.1).continuous).isClosed)
    exact ((isClosed_skelSet R k).isOpen_compl.preimage continuous_subtype_val).inter
      (hcl.isOpen_compl.preimage continuous_subtype_val)
  have hAY : IsOpen (R.punctNeighbourhood (k + 1) σ) := by
    have : R.punctNeighbourhood (k + 1) σ =
        (fun y : ↥(R.skelSet (k + 1)) => (y : X)) ⁻¹'
          ({R.cellBarycenter (k + 1) σ}ᶜ) := rfl
    rw [this]
    exact (isOpen_compl_singleton).preimage continuous_subtype_val
  have hcov : R.intCellPiece (k + 1) σ ∪ R.punctNeighbourhood (k + 1) σ = Set.univ := by
    ext y
    rcases eq_or_ne (y : X) (R.cellBarycenter (k + 1) σ) with h | h
    · refine iff_of_true (Or.inl ?_) trivial
      show (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ
      rw [h]
      exact DeltaSimplexMap.cellBarycenter_mem_intCell R (k + 1) σ
    · exact iff_of_true (Or.inr h) trivial
  haveI hcell : IsIso (relHomologyMap ZMod (k + 1)
      (PairHom.inclOpenCover (X := TopCat.of (R.cell (k + 1) σ))
        (cellIntPiece R (k + 1) σ) (cellPunctPiece R (k + 1) σ))) :=
    isIso_relHomologyMap_inclOpenCover_cell R (k + 1) (k + 1) σ
  haveI hskel : IsIso (relHomologyMap ZMod (k + 1)
      (PairHom.inclOpenCover (X := TopCat.of (R.skelSet (k + 1)))
        (R.intCellPiece (k + 1) σ) (R.punctNeighbourhood (k + 1) σ))) :=
    isIso_relHomologyMap_inclOpenCover hUY hAY hcov (k + 1)
  -- ## the homeomorphism between the two middles
  let Ac : Set ↥(cellIntPiece R (k + 1) σ) :=
    {x | (x : ↥(R.cell (k + 1) σ)) ∈ cellPunctPiece R (k + 1) σ}
  let By : Set ↥(R.intCellPiece (k + 1) σ) :=
    {y | (y : ↥(R.skelSet (k + 1))) ∈ R.punctNeighbourhood (k + 1) σ}
  let e : ↥(cellIntPiece R (k + 1) σ) ≃ₜ ↥(R.intCellPiece (k + 1) σ) :=
    { toFun := fun x => ⟨⟨(x : ↥(R.cell (k + 1) σ)), R.cell_subset_skelSet σ x.2.1⟩, x.2⟩
      invFun := fun y => ⟨⟨(y : ↥(R.skelSet (k + 1))), y.2.1⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  have hAB : ∀ x : ↥(cellIntPiece R (k + 1) σ), x ∈ Ac ↔ e x ∈ By := by
    intro x
    dsimp only [Ac, By]
    simp only [Set.mem_setOf_eq, cellPunctPiece_eq_compl_singleton,
      DeltaRealization.punctNeighbourhood]
    have hx : ((e x : ↥(R.intCellPiece (k + 1) σ)) : ↥(R.skelSet (k + 1))) =
        ⟨x.1, R.cell_subset_skelSet σ x.2.1⟩ := rfl
    rw [hx]
  let Φ : PairHom (TopCat.of (cellIntPiece R (k + 1) σ))
      (TopCat.of (R.intCellPiece (k + 1) σ)) Ac By :=
    Work.HomologyExtra.pairHomOfHomeomorph
      (X := TopCat.of (cellIntPiece R (k + 1) σ))
      (Y := TopCat.of (R.intCellPiece (k + 1) σ))
      (e := e) (A := Ac) (B := By) hAB
  have hcomp : (R.cellIntoNeighbourhood (k + 1) σ).comp
        (PairHom.inclOpenCover (X := TopCat.of (R.cell (k + 1) σ))
          (cellIntPiece R (k + 1) σ) (cellPunctPiece R (k + 1) σ))
      = (PairHom.inclOpenCover (X := TopCat.of (R.skelSet (k + 1)))
          (R.intCellPiece (k + 1) σ) (R.punctNeighbourhood (k + 1) σ)).comp Φ := by
    refine fold_pairHom_ext_of_hom_eq ?_
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    simp only [PairHom.comp, PairHom.inclOpenCover, TopCat.ofHom,
      CategoryTheory.ConcreteCategory.hom_ofHom, CategoryTheory.ConcreteCategory.comp_apply,
      DeltaRealization.cellIntoNeighbourhood, incl]
    exact Subtype.ext rfl
  haveI hhomeo : IsIso (relHomologyMap ZMod (k + 1) Φ) :=
    Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
      (X := TopCat.of (cellIntPiece R (k + 1) σ))
      (Y := TopCat.of (R.intCellPiece (k + 1) σ))
      (e := e) (A := Ac) (B := By) hAB (k + 1)
  have hsquare : relHomologyMap ZMod (k + 1)
        (PairHom.inclOpenCover (X := TopCat.of (R.cell (k + 1) σ))
          (cellIntPiece R (k + 1) σ) (cellPunctPiece R (k + 1) σ))
      ≫ relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)
      = relHomologyMap ZMod (k + 1) Φ
      ≫ relHomologyMap ZMod (k + 1)
        (PairHom.inclOpenCover (X := TopCat.of (R.skelSet (k + 1)))
          (R.intCellPiece (k + 1) σ) (R.punctNeighbourhood (k + 1) σ)) := by
    rw [← Work.HomologyExtra.relHomologyMap_comp, hcomp,
      Work.HomologyExtra.relHomologyMap_comp]
  have key : relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)
      = inv (relHomologyMap ZMod (k + 1)
          (PairHom.inclOpenCover (X := TopCat.of (R.cell (k + 1) σ))
            (cellIntPiece R (k + 1) σ) (cellPunctPiece R (k + 1) σ)))
        ≫ relHomologyMap ZMod (k + 1) Φ
        ≫ relHomologyMap ZMod (k + 1)
          (PairHom.inclOpenCover (X := TopCat.of (R.skelSet (k + 1)))
            (R.intCellPiece (k + 1) σ) (R.punctNeighbourhood (k + 1) σ)) := by
    rw [← Category.id_comp (relHomologyMap ZMod (k + 1) (R.cellIntoNeighbourhood (k + 1) σ)),
      ← IsIso.inv_hom_id (relHomologyMap ZMod (k + 1)
        (PairHom.inclOpenCover (X := TopCat.of (R.cell (k + 1) σ))
          (cellIntPiece R (k + 1) σ) (cellPunctPiece R (k + 1) σ))),
      Category.assoc, hsquare]
  rw [key]
  infer_instance


/-! ## The classes of the top cells are a basis -/

theorem isIso_fold_cellClassMap {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k : ℕ) :
    IsIso (biproduct.desc (fun σ : Fin (K.card (k + 1)) => cellClassMap R (k + 1) σ)) := by
  classical
  have hn1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  let D : Fin (K.card (k + 1)) → ModuleCat ℤ := fun _ =>
    relHomology ZMod (k + 1) (TopCat.of (StdSimplex ℝ (Fin (k + 1 + 1))))
      (StdSimplexBoundary (k + 1))
  let B : ModuleCat ℤ := relHomology ZMod (k + 1)
    (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1))) (R.punctSkelPiece (k + 1))
  have hiso : ∀ σ : Fin (K.card (k + 1)),
      IsIso (cellClassMap R (k + 1) σ ≫
        relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ)) := by
    intro σ
    rw [cellClassMap_comp_punctSkelToNeighbourhood R (k + 1) σ]
    haveI := cellClassMapCell_isIso R (k + 1) σ
    haveI := fold_isIso_cellIntoNeighbourhood R k σ
    infer_instance
  have hzero : ∀ σ τ : Fin (K.card (k + 1)), σ ≠ τ →
      cellClassMap R (k + 1) σ ≫
        relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) τ) = 0 :=
    fun σ τ h => cellClassMap_comp_punctSkelToNeighbourhood_eq_zero R k h
  haveI hinst : ∀ σ : Fin (K.card (k + 1)),
      IsIso (cellClassMap R (k + 1) σ ≫
        relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ)) := hiso
  set m := biproduct.desc (fun σ : Fin (K.card (k + 1)) => cellClassMap R (k + 1) σ) with hm
  set s := biproduct.lift (fun σ : Fin (K.card (k + 1)) =>
    relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ) ≫
      inv (cellClassMap R (k + 1) σ ≫
        relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ))) with hs
  have hs_apply : ∀ σ : Fin (K.card (k + 1)),
      s ≫ biproduct.π D σ =
        relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ) ≫
          inv (cellClassMap R (k + 1) σ ≫
            relHomologyMap ZMod (k + 1) (R.punctSkelToNeighbourhood (k + 1) σ)) := by
    intro σ
    rw [hs]
    rw [biproduct.lift_π]
  have hm_apply : ∀ σ : Fin (K.card (k + 1)),
      biproduct.ι D σ ≫ m = cellClassMap R (k + 1) σ := by
    intro σ
    rw [hm]
    exact biproduct.ι_desc _ σ
  have hms : m ≫ s = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro σ
    rw [← Category.assoc, hm_apply σ, Category.comp_id]
    apply biproduct.hom_ext
    intro τ
    rw [Category.assoc, hs_apply τ]
    by_cases h : σ = τ
    · subst h
      rw [biproduct.ι_π_self, ← Category.assoc, IsIso.hom_inv_id]
    · rw [biproduct.ι_π_ne D h, ← Category.assoc, hzero σ τ h, zero_comp]
  -- the rank computation
  obtain ⟨e₀⟩ := relHomology_punctSkel_succ_iso R k (k + 1)
  rw [if_pos rfl] at e₀
  haveI hNoeth : IsNoetherian ℤ ↥(∐ fun _ : Fin (K.card (k + 1)) => Work.Homology.ZMod) :=
    inferInstance
  haveI hBfin : Module.Finite ℤ ↥B := by
    refine Module.Finite.of_injective (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ) (e₀.hom.hom) ?_
    exact ((ConcreteCategory.isIso_iff_bijective e₀.hom).mp (Iso.isIso_hom e₀)).1
  haveI : IsIso (Work.HomologyExtra.simplexGenMap (k + 1)) :=
    simplexGenMap_isIso (k + 1) hn1
  have htest := asIso (Work.HomologyExtra.simplexGenMap (k + 1))
  let e₁ : (⨁ fun _ : Fin (K.card (k + 1)) => Work.Homology.ZMod) ≅ (⨁ D) :=
    biproduct.mapIso (fun _ => htest)
  let e : B ≅ (⨁ D) :=
    e₀ ≪≫ (biproduct.isoCoproduct (fun _ : Fin (K.card (k + 1)) => Work.Homology.ZMod)).symm
      ≪≫ e₁
  let f : B ⟶ B := s ≫ e.inv
  have hsurjS : Function.Surjective fun x : ↥B => ((s : B ⟶ ⨁ D) : ↥B → ↥(⨁ D)) x := by
    intro a
    refine ⟨(m : (⨁ D) ⟶ B) a, ?_⟩
    have hh : ((m ≫ s : (⨁ D) ⟶ (⨁ D)) : ↥(⨁ D) → ↥(⨁ D)) a = a := by
      rw [hms]; rfl
    simpa [CategoryTheory.ConcreteCategory.comp_apply] using hh
  have hsurjE : Function.Surjective fun x : ↥(⨁ D) => ((e.inv : (⨁ D) ⟶ B) : ↥(⨁ D) → ↥B) x := by
    intro b
    refine ⟨(e.hom : B ⟶ (⨁ D)) b, ?_⟩
    have hh := congrArg (fun φ : B ⟶ B => ((φ : ↥B → ↥B) b)) e.hom_inv_id
    simpa [CategoryTheory.ConcreteCategory.comp_apply] using hh
  have hsurjf : Function.Surjective fun x : ↥B => ((f : B ⟶ B) : ↥B → ↥B) x := by
    have h := hsurjE.comp hsurjS
    simpa [f, Function.comp_def, CategoryTheory.ConcreteCategory.comp_apply] using h
  haveI hfiso : IsIso f :=
    (ConcreteCategory.isIso_iff_bijective f).mpr
      ⟨OrzechProperty.injective_of_surjective_of_injective
        (i := (LinearMap.id : ↥B →ₗ[ℤ] ↥B)) (f := (f : B ⟶ B).hom)
        Function.injective_id hsurjf, hsurjf⟩
  have hright : s ≫ (e.inv ≫ inv f) = 𝟙 B := by
    rw [← Category.assoc, show s ≫ e.inv = f from rfl, IsIso.hom_inv_id]
  have hmr : m = e.inv ≫ inv f := by
    calc m = m ≫ 𝟙 B := (Category.comp_id m).symm
      _ = m ≫ (s ≫ (e.inv ≫ inv f)) := by rw [hright]
      _ = (m ≫ s) ≫ (e.inv ≫ inv f) := by rw [Category.assoc]
      _ = 𝟙 _ ≫ (e.inv ≫ inv f) := by rw [hms]
      _ = e.inv ≫ inv f := Category.id_comp _
  have h2 : s ≫ m = 𝟙 B := by rw [hmr, hright]
  show IsIso m
  exact ⟨s, hms, h2⟩


end

end Work.DeltaHomology

/-! ## The statement as delivered

The statement of the main theorem, repeated under the (doubled) namespace in which the file was
delivered; the flat name above is the one used by the rest of the project. -/

namespace Work.DeltaHomology

namespace Work.DeltaHomology

/-- **The classes of the top cells are a basis of `H_{k+1}(X^{k+1}, punctSkel (k+1))`.**  The
same statement under the (doubled) namespace in which the file was delivered; the flat name
`Work.DeltaHomology.isIso_fold_cellClassMap` above is the one used by the rest of the project. -/
theorem isIso_fold_cellClassMap {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ) :
    IsIso (biproduct.desc (fun σ : Fin (K.card (k + 1)) =>
      cellClassMap R (k + 1) σ)) :=
  _root_.Work.DeltaHomology.isIso_fold_cellClassMap R k

end Work.DeltaHomology

end Work.DeltaHomology
