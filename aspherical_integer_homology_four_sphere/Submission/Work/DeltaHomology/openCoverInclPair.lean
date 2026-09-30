import Mathlib
import Submission.Work.DeltaHomology.cell_relHomology_iso
import Submission.Work.DeltaHomology.punctCell_eq_sdiff
import Submission.Work.HomologyExtra.RelChainMapFunctor
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Excision for the inclusion of an open piece of a pair

If `U, A ⊆ X` are open and `U ∪ A = X`, the inclusion of pairs `(U, U ∩ A) → (X, A)` induces an
isomorphism on relative homology (`Work.Cohomology.excision_relChainsMap_isIso`).  This file
records that statement in the `PairHom` form used by the cell-class computation, together with the
two instances needed there:

* the pair `(Δⁿ ∖ ∂Δⁿ, Δⁿ ∖ {b}) → (Δⁿ, Δⁿ ∖ {b})` of the standard simplex;
* the pair `(intCellσ, intCellσ ∖ {bσ}) → (cellσ, cellσ ∖ {bσ})` of a cell of a realized
  `Δ`-complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.Homology

/-- The inclusion of pairs `(U, U ∩ A) ⟶ (X, A)` when `U, A ⊆ X`. -/
def PairHom.inclOpenCover {X : TopCat} (U A : Set X) :
    PairHom (TopCat.of U) X {y : ↥U | (y : X) ∈ A} A where
  hom := incl U
  mapsTo := fun _ hy => hy

end Work.Homology

namespace Work.DeltaHomology

variable {K : DeltaCx} {X : TopCat}

/-- `relChainsMapOf` depends only on the two maps, not on the proof of compatibility. -/
theorem relChainsMapOf_congr {X Y : TopCat} {A : Set X} {B : Set Y}
    {f f' : X ⟶ Y} {g g' : TopCat.of A ⟶ TopCat.of B} (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  subst hf
  subst hg
  exact congrArg (fun w => Work.Cohomology.relChainsMapOf X Y A B f g w) (Subsingleton.elim w w')

/-- **Excision, in the form of the inclusion of pairs.**  If `U, A ⊆ X` are open and
`U ∪ A = X`, the inclusion of pairs `(U, U ∩ A) ⟶ (X, A)` induces an isomorphism on relative
homology in every degree. -/
theorem isIso_relHomologyMap_inclOpenCover {X : TopCat} {U A : Set X}
    (hU : IsOpen U) (hA : IsOpen A) (hcov : U ∪ A = Set.univ) (m : ℕ) :
    IsIso (relHomologyMap ZMod m
      (Work.Homology.PairHom.inclOpenCover U A)) := by
  have hchain : relChainMap ZMod
        (Work.Homology.PairHom.inclOpenCover U A) = Work.Cohomology.relChainsMap X U A := by
    rw [Work.HomologyExtra.relChainMap_eq_relChainsMapOf]
    unfold Work.Cohomology.relChainsMap
    exact relChainsMapOf_congr rfl rfl _ _
  show IsIso (HomologicalComplex.homologyMap
    (relChainMap ZMod (Work.Homology.PairHom.inclOpenCover U A)) m)
  rw [hchain]
  exact Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov m

/-! ## The standard simplex -/

/-- **Excision for the standard simplex.**  The inclusion of pairs
`(intΔⁿ, intΔⁿ ∖ {b}) ⟶ (Δⁿ, Δⁿ ∖ {b})` is an isomorphism on relative homology. -/
theorem isIso_relHomologyMap_inclOpenCover_stdSimplex (n m : ℕ) :
    IsIso (relHomologyMap ZMod m
      (Work.Homology.PairHom.inclOpenCover (X := TopCat.of (StdSimplex ℝ (Fin (n + 1))))
        (openSimplexSet n) (punctStdSimplex n))) := by
  refine isIso_relHomologyMap_inclOpenCover (isOpen_setOf_isOpenSimplexPoint n)
    (isOpen_punctStdSimplex n) ?_ m
  ext w
  rcases eq_or_ne w (simplexBarycenter n) with h | h
  · exact iff_of_true (Or.inl (h ▸ isOpenSimplexPoint_simplexBarycenter n)) trivial
  · exact iff_of_true (Or.inr h) trivial

/-! ## The cell of a realized `Δ`-complex -/

/-- The open cell `intCell n σ`, viewed as a subset of the closed cell `cell n σ`. -/
abbrev cellIntPiece (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    Set ↥(R.toDeltaSimplexMap.cell n σ) :=
  {x | (x : X) ∈ R.toDeltaSimplexMap.intCell n σ}

/-- The punctured cell `punctCell n σ`, viewed as a subset of the closed cell `cell n σ`. -/
abbrev cellPunctPiece (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    Set ↥(R.toDeltaSimplexMap.cell n σ) :=
  {x | (x : X) ∈ R.toDeltaSimplexMap.punctCell n σ}

theorem mem_cellIntPiece {R : DeltaRealization K X} {n : ℕ} {σ : Fin (K.card n)}
    {x : ↥(R.toDeltaSimplexMap.cell n σ)} :
    x ∈ cellIntPiece R n σ ↔ (x : X) ∈ R.toDeltaSimplexMap.intCell n σ := Iff.rfl

theorem mem_cellPunctPiece {R : DeltaRealization K X} {n : ℕ} {σ : Fin (K.card n)}
    {x : ↥(R.toDeltaSimplexMap.cell n σ)} :
    x ∈ cellPunctPiece R n σ ↔ (x : X) ∈ R.toDeltaSimplexMap.punctCell n σ := Iff.rfl

/-- The punctured cell piece is the complement of the barycentre in the closed cell. -/
theorem cellPunctPiece_eq_compl_singleton (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) :
    cellPunctPiece R n σ =
      {x : ↥(R.toDeltaSimplexMap.cell n σ) |
        (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ} := by
  ext x
  rw [mem_cellPunctPiece, punctCell_eq_sdiff]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

/-- The open cell piece is open in the closed cell. -/
theorem isOpen_cellIntPiece (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    IsOpen (cellIntPiece R n σ) := by
  classical
  let χ := R.toDeltaSimplexMap
  let C : Set X := χ.cell n σ
  have hInt : χ.intCell n σ = C ∩ (⋃ i : {j : ℕ // j < n}, χ.skelSet i)ᶜ := by
    rw [DeltaSimplexMap.intCell_eq_sdiff, Set.sdiff_eq]
  have hUeq : cellIntPiece R n σ =
      (Subtype.val : ↥C → X) ⁻¹' (⋃ i : {j : ℕ // j < n}, χ.skelSet i)ᶜ := by
    ext x
    simp only [mem_cellIntPiece, Set.mem_preimage]
    rw [hInt]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [hUeq]
  haveI : Finite {j : ℕ // j < n} := Set.finite_Iio n
  exact (isClosed_iUnion_of_finite fun i : {j : ℕ // j < n} =>
    isClosed_skelSet R i).isOpen_compl.preimage continuous_subtype_val

/-- The punctured cell piece is open in the closed cell. -/
theorem isOpen_cellPunctPiece (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    IsOpen (cellPunctPiece R n σ) := by
  rw [cellPunctPiece_eq_compl_singleton]
  haveI : T1Space X := R.t2.t1Space
  exact (isOpen_compl_singleton (x := R.toDeltaSimplexMap.cellBarycenter n σ)).preimage
    continuous_subtype_val

/-- **Excision for a cell.**  The inclusion of pairs
`(intCell σ, intCell σ ∖ {bσ}) ⟶ (cell σ, cell σ ∖ {bσ})` is an isomorphism on relative
homology. -/
theorem isIso_relHomologyMap_inclOpenCover_cell (R : DeltaRealization K X) (n m : ℕ)
    (σ : Fin (K.card n)) :
    IsIso (relHomologyMap ZMod m
      (Work.Homology.PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
        (cellIntPiece R n σ) (cellPunctPiece R n σ))) := by
  refine isIso_relHomologyMap_inclOpenCover (isOpen_cellIntPiece R n σ)
    (isOpen_cellPunctPiece R n σ) ?_ m
  rw [cellPunctPiece_eq_compl_singleton]
  ext x
  rcases eq_or_ne (x : X) (R.toDeltaSimplexMap.cellBarycenter n σ) with h | h
  · refine iff_of_true (Or.inl ?_) trivial
    show (x : X) ∈ R.toDeltaSimplexMap.intCell n σ
    rw [h]
    exact DeltaSimplexMap.cellBarycenter_mem_intCell R n σ
  · exact iff_of_true (Or.inr h) trivial

end Work.DeltaHomology
