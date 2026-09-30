import Mathlib
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.openCoverInclPair
import Submission.Work.DeltaHomology.cell_relHomology_iso
import Submission.Work.DeltaHomology.relHomology_stdSimplexBoundary
import Submission.Work.DeltaHomology.exists_homeomorph_intCell
import Submission.Work.DeltaHomology.exists_homeomorph_cellIntPiece
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.cellPairHomPunct_comp_inclOpenCover
import Submission.Work.HomologyExtra.RelChainMapFunctor
import Submission.Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **The collar map of the standard simplex is an isomorphism.**  The inclusion of pairs
`(Δⁿ, ∂Δⁿ) ⟶ (Δⁿ, Δⁿ ∖ {b})` induces an isomorphism on relative homology in every degree
(the boundary is a deformation retract of the punctured simplex). -/
theorem isIso_relHomologyMap_stdSimplexBoundary_punctStdSimplex (n m : ℕ) :
    IsIso (relHomologyMap ZMod m (pairHomOfSubset
      (X := TopCat.of (StdSimplex ℝ (Fin (n + 1))))
      (stdSimplexBoundary_subset_punctStdSimplex n))) :=
  isIso_relHomologyMap_of_deformationRetract (stdSimplexBoundary_subset_punctStdSimplex n)
    (nonempty_deformationRetract_punctStdSimplex n).some m

/-- **The characteristic map of a top cell has degree `±1`.**  The map of pairs
`(Δⁿ, Δⁿ ∖ {b}) ⟶ (cell_σ, punctCell_σ)` induced by `χ.cls n σ` is an isomorphism on relative
homology in degree `n`.

Proof.  Both relative homology groups are the homology of an open piece of the pair, and the two
open pieces are identified by the characteristic map:

* `P₁ : (intΔⁿ, intΔⁿ ∖ {b}) ⟶ (Δⁿ, Δⁿ ∖ {b})` — the inclusion of the open simplex, an
  isomorphism on relative homology by excision (`isIso_relHomologyMap_inclOpenCover_stdSimplex`);
* `P₃ : (intCell_σ, intCell_σ ∖ {b_σ}) ⟶ (cell_σ, cell_σ ∖ {b_σ})` — the inclusion of the open
  cell, an isomorphism by excision (`isIso_relHomologyMap_inclOpenCover_cell`);
* `P₄ : (intΔⁿ, intΔⁿ ∖ {b}) ⟶ (intCell_σ, intCell_σ ∖ {b_σ})` — the characteristic map
  restricted to the open simplex, which is a homeomorphism of pairs
  (`exists_homeomorph_cellIntPiece`), hence an isomorphism on relative homology
  (`isIso_relHomologyMap_pairHomOfHomeomorph`).

The two composites `P₂ ∘ P₁` and `P₃ ∘ P₄` agree as maps of pairs
(`cellPairHomPunct_comp_inclOpenCover`), where `P₂ = χ.cellPairHomPunct n σ`.  Passing to relative
homology and cancelling the isomorphism `H_n(P₁)` gives
`H_n(P₂) = H_n(P₁)⁻¹ ≫ H_n(P₄) ≫ H_n(P₃)`, a composite of isomorphisms. -/
theorem isIso_cellPairHomPunct {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    IsIso (relHomologyMap ZMod n (R.cellPairHomPunct n σ)) := by
  obtain ⟨e, he, hbar⟩ := exists_homeomorph_cellIntPiece R n σ
  have hAB : ∀ w : ↥(openSimplexSet n),
      w ∈ {y : ↥(openSimplexSet n) | (y : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n} ↔
      e w ∈ {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ} := by
    intro w
    have h2 : e w ∈ {y : ↥(cellIntPiece R n σ) |
          (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ} ↔
        ((e w : ↥(R.toDeltaSimplexMap.cell n σ)) : X) ≠
          R.toDeltaSimplexMap.cellBarycenter n σ := by
      rw [Set.mem_setOf_eq, cellPunctPiece_eq_compl_singleton]
      exact Iff.rfl
    rw [h2]
    exact hbar w
  let P₁ : PairHom (TopCat.of (openSimplexSet n)) (TopCat.of (StdSimplex ℝ (Fin (n + 1))))
      {y : ↥(openSimplexSet n) | (y : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n}
      (punctStdSimplex n) :=
    Work.Homology.PairHom.inclOpenCover (X := TopCat.of (StdSimplex ℝ (Fin (n + 1))))
      (openSimplexSet n) (punctStdSimplex n)
  let P₃ : PairHom (TopCat.of (cellIntPiece R n σ)) (TopCat.of (R.toDeltaSimplexMap.cell n σ))
      {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ}
      (cellPunctPiece R n σ) :=
    Work.Homology.PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
      (cellIntPiece R n σ) (cellPunctPiece R n σ)
  let P₄ : PairHom (TopCat.of (openSimplexSet n)) (TopCat.of (cellIntPiece R n σ))
      {y : ↥(openSimplexSet n) | (y : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n}
      {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ} :=
    Work.HomologyExtra.pairHomOfHomeomorph
      (X := TopCat.of (openSimplexSet n)) (Y := TopCat.of (cellIntPiece R n σ))
      (A := {y : ↥(openSimplexSet n) |
        (y : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n})
      (B := {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ}) e hAB
  have hsq : (R.cellPairHomPunct n σ).comp P₁ = P₃.comp P₄ :=
    cellPairHomPunct_comp_inclOpenCover R n σ e he hAB
  haveI hP₁ : IsIso (relHomologyMap ZMod n P₁) :=
    isIso_relHomologyMap_inclOpenCover_stdSimplex n n
  haveI hP₃ : IsIso (relHomologyMap ZMod n P₃) :=
    isIso_relHomologyMap_inclOpenCover_cell R n n σ
  haveI hP₄ : IsIso (relHomologyMap ZMod n P₄) :=
    Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
      (X := TopCat.of (openSimplexSet n)) (Y := TopCat.of (cellIntPiece R n σ))
      (A := {y : ↥(openSimplexSet n) |
        (y : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n})
      (B := {y : ↥(cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ cellPunctPiece R n σ}) e hAB n
  have hsquare : relHomologyMap ZMod n P₁ ≫ relHomologyMap ZMod n (R.cellPairHomPunct n σ)
      = relHomologyMap ZMod n P₄ ≫ relHomologyMap ZMod n P₃ := by
    rw [← Work.HomologyExtra.relHomologyMap_comp, hsq]
    exact Work.HomologyExtra.relHomologyMap_comp ZMod n P₄ P₃
  have key : relHomologyMap ZMod n (R.cellPairHomPunct n σ)
      = inv (relHomologyMap ZMod n P₁) ≫ relHomologyMap ZMod n P₄
          ≫ relHomologyMap ZMod n P₃ := by
    rw [← Category.id_comp (relHomologyMap ZMod n (R.cellPairHomPunct n σ)),
      ← IsIso.inv_hom_id (relHomologyMap ZMod n P₁), Category.assoc, hsquare]
  rw [key]
  infer_instance

/-- **The characteristic map of a top cell has degree `±1`.**  For a realized `Δ`-complex, an
`n`-simplex `σ` and the map of pairs `(Δⁿ, ∂Δⁿ) → (cell_σ, punctCell_σ)` induced by `χ.cls n σ`,
the induced map on the top relative homology is an isomorphism; equivalently, the class of `χ σ`
generates `Hₙ(cell_σ, punctCell_σ) ≅ ℤ`.  This is the single remaining mathematical input of the
skeleta induction (Hatcher 2.27).  The target is `≅ ℤ` in degree `n` and `0` otherwise by
`cell_relHomology_iso`, the source is `≅ ℤ` in degree `n` by `relHomology_stdSimplexBoundary`.

The map `cellClassMapCell R n σ` is the composite of the collar
`Hₙ(Δⁿ, ∂Δⁿ) ≅ Hₙ(Δⁿ, Δⁿ ∖ {b})` (`isIso_relHomologyMap_stdSimplexBoundary_punctStdSimplex`)
with the map induced by the characteristic map
(`isIso_cellPairHomPunct`), so it is an isomorphism as a composite of isomorphisms. -/
theorem cellClassMapCell_isIso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    IsIso (cellClassMapCell R n σ) := by
  show IsIso (relHomologyMap ZMod n (pairHomOfSubset
      (X := TopCat.of (StdSimplex ℝ (Fin (n + 1))))
      (stdSimplexBoundary_subset_punctStdSimplex n)) ≫
    relHomologyMap ZMod n (R.cellPairHomPunct n σ))
  haveI := isIso_relHomologyMap_stdSimplexBoundary_punctStdSimplex n n
  haveI := isIso_cellPairHomPunct R n σ
  infer_instance

end

end Work.DeltaHomology

/-! ## The flat names used by the rest of the project

The file as delivered carries two identical `namespace Work.DeltaHomology` lines, so the
declarations above are registered in the namespace `Work.DeltaHomology.Work.DeltaHomology`.
The statements below are the same declarations, restated under the flat names
`Work.DeltaHomology.*` by which the rest of the project refers to them. -/

noncomputable section

/-- **The collar map of the standard simplex is an isomorphism** (flat name). -/
theorem isIso_relHomologyMap_stdSimplexBoundary_punctStdSimplex (n m : ℕ) :
    IsIso (relHomologyMap ZMod m (pairHomOfSubset
      (X := TopCat.of (StdSimplex ℝ (Fin (n + 1))))
      (stdSimplexBoundary_subset_punctStdSimplex n))) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.isIso_relHomologyMap_stdSimplexBoundary_punctStdSimplex
    n m

/-- **The characteristic map of a top cell has degree `±1`** (flat name). -/
theorem isIso_cellPairHomPunct {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    IsIso (relHomologyMap ZMod n (R.cellPairHomPunct n σ)) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.isIso_cellPairHomPunct R n σ

/-- **The characteristic map of a top cell has degree `±1`.**  For a realized `Δ`-complex, an
`n`-simplex `σ` and the map of pairs `(Δⁿ, ∂Δⁿ) → (cell_σ, punctCell_σ)` induced by `χ.cls n σ`,
the induced map on the top relative homology is an isomorphism; equivalently, the class of `χ σ`
generates `Hₙ(cell_σ, punctCell_σ) ≅ ℤ`.  This is the single remaining mathematical input of the
skeleta induction (Hatcher 2.27).  The target is `≅ ℤ` in degree `n` and `0` otherwise by
`cell_relHomology_iso`, the source is `≅ ℤ` in degree `n` by `relHomology_stdSimplexBoundary`.

This is the flat-name restatement of the theorem proved above. -/
theorem cellClassMapCell_isIso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    IsIso (cellClassMapCell R n σ) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.cellClassMapCell_isIso R n σ

end
