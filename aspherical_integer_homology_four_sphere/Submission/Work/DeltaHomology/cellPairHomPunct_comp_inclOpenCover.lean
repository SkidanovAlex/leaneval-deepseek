import Mathlib
import Submission.Work.DeltaHomology.openCoverInclPair
import Submission.Work.DeltaHomology.CellClassMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Naturality of the punctured pair maps

The map of pairs `(Δⁿ, punctΔⁿ) → (cell_σ, punctCell_σ)` induced by the characteristic map of
`σ` (`DeltaRealization.cellPairHomPunct`) is the composite of the excision inclusions
`(Δⁿ, punctΔⁿ) → (intΔⁿ, intΔⁿ∖{b})` and `(intCell_σ, intCell_σ∖{b_σ}) → (cell_σ, punctCell_σ)`
along the homeomorphism `e : intΔⁿ ≃ₜ intCell_σ`.  This is the naturality square identifying the
two ways of computing the class of `χ σ` on the cell pair.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-- Two maps of pairs with the same underlying continuous map are equal (the `mapsTo` fields live
in a proposition). -/
private theorem pairHom_ext_of_hom_eq {X Y : TopCat} {A : Set X} {B : Set Y}
    {Φ Ψ : PairHom X Y A B} (h : Φ.hom = Ψ.hom) : Φ = Ψ := by
  obtain ⟨f, hf⟩ := Φ
  obtain ⟨g, hg⟩ := Ψ
  subst h
  rw [Subsingleton.elim hf hg]

theorem cellPairHomPunct_comp_inclOpenCover {K : Work.DeltaHomology.DeltaCx} {X : TopCat}
    (R : Work.DeltaHomology.DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n))
    (e : ↥(Work.DeltaHomology.openSimplexSet n) ≃ₜ ↥(Work.DeltaHomology.cellIntPiece R n σ))
    (he : ∀ w : ↥(Work.DeltaHomology.openSimplexSet n),
      ((e w : ↥(R.toDeltaSimplexMap.cell n σ)) : X) = R.toDeltaSimplexMap.cls n σ w)
    (hAB : ∀ w : ↥(Work.DeltaHomology.openSimplexSet n),
      w ∈ {y : ↥(Work.DeltaHomology.openSimplexSet n) |
        (y : Convexity.StdSimplex ℝ (Fin (n + 1))) ∈ Work.DeltaHomology.punctStdSimplex n} ↔
      e w ∈ {y : ↥(Work.DeltaHomology.cellIntPiece R n σ) |
        (y : ↥(R.toDeltaSimplexMap.cell n σ)) ∈ Work.DeltaHomology.cellPunctPiece R n σ}) :
    (R.cellPairHomPunct n σ).comp
        (Work.Homology.PairHom.inclOpenCover (X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))))
          (Work.DeltaHomology.openSimplexSet n) (Work.DeltaHomology.punctStdSimplex n))
      = (Work.Homology.PairHom.inclOpenCover (X := TopCat.of (R.toDeltaSimplexMap.cell n σ))
          (Work.DeltaHomology.cellIntPiece R n σ) (Work.DeltaHomology.cellPunctPiece R n σ)).comp
        (Work.HomologyExtra.pairHomOfHomeomorph e hAB) := by
  refine pairHom_ext_of_hom_eq ?_
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  simp only [PairHom.comp, PairHom.inclOpenCover, Work.HomologyExtra.pairHomOfHomeomorph,
    Work.Homology.homeomorphTopCatHom, TopCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom,
    CategoryTheory.ConcreteCategory.comp_apply, DeltaRealization.cellPairHomPunct, incl]
  exact Subtype.ext (he w).symm

end Work.DeltaHomology
