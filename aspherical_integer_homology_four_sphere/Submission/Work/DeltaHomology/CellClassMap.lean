import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.DeltaHomology.GoodPairDefs
import Submission.Work.DeltaHomology.cell_relHomology_iso
import Submission.Work.HomologyExtra.SimplexClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The class of a top cell

For a realized `Δ`-complex and an `n`-simplex `σ`, this file builds the maps of pairs through
which the class of the characteristic map `χ σ` in the relative homology of the cell pair is
expressed:

* `DeltaRealization.skelPunctPairHom` — the map of pairs `(Δ^n, punctΔ^n) → (X^n, punctSkel n)`
  induced by `χ.cls n σ` (corestricted to the `n`-skeleton);
* `DeltaRealization.cellPairHomPunct` — the map of pairs `(Δ^n, punctΔ^n) → (cell_σ, punctCell_σ)`,
  the same map with target the closed cell;
* `cellClassMap` — the induced map on relative homology
  `ℤ ≅ H_n(Δ^n, ∂Δ^n) → H_n(X^n, punctSkel n)`, i.e. the class of `χ σ` in the `n`-skeleton pair.

The statement that `cellClassMap` is an isomorphism is the local-degree statement
(`[χ σ]` generates `H_n(cell_σ, punctCell_σ) ≅ ℤ`), the remaining input of the skeleta
induction of Hatcher's theorem; see `NOTES.md` §6.3, §7, §9.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-- The map of pairs `(Δ^n, punctΔ^n) → (X^n, punctSkel n)` induced by the characteristic map
of the simplex `σ` (corestricted to the `n`-skeleton). -/
def DeltaRealization.skelPunctPairHom (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    PairHom (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) (TopCat.of (R.toDeltaSimplexMap.skelSet n))
      (punctStdSimplex n)
      {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.punctSkel n} where
  hom := TopCat.ofHom (R.toDeltaSimplexMap.clsInSkelSet n le_rfl σ)
  mapsTo := fun w hw =>
    DeltaRealization.cls_mem_punctSkel R n σ (mem_punctStdSimplex_iff.mp hw)

@[simp]
theorem DeltaRealization.skelPunctPairHom_hom (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) :
    (R.skelPunctPairHom n σ).hom = TopCat.ofHom (R.toDeltaSimplexMap.clsInSkelSet n le_rfl σ) :=
  rfl

/-- The map of pairs `(Δ^n, punctΔ^n) → (cell_σ, punctCell_σ)` induced by the characteristic map
of the simplex `σ`. -/
def DeltaRealization.cellPairHomPunct (R : DeltaRealization K X) (n : ℕ)
    (σ : Fin (K.card n)) :
    PairHom (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) (TopCat.of (R.toDeltaSimplexMap.cell n σ))
      (punctStdSimplex n)
      {x : ↥(R.toDeltaSimplexMap.cell n σ) | (x : X) ∈ R.toDeltaSimplexMap.punctCell n σ} where
  hom := TopCat.ofHom ⟨fun w => ⟨R.toDeltaSimplexMap.cls n σ w, Set.mem_range_self w⟩,
    (R.toDeltaSimplexMap.cls n σ).continuous.subtype_mk _⟩
  mapsTo := fun w hw =>
    ⟨DeltaRealization.cls_mem_punctSkel R n σ (mem_punctStdSimplex_iff.mp hw), ⟨w, rfl⟩⟩

/-- **The class of the characteristic map of a simplex, as a map on relative homology.**  The
composite `ℤ ≅ H_n(Δ^n, ∂Δ^n) → H_n(X^n, punctSkel n)` sends the generator of the first group to
the class of the singular simplex `χ σ` in the relative homology of the pair `(X^n, punctSkel n)`. -/
def cellClassMap (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    relHomology ZMod n (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) (StdSimplexBoundary n) ⟶
      relHomology ZMod n (TopCat.of (R.toDeltaSimplexMap.skelSet n))
        {x : ↥(R.toDeltaSimplexMap.skelSet n) | (x : X) ∈ R.toDeltaSimplexMap.punctSkel n} :=
  relHomologyMap ZMod n (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex n)) ≫
    relHomologyMap ZMod n (R.skelPunctPairHom n σ)

/-- The same class, but with the closed cell as target:
`ℤ ≅ H_n(Δ^n, ∂Δ^n) → H_n(cell_σ, punctCell_σ)`. -/
def cellClassMapCell (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    relHomology ZMod n (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) (StdSimplexBoundary n) ⟶
      relHomology ZMod n (TopCat.of (R.toDeltaSimplexMap.cell n σ))
        {x : ↥(R.toDeltaSimplexMap.cell n σ) | (x : X) ∈ R.toDeltaSimplexMap.punctCell n σ} :=
  relHomologyMap ZMod n (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex n)) ≫
    relHomologyMap ZMod n (R.cellPairHomPunct n σ)

end

end Work.DeltaHomology
