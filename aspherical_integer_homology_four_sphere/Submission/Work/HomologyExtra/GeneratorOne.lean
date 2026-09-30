import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.RelProjIso
import Submission.Work.HomologyExtra.epi_simplexBoundaryClass_of_epi_simplexGenMap
import Submission.Work.HomologyExtra.simplexBoundaryClass_one_epi
import Submission.Work.HomologyExtra.simplexStar_contractible
import Submission.Work.HomologyExtra.isIso_relHomologyMap_simplexFacePairHom
import Submission.Work.HomologyExtra.SimplexPairHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The identity simplex generates `H₁(Δ¹, ∂Δ¹)`

The remaining case of the generator statement, `n = 1`.  It is genuinely different from the cases
`n ≥ 2` (`Submission/Work/HomologyExtra/Generator.lean`), where the class of the identity simplex of
`Δ^{k+2}` is the inverse image of the fundamental class of `∂Δ^{k+2}` under the **isomorphism**
`H_{k+1}(Δ^{k+2}, ∂Δ^{k+2}) ≅ H_{k+1}(∂Δ^{k+2})`.  In degree `1` the connecting map
`H₁(Δ¹,∂Δ¹) → H₀(∂Δ¹)` is only injective (its cokernel is `H₀(Δ¹) = ℤ`), so there is no
isomorphism to run that argument with.

## The proof

Let `X = ∂Δ²` and `B = simplexStar 1 ⊆ X`, the closed star of the last vertex — the closed
neighbourhood of the last face `Δ¹ ⊆ ∂Δ²`.  Three ingredients, all previously proved:

* `simplexBoundaryClass_comp_relProjHom 1` — the class of the fundamental cycle `F₀ - F₁` of
  `∂Δ²` in the relative homology `H₁(X,B)` is `±` the image of the class of the identity simplex
  `ι₁` of `Δ¹` under the face map of pairs `Φ : (Δ¹,∂Δ¹) → (X,B)`;
* `simplexBoundaryClass_one_epi` — the fundamental cycle generates `H₁(∂Δ²) ≅ ℤ`;
* `isIso_relHomologyMap_simplexFacePairHom 1` — `Φ` induces an isomorphism on relative homology in
  degree `1`.

The one new input is that the projection `p : H₁(X) ⟶ H₁(X,B)` is an isomorphism.  Since `B` is
contractible, `H₁(B) = 0` and `H₀(B) → H₀(X)` is injective (`B` is path-connected, and this is
the naturality of the augmentation `ε`), so `p` is both a monomorphism and an epimorphism by the
exactness of the long exact sequence of the pair `(X,B)`: this is
`Work.HomologyExtra.isIso_relProjHom_one` in `Submission/Work/HomologyExtra/RelProjIso.lean`.

With `p` invertible, the square `simplexBoundaryClass 1 ≫ p = ±(simplexGenMap 1 ≫ Φ)` transfers
epimorphicity from `simplexBoundaryClass 1` to `simplexGenMap 1`: the scalar `lastSign 1 = ±1` is
invertible and `Φ` is invertible.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The identity simplex generates `H₁(Δ¹,∂Δ¹)`.** -/
theorem epi_simplexGenMap_one : Epi (simplexGenMap 1) := by
  haveI hcontr : ContractibleSpace (TopCat.of (simplexStar 1)) := simplexStar_contractible 1
  have h1z : IsZero (Work.Homology.singHomology Work.Homology.ZMod 1
      (TopCat.of (simplexStar 1))) := by
    have h := Work.Homology.isZero_singHomology_succ_of_contractibleSpace Work.Homology.ZMod
      (TopCat.of (simplexStar 1)) 0
    simpa using h
  haveI hp : IsIso (Work.Homology.relProjHom Work.Homology.ZMod 1 (boundarySpace 2)
      (simplexStar 1)) :=
    isIso_relProjHom_one (boundarySpace 2) (simplexStar 1) h1z
      (mono_homologyMap_inclChain_zero (boundarySpace 2) (simplexStar 1))
  haveI hφ : IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1)) :=
    isIso_relHomologyMap_simplexFacePairHom 1 le_rfl
  haveI hb : Epi (simplexBoundaryClass 1) := simplexBoundaryClass_one_epi
  have hiso : IsIso (lastSign 1 • 𝟙 Work.Homology.ZMod) := by
    refine ⟨lastSign 1 • 𝟙 Work.Homology.ZMod, ?_, ?_⟩ <;>
      rw [Preadditive.zsmul_comp, Category.id_comp, smul_smul, lastSign_sq, one_smul]
  have hE : Epi (lastSign 1 • (simplexGenMap 1 ≫
      Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1))) := by
    rw [← simplexBoundaryClass_comp_relProjHom 1]
    exact epi_comp _ _
  haveI h1 : Epi (simplexGenMap 1 ≫
      Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1)) := by
    have hsplit : lastSign 1 • (simplexGenMap 1 ≫
        Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1)) =
        (lastSign 1 • 𝟙 Work.Homology.ZMod) ≫ (simplexGenMap 1 ≫
          Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1)) := by
      rw [Preadditive.zsmul_comp, Category.id_comp]
    rw [hsplit] at hE
    exact epi_of_epi (lastSign 1 • 𝟙 Work.Homology.ZMod) (simplexGenMap 1 ≫
      Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1))
  rw [show simplexGenMap 1 = (simplexGenMap 1 ≫
      Work.Homology.relHomologyMap Work.Homology.ZMod 1 (simplexFacePairHom 1)) ≫
      CategoryTheory.inv (Work.Homology.relHomologyMap Work.Homology.ZMod 1
        (simplexFacePairHom 1))
      from by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
  exact epi_comp _ _

/-- **The identity simplex generates `H₁(Δ¹,∂Δ¹)`**: the map `ℤ → H₁(Δ¹,∂Δ¹)`, `1 ↦ [ι₁]` is an
isomorphism. -/
theorem isIso_simplexGenMap_one : IsIso (simplexGenMap 1) :=
  isIso_simplexGenMap_of_epi 1 epi_simplexGenMap_one (relHomology_simplexPair_top 1 le_rfl)

end

end Work.HomologyExtra
