import Mathlib
import Submission.Work.CY3Stab.Prod.AlgMapResidue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The structure map `𝕜 ⟶ κ(s)` for `s : Spec 𝕜`, `𝕜` a field, is an isomorphism

For a field `𝕜` the residue field of `Spec 𝕜` at its unique point is `𝕜` itself, so the
structure map `algMapResidue (𝟙 (Spec 𝕜)) s : 𝕜 ⟶ κ(s)` is an isomorphism.

The proof identifies `algMapResidue (𝟙 (Spec 𝕜)) s` with the composite

`𝕜 ⟶ κ(s.asIdeal) ≅ κ(s)`

of two isomorphisms, using `Scheme.Spec.algebraMap_residueFieldIso_inv`: the algebra map
`𝕜 ⟶ s.asIdeal.ResidueField` is an isomorphism because a prime ideal of a field is `⊥`
(`Ideal.algEquivResidueFieldOfField`), and `Scheme.Spec.residueFieldIso` is an isomorphism.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme in
theorem isIso_algMapResidue_id (𝕜 : Type) [Field 𝕜] (s : Spec (CommRingCat.of 𝕜)) : IsIso (Work.CY3Stab.Prod.algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) s) := by
  haveI hprime : s.asIdeal.IsPrime := s.isPrime
  -- `algMapResidue` of the identity is the composite of the algebra map `𝕜 ⟶ κ(s.asIdeal)`
  -- with the canonical isomorphism `κ(s.asIdeal) ≅ κ(s)`.
  have key : CommRingCat.ofHom (algebraMap 𝕜 s.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of 𝕜) s).inv =
      Work.CY3Stab.Prod.algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) s := by
    have h1 := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of 𝕜) s
    rw [h1]
    simp [Work.CY3Stab.Prod.algMapResidue, Scheme.Γevaluation, Scheme.evaluation]
  rw [← key]
  -- `𝕜 ⟶ κ(s.asIdeal)` is `algebraMap`, which is bijective since `s.asIdeal = ⊥` in a field.
  haveI hiso1 : IsIso (CommRingCat.ofHom (algebraMap 𝕜 s.asIdeal.ResidueField)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (Ideal.algEquivResidueFieldOfField s.asIdeal).bijective
  infer_instance

end

end Work.CY3Stab.Prod
