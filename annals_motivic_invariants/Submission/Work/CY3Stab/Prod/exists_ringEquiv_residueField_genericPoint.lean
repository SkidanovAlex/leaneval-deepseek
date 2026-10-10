import Mathlib
import Submission.Work.CY3Stab.Prod.AlgMapResidue

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.exists_ringEquiv_residueField_genericPoint`

The residue field of the affine scheme `Spec A` at its generic point is the fraction field
`FractionRing A` of `A` (for `A` a domain), and the structure map
`A → κ(genericPoint)` agrees with `algebraMap A (FractionRing A)` under this identification.

The proof identifies `genericPoint (Spec A)` with the prime ideal `⊥`
(`genericPoint_eq_bot_of_affine`), rewrites the residue field via `Spec.residueFieldIso` as
`Ideal.ResidueField ⊥`, and uses that the latter is a fraction ring of `A` because
`Ideal.ResidueField ⊥` is a fraction ring of `A ⧸ ⊥ ≃+* A`
(`RingTheory/LocalRing/ResidueField/Ideal.lean`).
-/

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [CommRing 𝕜]

/-- The structure map `𝕜 ⟶ κ(x)` of `Spec 𝕜` at a prime `x`, rewritten with
`Spec.algebraMap_residueFieldIso_inv` as `algebraMap 𝕜 κ(x)` followed by the inverse of
`Spec.residueFieldIso`. -/
lemma algMapResidue_id_eq_ofHom_residueFieldIso (x : PrimeSpectrum 𝕜) :
    algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) x =
      CommRingCat.ofHom (algebraMap 𝕜 (x.asIdeal.ResidueField)) ≫
        (Spec.residueFieldIso (CommRingCat.of 𝕜) x).inv := by
  rw [show algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜))) x =
      (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
        (Spec (CommRingCat.of 𝕜)).presheaf.germ ⊤ x trivial ≫
          (Spec (CommRingCat.of 𝕜)).residue x from by
    simp only [algMapResidue, Scheme.Hom.id_appTop, Category.id_comp]
    rfl]
  exact (Spec.algebraMap_residueFieldIso_inv (CommRingCat.of 𝕜) x).symm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme in
theorem exists_ringEquiv_residueField_genericPoint (A : Type) [CommRing A] [IsDomain A] : ∃ e : (Spec (CommRingCat.of A)).residueField (genericPoint (Spec (CommRingCat.of A))) ≃+* FractionRing A, ∀ a : A, e ((Work.CY3Stab.Prod.algMapResidue (𝟙 (Spec (CommRingCat.of A))) (genericPoint (Spec (CommRingCat.of A)))).hom a) = algebraMap A (FractionRing A) a := by
  rw [genericPoint_eq_bot_of_affine (CommRingCat.of A)]
  -- `Φ` identifies `κ(⊥)` with `Ideal.ResidueField ⊥`, `Ψ` identifies the latter with
  -- `FractionRing A`.
  let Φ : (Spec (CommRingCat.of A)).residueField (⊥ : PrimeSpectrum (CommRingCat.of A)) ≃+*
      ((⊥ : Ideal A).ResidueField) :=
    (Spec.residueFieldIso (CommRingCat.of A)
      (⊥ : PrimeSpectrum (CommRingCat.of A))).commRingCatIsoToRingEquiv
  let Ψ : ((⊥ : Ideal A).ResidueField) ≃+* FractionRing A :=
    (FractionRing.algEquiv A ((⊥ : Ideal A).ResidueField)).symm.toRingEquiv
  refine ⟨Φ.trans Ψ, fun a ↦ ?_⟩
  -- The structure map at `⊥` is `algebraMap A (Ideal.ResidueField ⊥)` composed with `Φ.symm`.
  have key : (Work.CY3Stab.Prod.algMapResidue (𝟙 (Spec (CommRingCat.of A)))
        (⊥ : PrimeSpectrum (CommRingCat.of A))).hom a =
      Φ.symm (algebraMap A ((⊥ : Ideal A).ResidueField) a) := by
    rw [algMapResidue_id_eq_ofHom_residueFieldIso (𝕜 := A)
      (⊥ : PrimeSpectrum (CommRingCat.of A))]
    rfl
  rw [key, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact (FractionRing.algEquiv A ((⊥ : Ideal A).ResidueField)).symm.commutes a

end

end Work.CY3Stab.Prod
