import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtConeLift

open CategoryTheory Limits CochainComplex HomComplex

universe u v

/-- The differential of `Hom(-, singleFunctor C 0)` applied to the degree-`n` cochain
`toSingleMk` associated with `w₂ : R.complex.X n ⟶ S.X₂` is `(n+1).negOnePow` times the degree-`n+1`
cochain `toSingleMk` associated with the composite `R.complex.d (n+1) n ≫ w₂`. -/
theorem delta_toSingleMk_eq {C : Type u} [Category.{v} C] [Abelian C] {X : C}
    (R : ProjectiveResolution X) {S : ShortComplex C} {n : ℕ} (w₂ : R.complex.X n ⟶ S.X₂) :
    δ (↑n : ℤ) ((↑n : ℤ) + 1)
        (Cochain.toSingleMk ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂)
          (show -↑n + (↑n : ℤ) = 0 by simp)) =
      ((((↑n : ℤ) + 1).negOnePow : ℤˣ) : ℤ) • Cochain.toSingleMk
        ((R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫ (R.complex.d (n + 1) n ≫ w₂))
        (show -↑(n + 1) + ((↑n : ℤ) + 1) = 0 by simp) := by
  -- The identification of `R.cochainComplex` with `R.complex` is compatible with the
  -- differentials, so the two degree-`n+1` morphisms of the two sides agree.
  have key : R.cochainComplex.d (-↑(n + 1)) (-↑n) ≫
      ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂) =
      (R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫ (R.complex.d (n + 1) n ≫ w₂) := by
    rw [ProjectiveResolution.cochainComplex_d R (-↑(n+1)) (-↑n) (n+1) n rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- `Cochain.δ_toSingleMk` computes the differential of a `toSingleMk` cochain.
  rw [Cochain.δ_toSingleMk (K := R.cochainComplex) (X := S.X₂)
    ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂)
    (show -↑n + (↑n : ℤ) = 0 by simp) ((↑n : ℤ) + 1) (-↑(n+1))
    (show -↑(n + 1) + ((↑n : ℤ) + 1) = 0 by simp), key, Units.smul_def]

end Work.SSGRoute.ExtConeLift
