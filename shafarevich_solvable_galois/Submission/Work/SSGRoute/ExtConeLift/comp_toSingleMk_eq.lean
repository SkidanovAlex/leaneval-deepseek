import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtConeLift

open CategoryTheory Limits CochainComplex HomComplex

universe u v

/-- The composition of the degree-`n+1` cochain `toSingleMk` associated with `w₁ : R.complex.X (n+1) ⟶ S.X₁`
with the (degree `0`) cochain associated with `S.f` is the `toSingleMk` associated with the composite
`R.complex.d (n+1) n ≫ w₂` (using `w₁ ≫ S.f = R.complex.d (n+1) n ≫ w₂`). -/
theorem comp_toSingleMk_eq {C : Type u} [Category.{v} C] [Abelian C] {X : C}
    (R : ProjectiveResolution X) {S : ShortComplex C} {n : ℕ}
    (w₂ : R.complex.X n ⟶ S.X₂) (w₁ : R.complex.X (n + 1) ⟶ S.X₁)
    (hw₁ : w₁ ≫ S.f = R.complex.d (n + 1) n ≫ w₂) :
    (Cochain.toSingleMk ((R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫ w₁) (by simp)).comp
        (Cochain.ofHom (S.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)).f)
        (add_zero ((↑n : ℤ) + 1)) =
      Cochain.toSingleMk ((R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫
        (R.complex.d (n + 1) n ≫ w₂)) (by simp) := by
  -- `Cochain.toSingleMk` is of the form `Cochain.single _ _`, so it only depends on its
  -- first argument: rewrite `(S.map _).f` as the image of `S.f` under the single functor.
  change (Cochain.toSingleMk
      ((R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫ w₁) (by simp)).comp
      (Cochain.ofHom ((singleFunctor C 0).map S.f)) (add_zero ((↑n : ℤ) + 1)) = _
  -- Apply the defining property of `toSingleMk` with respect to post-composition.
  rw [← Cochain.toSingleMk_postcomp
    (f := (R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫ w₁) (g := S.f)]
  congr 1
  rw [Category.assoc, hw₁]

end Work.SSGRoute.ExtConeLift
