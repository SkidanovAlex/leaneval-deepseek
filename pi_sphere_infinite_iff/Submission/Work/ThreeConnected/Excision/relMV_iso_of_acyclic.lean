import Mathlib
import Submission.Work.Cohomology.RelMVLes

/-!
# The connecting map of the relative Mayer–Vietoris sequence is an isomorphism when the
middle term is zero

For a space `X`, subsets `A, U, V ⊆ X`, the relative Mayer–Vietoris long exact sequence reads

`⋯ ⟶ Hₙ₊₁(U∩V, U∩V∩A) --F--> Hₙ₊₁(U,U∩A) ⊕ Hₙ₊₁(V,V∩A) --G--> Hₙ₊₁(X,A) --δ--> Hₙ(U∩V, U∩V∩A) ⟶ ⋯`

If the middle term `relMVH₂` vanishes in every degree, then `G = 0` and `F = 0` on the nose, so
exactness at the third spot says that `ker δ = im G = 0` (whence `δ` is a monomorphism) and
exactness at the first spot says that `im δ = ker F = ⊤` (whence `δ` is an epimorphism).  In an
abelian category mono + epi is an isomorphism.
-/

set_option linter.unusedVariables false

open CategoryTheory Limits

namespace Work.ThreeConnected.Excision

/-- **Exactness with a zero middle term**: if `H` is exact at the middle term of `A --f--> B --
g--> C`, the source of `f` is a zero object and `g ∘ …` — used in the form: an exact short
complex whose first term is `f = 0` has `g` a monomorphism. -/
theorem mono_of_exact_of_isZero_src {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).Exact) (hf : f = 0) : Mono g :=
  h.mono_g (by simpa using hf)

/-- **Exactness with a zero middle term**: an exact short complex whose last map is `g = 0` has
`f` an epimorphism. -/
theorem epi_of_exact_of_isZero_tgt {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).Exact) (hg : g = 0) : Epi f :=
  h.epi_f (by simpa using hg)

theorem relMV_iso_of_acyclic {X : TopCat} (A U V : Set X)
    (h₂ : ∀ n, CategoryTheory.Limits.IsZero (Work.Cohomology.relMVH₂ X A U V n)) (n : ℕ) :
    CategoryTheory.IsIso (Work.Cohomology.relMVδ X A U V n) := by
  -- Exactness at the third spot: `im G = ker δ`, and `G = 0` since its source is zero.
  have hmono : Mono (Work.Cohomology.relMVδ X A U V n) :=
    (Work.Cohomology.relMV_exact₃ X A U V n).mono_g
      (IsZero.eq_zero_of_src (h₂ (n + 1))
        (HomologicalComplex.homologyMap (Work.Cohomology.relMVG X A U V) (n + 1)))
  -- Exactness at the first spot: `im δ = ker F`, and `F = 0` since its target is zero.
  have hepi : Epi (Work.Cohomology.relMVδ X A U V n) :=
    (Work.Cohomology.relMV_exact₁ X A U V n).epi_f
      (IsZero.eq_zero_of_tgt (h₂ n)
        (HomologicalComplex.homologyMap (Work.Cohomology.relMVF X A U V) n))
  exact isIso_of_mono_of_epi (Work.Cohomology.relMVδ X A U V n)

end Work.ThreeConnected.Excision
