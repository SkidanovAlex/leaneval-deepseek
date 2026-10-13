import Mathlib
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.Segre.Basic
import Submission.Work.DSG2.Segre.Triangle
import Submission.Work.DSG2.Segre.charts_compat
import Submission.Work.DSG2.Segre.isClosedImmersion_glue
import Submission.Work.DSG2.SegreProduct

/-!
# DSG2: the two-factor Segre embedding, universe-general

`Work.DSG2.segreEmbedding` in `Submission/Work/DSG2/segreEmbedding.lean` is stated with the
universe-monomorphic binder `(A : Type)`, so it cannot be instantiated at a higher universe.
This file contains the same statement with `A : Type u` (the proof is the same, since all the
ingredients in `Submission/Work/DSG2/Segre/` are universe-polymorphic).

* `Work.DSG2.segreEmbedding_u` : for `a b : ℕ` there is a closed immersion
  `ℙ^a_A ×_{Spec A} ℙ^b_A ⟶ ℙ^{(a+1)(b+1)-1}_A` over `Spec A`.
* `Work.DSG2.hasSegre` : the packaged form `HasSegre A` used by
  `Work.DSG2.nonempty_segreProductData`.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSG2

universe u

/-- The two-factor Segre embedding, at an arbitrary universe. -/
theorem segreEmbedding_u (A : Type u) [CommRing A] (a b : ℕ) :
    ∃ (σ : CategoryTheory.Limits.pullback (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)
        ⟶ DSMap.PSpace A ((a + 1) * (b + 1) - 1)),
      IsClosedImmersion σ ∧
        CategoryTheory.CategoryStruct.comp σ (DSMap.PSpace.toSpec A ((a + 1) * (b + 1) - 1)) =
          CategoryTheory.CategoryStruct.comp
            (CategoryTheory.Limits.pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b))
            (DSMap.PSpace.toSpec A a) := by
  refine ⟨(Segre.cover A a b).glueMorphisms (Segre.sigma A a b) (Segre.charts_compat A a b),
    ?_, ?_⟩
  · exact Segre.isClosedImmersion_glue A a b (Segre.charts_compat A a b)
  · exact Segre.glue_toSpec A a b (Segre.charts_compat A a b)

/-- The two-factor Segre embedding, packaged as `HasSegre`. -/
theorem hasSegre (A : Type u) [CommRing A] : HasSegre A := fun a b => segreEmbedding_u A a b

end Work.DSG2
