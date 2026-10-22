/-
# AREA CONDMV — colimits of light condensed sets along an open exhaustion

This file sets up the second half of `REFS/01` F11: if `X = ⋃ₙ Aₙ` is an increasing union of open
subsets such that every compact subset of `X` is contained in some `Aₙ`, then `X_cond` is the
colimit of the light condensed sets `(Aₙ)_cond`.

Here we only define the diagram and the cocone; the statement that the cocone is a colimit is
`Work.CONDMV.Exhaust.isColimit_exhaustCocone`
(`Submission/Work/CONDMV/Exhaust/isColimit_exhaustCocone.lean`), and its image under `free ℤ`
(which is what the CW induction uses) is `Work.CONDMV.isColimit_exhaustCocone_free`.
-/
import Submission.Work.CONDMV.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.CONDMV

variable {X : TopCat.{0}}

/-- The diagram `n ↦ (Aₙ)_cond` of light condensed sets attached to an increasing sequence of
subsets of `X`. -/
noncomputable def exhaustFunctor (A : ℕ → Set X) (hmono : Monotone A) : ℕ ⥤ LightCondSet.{0} where
  obj n := setCond (A n)
  map {m n} f := topCatToLightCondSet.map
    (Submission.Blueprint.incl (hmono (leOfHom f)))

@[simp]
lemma exhaustFunctor_obj (A : ℕ → Set X) (hmono : Monotone A) (n : ℕ) :
    (exhaustFunctor A hmono).obj n = setCond (A n) := rfl

/-- The cocone with point `X_cond` under the diagram of an open exhaustion. -/
noncomputable def exhaustCocone (A : ℕ → Set X) (hmono : Monotone A) :
    Cocone (exhaustFunctor A hmono) where
  pt := condOf X
  ι :=
    { app := fun n => topCatToLightCondSet.map (Submission.Blueprint.inclTop (A n))
      naturality := by
        intro m n f
        show topCatToLightCondSet.map (Submission.Blueprint.incl (hmono (leOfHom f))) ≫
            topCatToLightCondSet.map (Submission.Blueprint.inclTop (A n)) =
          topCatToLightCondSet.map (Submission.Blueprint.inclTop (A m))
        rw [← Functor.map_comp]
        congr 1 }

end Work.CONDMV
