import Mathlib
import Submission.Work.ANALYTIC.RealSideDefs

/-!
# The presheaf of uniformly bounded families of `ℝ`-valued functions, as a presheaf of types

`boundedRealPresheaf ⋙ forget (ModuleCat ℤ)` is the underlying presheaf of *types* of the presheaf
`boundedRealPresheaf` of `Submission/Work/ANALYTIC/RealSideDefs.lean`: at a light profinite set `S`
its value is the set of uniformly bounded families `(x_n)_{n : ℕ}` of continuous `ℝ`-valued
functions on `S`.

This module only gives that composite a name (`boundedRealTypePresheaf`) so that statements about it
stay readable; it is definitionally the composite.  It is the `ℝ`-valued analogue of
`Submission/Work/ANALYTIC/BoundedType.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The underlying presheaf of types of `boundedRealPresheaf`: at a light profinite set `S` it is
the set of uniformly bounded families of continuous `ℝ`-valued functions on `S`. -/
abbrev boundedRealTypePresheaf :=
  CategoryTheory.Functor.comp boundedRealPresheaf (CategoryTheory.forget (ModuleCat ℤ))

/-- The value of `boundedRealTypePresheaf` at `S` is `boundedRealSet S` (definitionally). -/
theorem boundedRealTypePresheaf_obj (S : LightProfinite) :
    boundedRealTypePresheaf.obj (Opposite.op S) = boundedRealSet S := rfl

/-- Evaluation of the restriction of a bounded family along a morphism `f : S ⟶ T` of light
profinite sets: the `n`-th coordinate at a point `s` of the source is the `n`-th coordinate of the
original family at the image of `s`.  This is `rfl`, since this is how `boundedRealPresheaf` is
defined. -/
theorem boundedRealTypePresheaf_map_apply {S T : LightProfinite} (f : S ⟶ T)
    (x : boundedRealSet T) (n : ℕ) (s : S) :
    (boundedRealTypePresheaf.map f.op x).1 n s = x.1 n (f s) := rfl

/-- The points of the explicit finite coproduct are the points of the summands. -/
theorem boundedReal_finiteCoproduct_ι_apply {α : Type} [Finite α] (X : α → LightProfinite)
    (a : α) (s : X a) :
    (CompHausLike.finiteCoproduct.ι X a s : ↥(CompHausLike.finiteCoproduct X).toTop) = ⟨a, s⟩ :=
  rfl

end Work.ANALYTIC
