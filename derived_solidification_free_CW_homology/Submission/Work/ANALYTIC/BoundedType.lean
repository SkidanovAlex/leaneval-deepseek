import Mathlib
import Submission.Work.ANALYTIC.Bounded

/-!
# The presheaf of uniformly bounded sequences, as a presheaf of types

`boundedPresheaf ⋙ forget (ModuleCat ℤ)` is the underlying presheaf of *types* of the presheaf of
uniformly bounded sequences of `Submission/Work/ANALYTIC/Bounded.lean`.  This module only gives it a
name (`boundedTypePresheaf`) so that statements about it stay readable; it is definitionally the
composite.
-/

open CategoryTheory

noncomputable section

namespace Work.ANALYTIC

/-- The underlying presheaf of types of `boundedPresheaf`: at a light profinite set `S` it is the
set of uniformly bounded families of continuous `ℤ`-valued functions on `S`. -/
abbrev boundedTypePresheaf :=
  CategoryTheory.Functor.comp boundedPresheaf (CategoryTheory.forget (ModuleCat ℤ))

/-- The value of `boundedTypePresheaf` at `S` is `boundedSeqSet S` (definitionally). -/
theorem boundedTypePresheaf_obj (S : LightProfinite) :
    boundedTypePresheaf.obj (Opposite.op S) = boundedSeqSet S := rfl

end Work.ANALYTIC
