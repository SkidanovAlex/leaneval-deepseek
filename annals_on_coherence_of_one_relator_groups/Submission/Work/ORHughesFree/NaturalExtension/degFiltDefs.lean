/-
# The degree filtration of a left ideal of `S = SkewL R`

For a set `I` of elements of `S = R[t^{±1};τ]` and `m : ℕ`, `degPart R I m` is the `R`-submodule
of `R^{m+1}` spanned by the coefficient vectors (in degrees `0,…,m`) of the elements of `I`
whose coefficients in negative degrees vanish ("polynomial elements").

`sigmaSet R I` is the set of constant terms of polynomial elements of `I`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.subDimDefs
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The coefficient vector, in degrees `0,…,m`, of an element of `S = SkewL R`. -/
noncomputable def cvec (R : Type u) [Zero R] (m : ℕ) (f : SkewL R) : Fin (m+1) → R :=
  fun i => coeffElt f (i : ℕ)

/-- The `R`-submodule of `R^{m+1}` spanned by the coefficient vectors (in degrees `0,…,m`) of the
polynomial elements of `I`. -/
noncomputable def degPart (R : Type u) [Ring R] (I : Set (SkewL R)) (m : ℕ) :
    Submodule R (Fin (m+1) → R) :=
  Submodule.span R {v : Fin (m+1) → R |
    ∃ f ∈ I, (∀ k : ℤ, k < 0 → coeffElt f k = 0) ∧ v = cvec R m f}

/-- The set of constant terms of polynomial elements of `I`. -/
def sigmaSet (R : Type u) [Zero R] (I : Set (SkewL R)) : Set R :=
  {c : R | ∃ f ∈ I, (∀ k : ℤ, k < 0 → coeffElt f k = 0) ∧ coeffElt f 0 = c}

end Work.ORHughesFree.NaturalExtension
