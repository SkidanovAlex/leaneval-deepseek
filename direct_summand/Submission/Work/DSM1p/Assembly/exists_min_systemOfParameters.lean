import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSNORM.Defs

/-!
# A minimal system of parameters of a regular local ring

A regular local ring `R` has a system of parameters of length `dim R`:
by definition of `IsRegularLocalRing` the embedding dimension
`(maximalIdeal R).spanFinrank` equals `ringKrullDim R`, and any finite family of
`(maximalIdeal R).spanFinrank` elements spanning the maximal ideal is a system of
parameters.

The chosen generators of the maximal ideal of a Noetherian local ring, together with
their cardinality, are provided by the area `DSNORM`
(`Work.DSNORM.params`, `Work.DSNORM.nParams`, `Work.DSNORM.params_span`); here we only
need to combine them with `IsRegularLocalRing.spanFinrank_maximalIdeal`.
-/

namespace Work.DSM1p.Assembly

/-- **A regular local ring has a (minimal) system of parameters**: there are
`d = dim R` elements of `R` whose span is the maximal ideal. -/
theorem exists_min_systemOfParameters (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    ∃ (d : ℕ) (x : Fin d → R), Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧
      (d : WithBot ℕ∞) = ringKrullDim R := by
  refine ⟨Work.DSNORM.nParams R, Work.DSNORM.params R, Work.DSNORM.params_span R, ?_⟩
  rw [Work.DSNORM.nParams]
  exact IsRegularLocalRing.spanFinrank_maximalIdeal

end Work.DSM1p.Assembly
