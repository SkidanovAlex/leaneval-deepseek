import Mathlib
import Submission.Work.DSMap.Map

/-!
# `Work.DSEQ0.chartCover`: the standard chart cover of projective space, pulled back

For `i : X ⟶ ℙᴺ_A = DSMap.PSpace A N`, this is the family of open subschemes
`X ∩ D₊(X_t)` (`t : Fin (N+1)`) of `X`: the restriction of the standard affine chart cover of
projective space.  These are the opens whose Čech complex is described by the graded module
machinery of area `DSCOH` (their `chartCech`).

The charts are affine (`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`) and cover `X`
(`Proj.iSup_basicOpen_eq_top`, transported along `i`).
-/

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Work.DSEQ0

universe a

/-- The standard chart cover of `ℙᴺ_A` (the opens `D₊(X_t)`, `t : Fin (N+1)`), pulled back to `X`
along `i : X ⟶ ℙᴺ_A`.  The index type is `ULift.{a} (Fin (N+1))` so that the family lives in the
universe of `A`, as `DSMap.cechZ` requires. -/
noncomputable def chartCover (A : Type a) [CommRing A] (N : ℕ) {X : Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) : ULift.{a} (Fin (N + 1)) → X.Opens :=
  fun t => i ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X t.down))

/-- The structure morphism `X ⟶ Spec A` determined by `i : X ⟶ ℙᴺ_A` (the composite with the
projection of projective space). -/
noncomputable def chartCoverToSpec (A : Type a) [CommRing A] (N : ℕ) {X : Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) : X ⟶ Spec (.of A) :=
  i ≫ DSMap.PSpace.toSpec A N

end Work.DSEQ0
