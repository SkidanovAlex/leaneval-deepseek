import Submission.Work.DSMap.Mix

/-!
# DSAM2 (curric-46): mixed-characteristic almost-splitting descent

Basic vocabulary for the descent theorem `DSMap.Mix.modSplit_descent` (AM2 of the MIX design):
`ModSplit P ε ψ I c` says that the unit of a finite free model `(P, ε)` of `RΓ(X, 𝒪)` splits
modulo the ideal `I`, up to the factor `c`.  This file records the *matrix form* of that
predicate in a basis of `P.X 0` and `P.X (-1)`.

`Work.DSAM2.systemMatrix` is the matrix of the associated inhomogeneous linear system, whose
unknowns are the values `q i = s (1 ⊗ₜ b0 i)`: the `some j`-row expresses `s (d(b1 j)) = 0`
and the `none`-row expresses `s (ε 1) = c`.  `Work.DSAM2.systemRHS c` is the corresponding
right-hand side.  The point of the matrix form is that it is stable under base change along
`A → S → S ⧸ J`, which is what makes faithful-flat descent available.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSAM2

universe a

/-- The matrix of the linear system describing `ModSplit`, in bases `b0` of `P.X 0` and `b1`
of `P.X (-1)`.  Row `some j` records the coefficient vector of `(P.d (-1) 0) (b1 j)` and row
`none` records the coefficient vector of the unit `ε 1`. -/
noncomputable def systemMatrix {A : Type a} [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {ι₀ ι₁ : Type} (b0 : Module.Basis ι₀ A (P.X 0)) (b1 : Module.Basis ι₁ A (P.X (-1))) :
    Matrix (Option ι₁) ι₀ A :=
  fun k i => match k with
    | some j => (b0.repr ((P.d (-1) 0).hom (b1 j))) i
    | none => (b0.repr (ε.hom 1)) i

/-- The right-hand side of the linear system: zero on the differential rows, `c` on the unit row. -/
def systemRHS {ι₁ : Type} {S : Type*} [Zero S] (c : S) : Option ι₁ → S :=
  fun k => match k with
    | some _ => 0
    | none => c

/-- The unit row of the system: the coordinates of `ε 1`. -/
noncomputable def unitRow {A : Type a} [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {ι₀ : Type} (b0 : Module.Basis ι₀ A (P.X 0)) : ι₀ → A :=
  fun i => (b0.repr (ε.hom 1)) i

end Work.DSAM2
