import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints_of_flat
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry in
open scoped TensorProduct in
/-- The canonical map `A^Γ ⊗[K] R ⟶ A ⊗[K] R` is injective, and its image is exactly the set of
points of `A ⊗[K] R` fixed by the induced `Γ`-action on the first factor.  (Injectivity uses that
`R` is automatically flat over the field `K`; the range statement is
`Work.SymQuot.Invariants.tensor_fixedPoints_of_flat`.) -/
theorem tensorIncl_range {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ]
    (A : Type u) [CommRing A] [Algebra K A] [MulSemiringAction Γ A] [SMulCommClass Γ K A]
    (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := Γ) A R) ∧
      Set.range (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := Γ) A R) =
        {x : A ⊗[K] R | ∀ g : Γ, Work.SymQuot.RelQuot.tensorAct (Γ := Γ) A R g x = x} := by
  classical
  constructor
  · have hf : Function.Injective (Subalgebra.val (FixedPoints.subalgebra K A Γ)).toLinearMap :=
      Subtype.val_injective
    have key : Function.Injective
        (LinearMap.rTensor R (Subalgebra.val (FixedPoints.subalgebra K A Γ)).toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hf
    exact key
  · exact Work.SymQuot.Invariants.tensor_fixedPoints_of_flat (K := K) (B := A) (R := R) (G := Γ)

end Work.SymQuot.RelQuot
