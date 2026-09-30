import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.moduleSpeiser
import Submission.Work.Descent.Invariants

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

open CategoryTheory Limits AlgebraicGeometry

open scoped TensorProduct

/-- The `k`-linear equivalence between the fixed points of the underlying module structure
`(A.toModule).fixed` and the invariant subalgebra `A.invariants`.  These two subobjects of `B`
have the same carrier, so the canonical "identity" equivalence `LinearEquiv.ofEq` applies. -/
noncomputable def fixedInvariantsEquiv {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {B : Type u} [CommRing B] [Algebra k' B] [Algebra k B] [IsScalarTower k k' B]
    (A : SemilinearAction k k' B) :
    (A.toModule).fixed ≃ₗ[k] A.invariants :=
  LinearEquiv.ofEq _ _ A.fixed_toModule

/-- The algebra Speiser map, transported across `fixedInvariantsEquiv`, is the module Speiser map. -/
lemma speiserHomK_comp_rTensor {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {B : Type u} [CommRing B] [Algebra k' B] [Algebra k B] [IsScalarTower k k' B]
    (A : SemilinearAction k k' B) (t : (A.toModule).fixed ⊗[k] k') :
    A.speiserHomK (LinearEquiv.rTensor k' (fixedInvariantsEquiv A) t) =
      (A.toModule).speiserMapK t := by
  induction t using TensorProduct.inductionOn with
  | tmul v c =>
      rw [LinearEquiv.rTensor_tmul, SemilinearAction.speiserHomK_tmul,
        SemilinearActionModule.speiserMapK_tmul]
      congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Speiser's descent result for algebras: for a `k'`-algebra `B` with a semilinear action of the
Galois group of a finite Galois extension `k'/k`, the comparison map `B^Γ ⊗_k k' → B`,
`b ⊗ c ↦ c • b`, is bijective. -/
theorem speiser {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsGalois k k'] {B : Type u} [CommRing B] [Algebra k' B] [Algebra k B]
    [IsScalarTower k k' B] (A : SemilinearAction k k' B) :
    Function.Bijective A.speiserHomK := by
  -- Transport the module Speiser lemma across `fixedInvariantsEquiv`.
  have hcomp : ((A.speiserHomK) ∘ (LinearEquiv.rTensor k' (fixedInvariantsEquiv A))) =
      (A.toModule).speiserMapK := funext (speiserHomK_comp_rTensor A)
  have hbij : Function.Bijective
      ((A.speiserHomK) ∘ (LinearEquiv.rTensor k' (fixedInvariantsEquiv A))) := by
    rw [hcomp]
    exact moduleSpeiser A.toModule
  exact (Function.Bijective.of_comp_iff A.speiserHomK
    (LinearEquiv.rTensor k' (fixedInvariantsEquiv A)).bijective).mp hbij

end Work.Descent
