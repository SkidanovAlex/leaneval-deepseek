/-
Area AV (abelian-variety toolkit) for the Jacobian challenge: the projective line.
-/
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The projective line

`Work.AbVar.P1 k` is the projective line over a field `k`, realised as
`Proj k[X, Y]` for the grading by total degree, with the base `Spec (𝒜 0)` identified
with `Spec k` via the isomorphism `Work.AbVar.p1BaseEquiv` between `k` and the constants.

This is the scheme appearing in the `P1CONST` item of the contract: every morphism
`P1 k ⟶ A` into a proper group scheme over `k` is constant. See
`Work.AbVar.ProjectiveLine.isConstant_of_projectiveLine`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace Work.AbVar

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard grading of `k[X, Y]` by total degree. -/
noncomputable abbrev P1Grading (k : Type u) [Field k] :
    ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The degree-zero part of `k[X, Y]` is the constants, i.e. a copy of `k`. -/
noncomputable def p1BaseEquiv (k : Type u) [Field k] :
    k ≃+* ↥(P1Grading k 0) where
  toFun r := ⟨MvPolynomial.C r,
    (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 2) (R := k) 0 _).mpr
      (MvPolynomial.isHomogeneous_C (Fin 2) r)⟩
  invFun p := p.1.coeff 0
  left_inv r := by simp
  right_inv p := by
    apply Subtype.ext
    have htd : p.1.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.2
    change MvPolynomial.C (p.1.coeff 0) = (p.1 : MvPolynomial (Fin 2) k)
    rw [← MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd]
  map_add' a b := by ext; simp
  map_mul' a b := by ext; simp

/-- `Proj k[X, Y]`, the projective line as a scheme. -/
noncomputable abbrev P1Scheme (k : Type u) [Field k] : Scheme :=
  Proj (P1Grading k)

/-- The projective line over `k`, as a `k`-scheme. -/
noncomputable def P1 (k : Type u) [Field k] : Sch k :=
  Over.mk (Proj.toSpecZero (P1Grading k) ≫
    Spec.map (CommRingCat.ofHom (p1BaseEquiv k).toRingHom))

/-- The structure morphism of `P1 k` is the composition of `Proj.toSpecZero` with the base
identification. -/
lemma p1_hom (k : Type u) [Field k] :
    (P1 k).hom = Proj.toSpecZero (P1Grading k) ≫
      Spec.map (CommRingCat.ofHom (p1BaseEquiv k).toRingHom) := rfl

end Work.AbVar
