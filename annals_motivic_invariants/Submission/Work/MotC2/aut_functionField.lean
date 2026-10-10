/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The automorphisms of the function field of an elliptic curve

The chapter target: for an elliptic Weierstrass curve `E` over a field `L` with `j(E) ≠ 0, 1728`,
every `L`-algebra automorphism of the function field `L(E)` is a translation composed with `±1`
(Silverman, *AEC*, III.10 / Prop. A.1.2).

## Proof

Let `Θ : L(E) ≃ₐ[L] L(E)` and let `S := Subalgebra.map Θ.toAlgHom (infPlace E)` be the image of the
local ring of the point at infinity `O`.  `S` is a rational place of `L(E)/L`
(`Work.MotC2.IsRatPlaceMap`, applied to `Work.MotC2.InfPlace`), so the classification of rational
places (`Work.MotC2.Classification`) gives either `S = infPlace E` (`Θ` fixes `O` up to `Θ⁻¹`) or
`S = affPlaceAt E a b` for a nonsingular affine point `(a, b)`.

In the second case, `T := Point.some a b h` is a rational point and
`Work.MotC2.TransPlace` says that translation by `T` carries the place at `T` to `O`; hence
`Ψ := transAlgEquiv E T * Θ` satisfies `Subalgebra.map Ψ.toAlgHom (infPlace E) = infPlace E`.  In
the first case the same holds with `T := 0` and `Ψ := Θ`.  By `Work.MotC2.CoordPreserved`, `Ψ`
preserves the affine coordinate ring `L[x,y]` as well, so `Work.MotC2.VariableChange` applies: with
`j ≠ 0, 1728`, `Ψ` is either the identity or the negation `[-1]` on `x` and `y`, i.e.
`Ψ = Work.MotC2.negAlgEquiv E` (`Work.MotC2.eq_negAlgEquiv_iff`).

Finally `Θ = (transAlgEquiv E T)⁻¹ * Ψ = transAlgEquiv E (-T) * Ψ`, which is
`transAlgEquiv E (-T)` (a pure translation) or `transAlgEquiv E (-T) * negAlgEquiv E`.

## Tags

elliptic curve, function field, automorphism, translation, negation
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.FuncExt
import Submission.Work.MotC2.Classification
import Submission.Work.MotC2.CoordPreserved
import Submission.Work.MotC2.VariableChange
import Submission.Work.MotC2.TransPlace
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotC2.InfPlace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open WeierstrassCurve WeierstrassCurve.Affine

/-- **The automorphisms of the function field of an elliptic curve.**

For an elliptic Weierstrass curve `E` over a field `L` with `j(E) ≠ 0, 1728`, every `L`-algebra
automorphism of `L(E)` is a translation composed with `±1`: there is a point `Q ∈ E(L)` and
`ε ∈ {0, 1}` with `Θ = transAlgEquiv E Q * (negAlgEquiv E) ^ ε`. -/
theorem aut_functionField (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (hj0 : E.j ≠ 0) (hj : E.j ≠ 1728) (Θ : Func E ≃ₐ[L] Func E) :
    ∃ (Q : E.toAffine.Point) (ε : Fin 2),
      Θ = transAlgEquiv E Q * (negAlgEquiv E) ^ (ε : ℕ) := by
  have hS : IsRatPlace E (Subalgebra.map Θ.toAlgHom (infPlace E)) :=
    IsRatPlaceMap L E Θ (infPlace E) (InfPlace L E).1
  -- The key step: after composing with a translation by `T`, the automorphism fixes the point
  -- at infinity, hence is a variable change, hence `±1`.
  have key : ∀ (T : E.toAffine.Point),
      Subalgebra.map (transAlgEquiv E T * Θ).toAlgHom (infPlace E) = infPlace E →
      ∃ (Q : E.toAffine.Point) (ε : Fin 2),
        Θ = transAlgEquiv E Q * (negAlgEquiv E) ^ (ε : ℕ) := by
    intro T hOΨ
    set Ψ : Func E ≃ₐ[L] Func E := transAlgEquiv E T * Θ with hΨdef
    have hR : Subalgebra.map Ψ.toAlgHom (affRing E) = affRing E := CoordPreserved L E Ψ hOΨ
    have hΘ : Θ = (transAlgEquiv E T)⁻¹ * Ψ := by
      rw [hΨdef]
      group
    have hmul : transAlgEquiv E T * transAlgEquiv E (-T) = 1 := by
      rw [← transAlgEquiv_add, add_neg_cancel, transAlgEquiv_zero]
    have hinv : (transAlgEquiv E T)⁻¹ = transAlgEquiv E (-T) :=
      inv_eq_of_mul_eq_one_right hmul
    have hΘ' : Θ = transAlgEquiv E (-T) * Ψ := by rw [hΘ, hinv]
    rcases VariableChange L E hj0 hj Ψ hR hOΨ with h1 | ⟨hx, hy⟩
    · refine ⟨-T, 0, ?_⟩
      rw [hΘ', h1, mul_one]
      norm_num
    · have hΨneg : Ψ = negAlgEquiv E := (eq_negAlgEquiv_iff E Ψ).mpr ⟨hx, hy⟩
      refine ⟨-T, 1, ?_⟩
      rw [hΘ', hΨneg]
      norm_num
  rcases Classification L E (Subalgebra.map Θ.toAlgHom (infPlace E)) hS with hO | ⟨a, b, hns, hab⟩
  · -- the image place is the point at infinity already: `T = 0`
    refine key 0 ?_
    have hprod : transAlgEquiv E (0 : E.toAffine.Point) * Θ = Θ := by
      rw [transAlgEquiv_zero, one_mul]
    rw [hprod]
    exact hO
  · -- the image place is an affine point: translate it to `O`
    refine key (Point.some a b hns) ?_
    have hcomp : ((transAlgEquiv E (Point.some a b hns) * Θ).toAlgHom)
        = (transAlgEquiv E (Point.some a b hns)).toAlgHom.comp Θ.toAlgHom :=
      AlgHom.ext fun y => AlgEquiv.mul_apply _ _ y
    rw [hcomp, ← Subalgebra.map_map]
    rw [hab]
    exact (TransPlace L E a b hns).1

end Work.MotC2
