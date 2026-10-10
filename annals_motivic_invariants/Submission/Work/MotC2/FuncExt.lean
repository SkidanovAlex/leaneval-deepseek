/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# Extensionality and the characterisation of `[-1]` on `L(E)`

* `Work.MotC2.funcAlgEquiv_ext_genX_genY`: two `L`-algebra automorphisms of `L(E)` agreeing on
  `x = genX E` and `y = genY E` are equal.  (`x` and `y` generate `L(E)` over `L`.)
* `Work.MotC2.eq_negAlgEquiv_iff`: an automorphism is `negAlgEquiv E = [-1]` exactly when it fixes
  `x` and sends `y` to `-y - a₁x - a₃`.

## Tags

elliptic curve, function field, automorphism, negation
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Negation

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- Two `L`-algebra automorphisms of `L(E)` which agree on `x` and `y` are equal: as `L`-algebra
homomorphisms out of the affine coordinate ring `Coord E = AdjoinRoot (polynomial E)` they agree on
the root `y` and on `L[X]` (through their value on `x`), and `L(E)` is the fraction field of
`Coord E`. -/
theorem funcAlgEquiv_ext_genX_genY (E : WeierstrassCurve L) (f g : Func E ≃ₐ[L] Func E)
    (hX : f (genX E) = g (genX E)) (hY : f (genY E) = g (genY E)) : f = g := by
  have h : f.toAlgHom = g.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Coord E))
    apply AdjoinRoot.algHom_ext' (S := L) (R := Polynomial L)
      (p := WeierstrassCurve.Affine.polynomial E)
    · apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply]
      exact hX
    · exact hY
  ext z
  exact AlgHom.congr_fun h z

/-- An `L`-algebra automorphism of `L(E)` is the negation `[-1]` exactly when it fixes `x` and
sends `y` to `-y - a₁x - a₃`. -/
theorem eq_negAlgEquiv_iff (E : WeierstrassCurve L) (Θ : Func E ≃ₐ[L] Func E) :
    Θ = negAlgEquiv E ↔
      Θ (genX E) = genX E ∧
        Θ (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
          algebraMap L (Func E) E.a₃ := by
  constructor
  · rintro rfl
    exact ⟨negAlgEquiv_genX E, negAlgEquiv_genY E⟩
  · rintro ⟨hx, hy⟩
    refine funcAlgEquiv_ext_genX_genY E Θ (negAlgEquiv E) ?_ ?_
    · rw [hx]; exact (negAlgEquiv_genX E).symm
    · rw [hy]; exact (negAlgEquiv_genY E).symm

end Work.MotC2
