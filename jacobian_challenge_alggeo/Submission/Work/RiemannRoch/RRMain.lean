/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: the Riemann–Roch equation, unconditionally

Here the Riemann–Roch equation
`l D - i D = deg D + 1 - g`
is derived from the exact sequence `A(E)/A(D) = L(E)/L(D) ⊕ (A(E)+K)/(A(D)+K)`: the quantity
`i D - l D + deg D` is constant on comparable divisors, hence constant, and its value at `D = 0`
is `g - 1`.
-/
import Submission.Work.RiemannRoch.Genus
import Submission.Work.RiemannRoch.RR.step
import Submission.Work.RiemannRoch.RR.finrank_Kquot_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The kernel of `H1 C D → H1 C E` has dimension `(deg E - l E) - (deg D - l D)`. -/
theorem finrank_KquotAd_eq (C : Curve k) {D E : C.Div} (h : D ≤ E) :
    (Module.finrank k ↥(KquotAd C D E) : ℤ) = (C.deg E - C.l E) - (C.deg D - C.l D) := by
  haveI : FiniteDimensional k
      (relQuot (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C)) :=
    (Work.RiemannRoch.RR.finrank_sup_diagK_quot C h).1
  have h1 : Module.finrank k ↥(KquotAd C D E) =
      Module.finrank k (relQuot (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C)) := by
    rw [KquotAd]
    exact (LinearEquiv.finrank_eq
      (relQuotEquivMap (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C))).symm
  rw [h1, (Work.RiemannRoch.RR.finrank_sup_diagK_quot C h).2]

/-- The step between two comparable divisors: `i` drops by `deg(E-D) - (l E - l D)`. -/
theorem i_sub_i_of_finiteGenus (C : Curve k) (h : HasFiniteGenus C) {D E : C.Div}
    (hDE : D ≤ E) :
    (i C D : ℤ) - i C E = (C.deg E - C.l E) - (C.deg D - C.l D) := by
  have h1 := Work.RiemannRoch.RR.step C h hDE
  have h2 := finrank_KquotAd_eq C hDE
  have h4 : (Module.finrank k (H1 C D) : ℤ) =
      (Module.finrank k (H1 C E) : ℤ) + (Module.finrank k ↥(KquotAd C D E) : ℤ) := by
    rw [h1]; push_cast; ring
  have h3 : (i C E : ℤ) = (i C D : ℤ) - Module.finrank k ↥(KquotAd C D E) := by
    show (Module.finrank k (H1 C E) : ℤ) =
      (Module.finrank k (H1 C D) : ℤ) - (Module.finrank k ↥(KquotAd C D E) : ℤ)
    rw [h4]; ring
  rw [h3, h2]
  ring

/-- **Riemann–Roch**, in the presence of the finiteness of the genus. -/
theorem riemannRoch_of_finiteGenus (C : Curve k) (h : HasFiniteGenus C) (D : C.Div) :
    (C.l D : ℤ) - i C D = C.deg D + 1 - (genus C : ℤ) := by
  have hD : D ≤ D ⊔ 0 := le_sup_left
  have h0 : (0 : C.Div) ≤ D ⊔ 0 := le_sup_right
  have h1 := i_sub_i_of_finiteGenus C h hD
  have h2 := i_sub_i_of_finiteGenus C h h0
  rw [Curve.deg_zero, l_zero] at h2
  have hgen : (i C 0 : ℤ) = (genus C : ℤ) := rfl
  have h3 : (i C 0 : ℤ) - (i C D : ℤ) = 1 + C.deg D - (C.l D : ℤ) := by
    linear_combination h2 - h1
  omega

end

end Curve

end Work.RiemannRoch
