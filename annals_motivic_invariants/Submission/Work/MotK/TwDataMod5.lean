/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.KleinTwI1
import Submission.Work.MotK.KleinIdents
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The corrected **target-side** data of the T-twisted Crauder--Katz link

The T-twist is the Kummer substitution `x_i = w^i y_i` (`w^5 = h`).  Every polynomial of the
Klein model is homogeneous for the `Z/5`-grading `deg x_i = i`, so a *substitution* by powers of
`w` produces a `w`-power times a polynomial in `h` and the new coordinates.  The **weight** used
on the two sides of the link is forced by the identities:

* the *source* side uses the plain weights `x_i -> w^i y_i`; this is `kleinTwP`, `kleinTwS`
  (already in `KleinTwData`, satisfying the twisted identity I1' of `KleinTwI1`);
* the *target* side must use the weights `z_i -> w^(4 i mod 5) z_i` — the substitution under
  which the split identities I1--I4 of `KleinIdents` descend.

`kleinTwR` (`KleinTwData`) is already normalised this way (its defining identity is
`kleinR a b (fun i => w^(4*i) z i) k = w^k * kleinTwR a b (w^5) z k`, and the two normalisations
agree because the index degree of `kleinR_k` is `4k mod 5`), but the *dual secant quintic*
`kleinTwSDual` is **not**: it is the plain twist `s'(w^i z_i)`, and with it the twisted analogues
of I2, I3 and I4 are **false** (CAS counterexample: `kleinTwSDual (kleinTwP y) - kleinTwS y ^ 2
≠ 0` for `h ≠ 1`; see `AUDIT_LinkCertT.md` §3).  The correct target-side dual secant is the
*Kummer-inverse* twist, defined below; it is computed by `cas/gen_SDv.py` and, with it, all four
identities hold (verified symbolically and in `cas/_mod5c.py`).

The four identities, in the form in which the certificate consumes them:

* **I1'** `kleinTwR (kleinTwP y) = kleinTwS y · y`                     (`KleinTwI1`, proved);
* **I2'** `kleinTwP k (kleinTwR z) = kleinTwSDualV z · z k`            (`kleinTwP_kleinTwR_V`);
* **I3'** `kleinTwSDualV (kleinTwP y) = kleinTwS y ^ 2`                (`kleinTwSDualV_kleinTwP`);
* **I4'** `kleinTwS (kleinTwR z) = kleinTwSDualV z ^ 3`                (`kleinTwSec_kleinTwR`).

The unit condition of the link (`kleinTwLinkUnitV`) then follows from I1', I3', the bilinearity
of the polar form and the stereographic identity `KleinTwQ_stereo`, exactly as in the split case
`Work.MotK.KleinLinkUnit`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- **The Kummer-inverse twist of the dual secant quintic** `s'`: the target-side dual secant of
the T-twisted link.  (Substitute `z_i -> w^(4 i mod 5) z_i` in `s'` and reduce `w^5 = h`.) -/
def kleinTwSDualV (a b h : R) (z : Fin 5 → R) : R :=
  2*a^(3:ℕ)*b^(7:ℕ)*h*(z 0)^(3:ℕ)*z 2*z 3 + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*z 0*(z 2)^(3:ℕ)*z 4 + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*z 0*z 1*(z 3)^(3:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*z 1*z 2*(z 4)^(3:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ)*h^(3:ℕ)*(z 1)^(3:ℕ)*z 3*z 4 + 2*a^(7:ℕ)*b^(3:ℕ)*h*(z 0)^(3:ℕ)*z 1*z 4 + 2*a^(7:ℕ)*b^(3:ℕ)*h*z 0*z 3*(z 4)^(3:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ)*h^(2:ℕ)*z 2*(z 3)^(3:ℕ)*z 4 + 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*z 0*(z 1)^(3:ℕ)*z 2 + 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*z 1*(z 2)^(3:ℕ)*z 3 + 3*a^(4:ℕ)*b^(6:ℕ)*h*(z 0)^(2:ℕ)*(z 3)^(2:ℕ)*z 4 + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(z 0)^(2:ℕ)*z 1*(z 2)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(z 2)^(2:ℕ)*z 3*(z 4)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*z 0*(z 1)^(2:ℕ)*(z 4)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*h^(3:ℕ)*(z 1)^(2:ℕ)*z 2*(z 3)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h*(z 0)^(2:ℕ)*z 2*(z 4)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(z 0)^(2:ℕ)*(z 1)^(2:ℕ)*z 3 - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*z 0*(z 2)^(2:ℕ)*(z 3)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*z 1*(z 3)^(2:ℕ)*(z 4)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h^(3:ℕ)*(z 1)^(2:ℕ)*(z 2)^(2:ℕ)*z 4 - 6*a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*z 0*z 1*z 2*z 3*z 4 - a*b^(9:ℕ)*h*(z 0)^(2:ℕ)*z 2*(z 4)^(2:ℕ) - a*b^(9:ℕ)*h^(2:ℕ)*(z 0)^(2:ℕ)*(z 1)^(2:ℕ)*z 3 - a*b^(9:ℕ)*h^(2:ℕ)*z 0*(z 2)^(2:ℕ)*(z 3)^(2:ℕ) - a*b^(9:ℕ)*h^(2:ℕ)*z 1*(z 3)^(2:ℕ)*(z 4)^(2:ℕ) - a*b^(9:ℕ)*h^(3:ℕ)*(z 1)^(2:ℕ)*(z 2)^(2:ℕ)*z 4 + a^(10:ℕ)*h^(2:ℕ)*z 0*z 1*z 2*z 3*z 4 - a^(2:ℕ)*b^(8:ℕ)*h*(z 0)^(3:ℕ)*z 1*z 4 - a^(2:ℕ)*b^(8:ℕ)*h*z 0*z 3*(z 4)^(3:ℕ) - a^(2:ℕ)*b^(8:ℕ)*h^(2:ℕ)*z 2*(z 3)^(3:ℕ)*z 4 - a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*z 0*(z 1)^(3:ℕ)*z 2 - a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*z 1*(z 2)^(3:ℕ)*z 3 - a^(5:ℕ)*b^(5:ℕ)*(z 0)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h*(z 4)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*(z 3)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(3:ℕ)*(z 2)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(4:ℕ)*(z 1)^(5:ℕ) + a^(8:ℕ)*b^(2:ℕ)*h*(z 0)^(3:ℕ)*z 2*z 3 + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*z 0*(z 2)^(3:ℕ)*z 4 + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*z 0*z 1*(z 3)^(3:ℕ) + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*z 1*z 2*(z 4)^(3:ℕ) + a^(8:ℕ)*b^(2:ℕ)*h^(3:ℕ)*(z 1)^(3:ℕ)*z 3*z 4 - a^(9:ℕ)*b*h*(z 0)^(2:ℕ)*(z 3)^(2:ℕ)*z 4 - a^(9:ℕ)*b*h^(2:ℕ)*(z 0)^(2:ℕ)*z 1*(z 2)^(2:ℕ) - a^(9:ℕ)*b*h^(2:ℕ)*(z 2)^(2:ℕ)*z 3*(z 4)^(2:ℕ) - a^(9:ℕ)*b*h^(2:ℕ)*z 0*(z 1)^(2:ℕ)*(z 4)^(2:ℕ) - a^(9:ℕ)*b*h^(3:ℕ)*(z 1)^(2:ℕ)*z 2*(z 3)^(2:ℕ) - b^(10:ℕ)*h^(2:ℕ)*z 0*z 1*z 2*z 3*z 4

/-! ## I3': `kleinTwSDualV (kleinTwP y) = kleinTwS y ^ 2` -/

theorem kleinTwSDualV_kleinTwP (a b h : R) (y : Fin 5 → R) :
    kleinTwSDualV a b h (kleinTwP a b h y) = kleinTwS a b h y ^(2:ℕ) := by
  simp only [kleinTwSDualV, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  refl_ring1

/-! ## I2': `kleinTwP k (kleinTwR z) = kleinTwSDualV z · z k` -/

theorem kleinTwP_kleinTwR_V_zero (a b h : R) (z : Fin 5 → R) :
    kleinTwP a b h (kleinTwR a b h z) 0 = kleinTwSDualV a b h z * z 0 := by
  simp only [kleinTwP_zero, kleinTwP0, kleinTwR_zero, kleinTwR0, kleinTwR_one, kleinTwR1,
    kleinTwR_two, kleinTwR2, kleinTwR_three, kleinTwR3, kleinTwR_four, kleinTwR4,
    kleinTwSDualV]
  refl_ring1

theorem kleinTwP_kleinTwR_V_one (a b h : R) (z : Fin 5 → R) :
    kleinTwP a b h (kleinTwR a b h z) 1 = kleinTwSDualV a b h z * z 1 := by
  simp only [kleinTwP_one, kleinTwP1, kleinTwR_zero, kleinTwR0, kleinTwR_one, kleinTwR1,
    kleinTwR_two, kleinTwR2, kleinTwR_three, kleinTwR3, kleinTwR_four, kleinTwR4,
    kleinTwSDualV]
  refl_ring1

theorem kleinTwP_kleinTwR_V_two (a b h : R) (z : Fin 5 → R) :
    kleinTwP a b h (kleinTwR a b h z) 2 = kleinTwSDualV a b h z * z 2 := by
  simp only [kleinTwP_two, kleinTwP2, kleinTwR_zero, kleinTwR0, kleinTwR_one, kleinTwR1,
    kleinTwR_two, kleinTwR2, kleinTwR_three, kleinTwR3, kleinTwR_four, kleinTwR4,
    kleinTwSDualV]
  refl_ring1

theorem kleinTwP_kleinTwR_V_three (a b h : R) (z : Fin 5 → R) :
    kleinTwP a b h (kleinTwR a b h z) 3 = kleinTwSDualV a b h z * z 3 := by
  simp only [kleinTwP_three, kleinTwP3, kleinTwR_zero, kleinTwR0, kleinTwR_one, kleinTwR1,
    kleinTwR_two, kleinTwR2, kleinTwR_three, kleinTwR3, kleinTwR_four, kleinTwR4,
    kleinTwSDualV]
  refl_ring1

theorem kleinTwP_kleinTwR_V_four (a b h : R) (z : Fin 5 → R) :
    kleinTwP a b h (kleinTwR a b h z) 4 = kleinTwSDualV a b h z * z 4 := by
  simp only [kleinTwP_four, kleinTwP4, kleinTwR_zero, kleinTwR0, kleinTwR_one, kleinTwR1,
    kleinTwR_two, kleinTwR2, kleinTwR_three, kleinTwR3, kleinTwR_four, kleinTwR4,
    kleinTwSDualV]
  refl_ring1

/-- **I2'** (T-twist of the inverse relation `p(R z) = s'(z) · z`). -/
theorem kleinTwP_kleinTwR_V (a b h : R) (z : Fin 5 → R) (k : Fin 5) :
    kleinTwP a b h (kleinTwR a b h z) k = kleinTwSDualV a b h z * z k := by
  fin_cases k
  · exact kleinTwP_kleinTwR_V_zero a b h z
  · exact kleinTwP_kleinTwR_V_one a b h z
  · exact kleinTwP_kleinTwR_V_two a b h z
  · exact kleinTwP_kleinTwR_V_three a b h z
  · exact kleinTwP_kleinTwR_V_four a b h z

/-! ## Homogeneity of the twisted data -/

theorem kleinTwP_homog (a b h lam : R) (z : Fin 5 → R) :
    kleinTwP a b h (fun i => lam * z i) = fun k => lam ^(2:ℕ) * kleinTwP a b h z k := by
  funext k
  fin_cases k
  · show kleinTwP0 a b h (fun i => lam * z i) = lam ^(2:ℕ) * kleinTwP0 a b h z
    simp only [kleinTwP0]; ring
  · show kleinTwP1 a b h (fun i => lam * z i) = lam ^(2:ℕ) * kleinTwP1 a b h z
    simp only [kleinTwP1]; ring
  · show kleinTwP2 a b h (fun i => lam * z i) = lam ^(2:ℕ) * kleinTwP2 a b h z
    simp only [kleinTwP2]; ring
  · show kleinTwP3 a b h (fun i => lam * z i) = lam ^(2:ℕ) * kleinTwP3 a b h z
    simp only [kleinTwP3]; ring
  · show kleinTwP4 a b h (fun i => lam * z i) = lam ^(2:ℕ) * kleinTwP4 a b h z
    simp only [kleinTwP4]; ring

theorem kleinTwR_homog (a b h lam : R) (z : Fin 5 → R) :
    kleinTwR a b h (fun i => lam * z i) = fun k => lam ^(3:ℕ) * kleinTwR a b h z k := by
  funext k
  fin_cases k
  · show kleinTwR0 a b h (fun i => lam * z i) = lam ^(3:ℕ) * kleinTwR0 a b h z
    simp only [kleinTwR0]; ring
  · show kleinTwR1 a b h (fun i => lam * z i) = lam ^(3:ℕ) * kleinTwR1 a b h z
    simp only [kleinTwR1]; ring
  · show kleinTwR2 a b h (fun i => lam * z i) = lam ^(3:ℕ) * kleinTwR2 a b h z
    simp only [kleinTwR2]; ring
  · show kleinTwR3 a b h (fun i => lam * z i) = lam ^(3:ℕ) * kleinTwR3 a b h z
    simp only [kleinTwR3]; ring
  · show kleinTwR4 a b h (fun i => lam * z i) = lam ^(3:ℕ) * kleinTwR4 a b h z
    simp only [kleinTwR4]; ring

theorem kleinTwS_homog (a b h lam : R) (z : Fin 5 → R) :
    kleinTwS a b h (fun i => lam * z i) = lam ^(5:ℕ) * kleinTwS a b h z := by
  simp only [kleinTwS]
  refl_ring1

theorem kleinTwSDualV_homog (a b h lam : R) (z : Fin 5 → R) :
    kleinTwSDualV a b h (fun i => lam * z i) = lam ^(5:ℕ) * kleinTwSDualV a b h z := by
  simp only [kleinTwSDualV]
  refl_ring1

/-! ## I4': `kleinTwS (kleinTwR z) = kleinTwSDualV z ^ 3`

As in the split case (`KleinIdents.kleinI4_mul`), the identity is first proved in multiplied
form from I1' + I2' + homogeneity of `kleinTwR`, then divided by `kleinTwR z 0`. -/

theorem kleinTwI4_mul_V (a b h : R) (z : Fin 5 → R) :
    kleinTwR a b h z 0 * kleinTwS a b h (kleinTwR a b h z)
      = kleinTwR a b h z 0 * kleinTwSDualV a b h z ^(3:ℕ) := by
  have h1 : kleinTwR a b h (kleinTwP a b h (kleinTwR a b h z))
      = fun i => kleinTwS a b h (kleinTwR a b h z) * kleinTwR a b h z i := by
    funext i
    exact KleinTwI1 a b h (kleinTwR a b h z) i
  have h2 : kleinTwP a b h (kleinTwR a b h z)
      = fun i => kleinTwSDualV a b h z * z i := by
    funext i
    exact kleinTwP_kleinTwR_V a b h z i
  rw [h2, kleinTwR_homog (lam := kleinTwSDualV a b h z)] at h1
  have h0 := congrFun h1 0
  rw [mul_comm (kleinTwSDualV a b h z ^(3:ℕ)),
    mul_comm (kleinTwS a b h (kleinTwR a b h z))] at h0
  exact h0.symm

theorem kleinTwSec_kleinTwR (a b h : R) [IsDomain R] (z : Fin 5 → R)
    (hz : kleinTwR a b h z 0 ≠ 0) :
    kleinTwS a b h (kleinTwR a b h z) = kleinTwSDualV a b h z ^(3:ℕ) :=
  mul_left_cancel₀ hz (kleinTwI4_mul_V a b h z)

end Work.MotK
