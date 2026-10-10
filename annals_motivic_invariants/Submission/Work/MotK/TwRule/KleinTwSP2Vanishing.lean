import Mathlib
import Submission.Work.MotK.KleinTwPolar
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vanishing of the second polar of the twisted secant quintic on the twisted Klein curve

The second polar `kleinTwSP2` of the twisted secant quintic is a quadratic form in `u`,
`kleinTwSP2 = ∑_i kleinTwSD i · u_i² + ∑_{i<j} kleinTwSDD_{ij} · u_i u_j`, and each of the 15
coefficients lies in the ideal `(P_0, …, P_4)` of the twisted Klein curve: this is the twisted
analogue of identity **I5** of `Submission/Work/MotK/CensusFibre/SecPolar.lean` (the twisted
secant surface has multiplicity `≥ 3` along the twisted Klein curve).

Consequently, if `kleinTwP a b h c = 0` (i.e. `c` lies on the twisted Klein curve), then
`kleinTwSP2 a b h c u = 0` for every `u`.

The 15 certificates `kleinTwSD0_eq … kleinTwSDD_34_eq` and the polar expansion `kleinTwSP2_eq`
are copied verbatim from `Submission/Work/MotK/KleinTwI5.lean` (which we do not import here);
everything is over an arbitrary `CommRing R`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.MotK.TwRule

open Work.MotK

variable {R : Type*} [CommRing R]

/-! ## The second polar as a quadratic form in `u` -/

theorem kleinTwSP2_eq (a b h : R) (c u : Fin 5 → R) :
    kleinTwSP2 a b h c u
      = kleinTwSD0 a b h c * (u 0) ^(2:ℕ)
        + kleinTwSD1 a b h c * (u 1) ^(2:ℕ)
        + kleinTwSD2 a b h c * (u 2) ^(2:ℕ)
        + kleinTwSD3 a b h c * (u 3) ^(2:ℕ)
        + kleinTwSD4 a b h c * (u 4) ^(2:ℕ)
        + kleinTwSDD_01 a b h c * u 0 * u 1
        + kleinTwSDD_02 a b h c * u 0 * u 2
        + kleinTwSDD_03 a b h c * u 0 * u 3
        + kleinTwSDD_04 a b h c * u 0 * u 4
        + kleinTwSDD_12 a b h c * u 1 * u 2
        + kleinTwSDD_13 a b h c * u 1 * u 3
        + kleinTwSDD_14 a b h c * u 1 * u 4
        + kleinTwSDD_23 a b h c * u 2 * u 3
        + kleinTwSDD_24 a b h c * u 2 * u 4
        + kleinTwSDD_34 a b h c * u 3 * u 4 := by
  simp only [kleinTwSP2, kleinTwSD0, kleinTwSD1, kleinTwSD2, kleinTwSD3, kleinTwSD4,
    kleinTwSDD_01, kleinTwSDD_02, kleinTwSDD_03, kleinTwSDD_04, kleinTwSDD_12, kleinTwSDD_13,
    kleinTwSDD_14, kleinTwSDD_23, kleinTwSDD_24, kleinTwSDD_34]
  first | refl_ring1 | ring

/-! ## The I5 certificates for the second partials -/

/-- The divided second partial `kleinTwSD0` is a combination of the twisted quadrics. -/
theorem kleinTwSD0_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSD0 a b h c
      = (( (10*a^(4:ℕ)*b^(4:ℕ)) ) * (c 0)) * kleinTwP0 a b h c
        + (( (3*a^(7:ℕ)*b + a^(2:ℕ)*b^(6:ℕ)) * h ) * (c 1)) * kleinTwP1 a b h c
        + (( (2*a^(6:ℕ)*b^(2:ℕ) - a*b^(7:ℕ)) * h ) * (c 2)) * kleinTwP2 a b h c
        + (( (-a^(6:ℕ)*b^(2:ℕ) - 2*a*b^(7:ℕ)) * h ) * (c 3)) * kleinTwP3 a b h c := by
  simp only [kleinTwSD0, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The divided second partial `kleinTwSD1` is a combination of the twisted quadrics. -/
theorem kleinTwSD1_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSD1 a b h c
      = (( (-a^(6:ℕ)*b^(2:ℕ) - 2*a*b^(7:ℕ)) * h ) * (c 3)) * kleinTwP0 a b h c
        + (( (2*a^(6:ℕ)*b^(2:ℕ) - a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP1 a b h c
        + (( (3*a^(7:ℕ)*b + a^(2:ℕ)*b^(6:ℕ)) * h ) * (c 0)) * kleinTwP2 a b h c
        + (( (10*a^(4:ℕ)*b^(4:ℕ)) * h ) * (c 1)) * kleinTwP3 a b h c := by
  simp only [kleinTwSD1, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The divided second partial `kleinTwSD2` is a combination of the twisted quadrics. -/
theorem kleinTwSD2_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSD2 a b h c
      = (( (a^(7:ℕ)*b + 2*a^(2:ℕ)*b^(6:ℕ)) * h ) * (c 1)) * kleinTwP0 a b h c
        + (( (10*a^(4:ℕ)*b^(4:ℕ)) * h^(2:ℕ) ) * (c 2)) * kleinTwP1 a b h c
        + (( (2*a^(7:ℕ)*b - a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP2 a b h c
        + (( (a^(6:ℕ)*b^(2:ℕ) - 3*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP3 a b h c := by
  simp only [kleinTwSD2, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The divided second partial `kleinTwSD3` is a combination of the twisted quadrics. -/
theorem kleinTwSD3_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSD3 a b h c
      = (( (3*a^(7:ℕ)*b + a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP0 a b h c
        + (( (2*a^(6:ℕ)*b^(2:ℕ) - a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 0)) * kleinTwP1 a b h c
        + (( (-a^(6:ℕ)*b^(2:ℕ) - 2*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 1)) * kleinTwP2 a b h c
        + (( (10*a^(4:ℕ)*b^(4:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP4 a b h c := by
  simp only [kleinTwSD3, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The divided second partial `kleinTwSD4` is a combination of the twisted quadrics. -/
theorem kleinTwSD4_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSD4 a b h c
      = (( (a^(6:ℕ)*b^(2:ℕ) - 3*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 2)) * kleinTwP0 a b h c
        + (( (2*a^(7:ℕ)*b - a^(2:ℕ)*b^(6:ℕ)) * h^(3:ℕ) ) * (c 3)) * kleinTwP1 a b h c
        + (( (10*a^(4:ℕ)*b^(4:ℕ)) * h^(3:ℕ) ) * (c 4)) * kleinTwP2 a b h c
        + (( (a^(7:ℕ)*b + 2*a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 0)) * kleinTwP3 a b h c := by
  simp only [kleinTwSD4, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_01` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_01_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_01 a b h c
      = (( (-a^(8:ℕ) + 13*a^(3:ℕ)*b^(5:ℕ)) * h ) * (c 4)) * kleinTwP0 a b h c
        + (( (2*a^(7:ℕ)*b + 4*a^(2:ℕ)*b^(6:ℕ)) * h ) * (c 0)) * kleinTwP1 a b h c
        + (( (3*a^(7:ℕ)*b - 9*a^(2:ℕ)*b^(6:ℕ)) * h ) * (c 1)) * kleinTwP2 a b h c
        + (( (-3*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h ) * (c 3)) * kleinTwP4 a b h c := by
  simp only [kleinTwSDD_01, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_02` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_02_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_02 a b h c
      = (( (-4*a^(5:ℕ)*b^(3:ℕ) + 2*b^(8:ℕ)) * h ) * (c 3)) * kleinTwP0 a b h c
        + (( (-9*a^(5:ℕ)*b^(3:ℕ) - 3*b^(8:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP1 a b h c
        + (( (-5*a^(6:ℕ)*b^(2:ℕ) - 5*a*b^(7:ℕ)) * h ) * (c 0)) * kleinTwP2 a b h c
        + (( (-a^(8:ℕ) + 3*a^(3:ℕ)*b^(5:ℕ)) * h ) * (c 1)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_02, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_03` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_03_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_03 a b h c
      = (( (-13*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h ) * (c 2)) * kleinTwP0 a b h c
        + (( (-9*a^(6:ℕ)*b^(2:ℕ) - 3*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP1 a b h c
        + (( (-a^(8:ℕ) + 3*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP2 a b h c
        + (( (4*a^(6:ℕ)*b^(2:ℕ) - 2*a*b^(7:ℕ)) * h ) * (c 0)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_03, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_04` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_04_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_04 a b h c
      = (( (-3*a^(8:ℕ) + 9*a^(3:ℕ)*b^(5:ℕ)) * h ) * (c 1)) * kleinTwP0 a b h c
        + (( (-3*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h^(2:ℕ) ) * (c 2)) * kleinTwP1 a b h c
        + (( (2*a^(8:ℕ) + 4*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP2 a b h c
        + (( (5*a^(7:ℕ)*b - 5*a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_04, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_12` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_12_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_12 a b h c
      = (( (5*a^(7:ℕ)*b - 5*a^(2:ℕ)*b^(6:ℕ)) * h ) * (c 2)) * kleinTwP0 a b h c
        + (( (2*a^(8:ℕ) + 4*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP1 a b h c
        + (( (-3*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP2 a b h c
        + (( (-3*a^(8:ℕ) + 9*a^(3:ℕ)*b^(5:ℕ)) * h ) * (c 0)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_12, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_13` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_13_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_13 a b h c
      = (( (4*a^(6:ℕ)*b^(2:ℕ) - 2*a*b^(7:ℕ)) * h ) * (c 1)) * kleinTwP0 a b h c
        + (( (-a^(8:ℕ) + 3*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 2)) * kleinTwP1 a b h c
        + (( (-9*a^(6:ℕ)*b^(2:ℕ) - 3*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP2 a b h c
        + (( (-13*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_13, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_14` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_14_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_14 a b h c
      = (( (-a^(8:ℕ) + 3*a^(3:ℕ)*b^(5:ℕ)) * h ) * (c 0)) * kleinTwP0 a b h c
        + (( (-5*a^(6:ℕ)*b^(2:ℕ) - 5*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 1)) * kleinTwP1 a b h c
        + (( (-9*a^(5:ℕ)*b^(3:ℕ) - 3*b^(8:ℕ)) * h^(2:ℕ) ) * (c 2)) * kleinTwP2 a b h c
        + (( (-4*a^(5:ℕ)*b^(3:ℕ) + 2*b^(8:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_14, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_23` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_23_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_23 a b h c
      = (( (-3*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h ) * (c 0)) * kleinTwP0 a b h c
        + (( (-a^(8:ℕ) + 13*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 1)) * kleinTwP1 a b h c
        + (( (2*a^(7:ℕ)*b + 4*a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 2)) * kleinTwP2 a b h c
        + (( (3*a^(7:ℕ)*b - 9*a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_23, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_24` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_24_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_24 a b h c
      = (( (-5*a^(6:ℕ)*b^(2:ℕ) - 5*a*b^(7:ℕ)) * h^(2:ℕ) ) * (c 4)) * kleinTwP0 a b h c
        + (( (-9*a^(5:ℕ)*b^(3:ℕ) - 3*b^(8:ℕ)) * h^(2:ℕ) ) * (c 0)) * kleinTwP1 a b h c
        + (( (-4*a^(5:ℕ)*b^(3:ℕ) + 2*b^(8:ℕ)) * h^(2:ℕ) ) * (c 1)) * kleinTwP2 a b h c
        + (( (-a^(8:ℕ) + 3*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP4 a b h c := by
  simp only [kleinTwSDD_24, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-- The mixed second partial `kleinTwSDD_34` is a combination of the twisted quadrics. -/
theorem kleinTwSDD_34_eq (a b h : R) (c : Fin 5 → R) :
    kleinTwSDD_34 a b h c
      = (( (3*a^(7:ℕ)*b - 9*a^(2:ℕ)*b^(6:ℕ)) * h^(2:ℕ) ) * (c 3)) * kleinTwP0 a b h c
        + (( (2*a^(7:ℕ)*b + 4*a^(2:ℕ)*b^(6:ℕ)) * h^(3:ℕ) ) * (c 4)) * kleinTwP1 a b h c
        + (( (-a^(8:ℕ) + 13*a^(3:ℕ)*b^(5:ℕ)) * h^(2:ℕ) ) * (c 0)) * kleinTwP2 a b h c
        + (( (-3*a^(5:ℕ)*b^(3:ℕ) - b^(8:ℕ)) * h^(2:ℕ) ) * (c 1)) * kleinTwP3 a b h c := by
  simp only [kleinTwSDD_34, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4]
  first | refl_ring1 | ring

/-! ## The vanishing -/

/-- The second polar of the twisted secant quintic vanishes on the twisted Klein curve: if
`kleinTwP a b h c = 0`, then `kleinTwSP2 a b h c u = 0` for every `u`. -/
theorem KleinTwSP2Vanishing {R : Type*} [CommRing R] (a b h : R) (c u : Fin 5 → R)
    (hc : ∀ k : Fin 5, Work.MotK.kleinTwP a b h c k = 0) :
    Work.MotK.kleinTwSP2 a b h c u = 0 := by
  have h0 : kleinTwP0 a b h c = 0 := hc 0
  have h1 : kleinTwP1 a b h c = 0 := hc 1
  have h2 : kleinTwP2 a b h c = 0 := hc 2
  have h3 : kleinTwP3 a b h c = 0 := hc 3
  have h4 : kleinTwP4 a b h c = 0 := hc 4
  rw [kleinTwSP2_eq, kleinTwSD0_eq, kleinTwSD1_eq, kleinTwSD2_eq, kleinTwSD3_eq, kleinTwSD4_eq,
    kleinTwSDD_01_eq, kleinTwSDD_02_eq, kleinTwSDD_03_eq, kleinTwSDD_04_eq, kleinTwSDD_12_eq,
    kleinTwSDD_13_eq, kleinTwSDD_14_eq, kleinTwSDD_23_eq, kleinTwSDD_24_eq, kleinTwSDD_34_eq]
  simp only [h0, h1, h2, h3, h4, mul_zero, zero_mul, zero_add, add_zero]

end Work.MotK.TwRule
