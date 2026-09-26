import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.omega_rank_two

/-!
# The trace of the cutting plane on the `RefuteDrop` configuration

At the linear configuration of `RefuteDrop/Config.lean` (the diffeomorphism `dropDiffeo` with
matrix `dropA`, the box `PBox dropS dropC dropCyc` with `dropS = 7/5`, `dropC = 0`,
`dropCyc = swap 0 2`, and the cutting plane `{x = 0}`, `dropU = 0`), the trace of the cutting
plane on the surface `F = dropDiffeo(F_std)` consists of two circles.  The trace of the plane
on the standard torus is parametrised, at the longitude parameter `u`, by the two meridian
parameters

`cos v = (-2 A(u)^2 ∓ c S(u)) / R(u)^2`,  `sin v = A(u) (-2c ± S(u)) / R(u)^2`,

where `A(u) = -(2/25) cos u - (39/100) sin u`, `c = 97/100`, `S(u) = sqrt (c^2 - 3 A(u)^2)` and
`R(u)^2 = A(u)^2 + c^2`; these are exactly the two solutions of the plane equation
`A(u) (2 + cos v) + c sin v = 0`, i.e. `(dropDiffeo (torusMap u v)) 0 = 0`.

Cut by the box, each trace circle becomes a finite union of arcs, and this module proves the
honest tameness predicate `Work.BoxShrink.PinchOff.TameClosedSlice` at this configuration: the
closure of the slice is a union of four arcs of the surface.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## The trace of the cutting plane -/

/-- The `(0,2)`-entry `97/100` of `dropA`, in the closed form used below. -/
def trC : ℝ := 97/100

theorem trC_eq : trC = (97 : ℝ) / 100 := rfl

/-- The value `A(u) = -(2/25) cos u - (39/100) sin u` of the first row of `dropA` on
`(cos u, sin u)`. -/
def trA (u : ℝ) : ℝ := -(2/25) * Real.cos u - (39/100) * Real.sin u

/-- The first row of `dropA` evaluated on `(cos u, sin u)`, matching `dropGform`. -/
theorem trA_eq (u : ℝ) :
    trA u = (-(2/25)) * Real.cos u + (-(39/100)) * Real.sin u := by
  simp only [trA]; ring

/-- The second row of `dropA` evaluated on `(cos u, sin u)`. -/
def trB1 (u : ℝ) : ℝ := (81/100) * Real.cos u + (53/50) * Real.sin u

/-- The third row of `dropA` evaluated on `(cos u, sin u)`. -/
def trB2 (u : ℝ) : ℝ := (49/100) * Real.cos u + (31/25) * Real.sin u

/-- `S(u) = sqrt (c^2 - 3 A(u)^2)`. -/
def trS (u : ℝ) : ℝ := Real.sqrt ((97/100)^2 - 3 * (trA u)^2)

/-- `R(u)^2 = A(u)^2 + c^2`. -/
def trR2 (u : ℝ) : ℝ := (trA u)^2 + (97/100)^2

/-- The two trace branches, in terms of `cos v` and `sin v`: branch `B`. -/
def trCosVb (u : ℝ) : ℝ := (-2 * (trA u)^2 - (97/100) * trS u) / trR2 u

/-- The two trace branches, in terms of `cos v` and `sin v`: branch `B`. -/
def trSinVb (u : ℝ) : ℝ := trA u * (-2 * (97/100) + trS u) / trR2 u

/-- The two trace branches, in terms of `cos v` and `sin v`: branch `A`. -/
def trCosVa (u : ℝ) : ℝ := (-2 * (trA u)^2 + (97/100) * trS u) / trR2 u

/-- The two trace branches, in terms of `cos v` and `sin v`: branch `A`. -/
def trSinVa (u : ℝ) : ℝ := trA u * (-2 * (97/100) - trS u) / trR2 u

/-- The point of the distortion's surface above the parameter pair with the given values of
`cos v, sin v`. -/
def trPt (u cv sv : ℝ) : R3 := WithLp.toLp 2 ![
    trA u * (2 + cv) + (97/100) * sv,
    trB1 u * (2 + cv) - (3/25) * sv,
    trB2 u * (2 + cv) + (59/100) * sv]

/-- The `B` branch of the trace, as a curve in `ℝ³`. -/
def gammaB (u : ℝ) : R3 := trPt u (trCosVb u) (trSinVb u)

/-- The `A` branch of the trace, as a curve in `ℝ³`. -/
def gammaA (u : ℝ) : R3 := trPt u (trCosVa u) (trSinVa u)

/-! ## Elementary bounds -/

/-- `|A(u)| ≤ sqrt (317/2000)` for every `u`. -/
theorem trA_sq_le (u : ℝ) : (trA u)^2 ≤ (317/2000 : ℝ) := by
  have h1 : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := Real.cos_sq_add_sin_sq u
  have h2 : (trA u)^2 ≤ ((2/25 : ℝ)^2 + (39/100)^2) := by
    have h3 : (trA u)^2 + ((2/25) * Real.sin u - (39/100) * Real.cos u)^2
        = ((2/25 : ℝ)^2 + (39/100)^2) := by
      simp only [trA]; nlinarith [h1]
    nlinarith [sq_nonneg ((2/25) * Real.sin u - (39/100) * Real.cos u)]
  have : ((2/25 : ℝ)^2 + (39/100)^2) = 317/2000 := by norm_num
  linarith [h2, this.symm.le, this.le]

/-- `c^2 - 3 A(u)^2 > 0`: the plane is transverse to the surface in the parameter plane. -/
theorem trS_arg_pos (u : ℝ) : 0 < (97/100)^2 - 3 * (trA u)^2 := by
  have h := trA_sq_le u
  nlinarith [h]

theorem trS_pos (u : ℝ) : 0 < trS u := by
  rw [trS, Real.sqrt_pos]
  exact trS_arg_pos u

theorem trS_nonneg (u : ℝ) : 0 ≤ trS u := le_of_lt (trS_pos u)

theorem trS_sq (u : ℝ) : (trS u)^2 = (97/100)^2 - 3 * (trA u)^2 := by
  rw [trS, Real.sq_sqrt (le_of_lt (trS_arg_pos u))]

theorem trS_le (u : ℝ) : trS u ≤ 97/100 := by
  have h := trS_sq u
  have h2 : 0 ≤ (trA u)^2 := sq_nonneg _
  nlinarith [h, h2, trS_nonneg u]

theorem trR2_pos (u : ℝ) : 0 < trR2 u := by
  have := trS_pos u
  have := trS_sq u
  have h : (97/100)^2 - 3 * (trA u)^2 > 0 := trS_arg_pos u
  simp only [trR2]
  nlinarith

theorem trR2_ne_zero (u : ℝ) : trR2 u ≠ 0 := ne_of_gt (trR2_pos u)

/-- The classical identity `(2c - S)(2c + S) = 3 R^2`. -/
theorem tr_two_c_sub_mul_add (u : ℝ) :
    (2 * (97/100) - trS u) * (2 * (97/100) + trS u) = 3 * trR2 u := by
  have h := trS_sq u
  simp only [trR2] at *
  nlinarith [h]

theorem tr_two_c_add_pos (u : ℝ) : 0 < 2 * (97/100) + trS u := by
  have := trS_nonneg u; linarith

theorem tr_two_c_sub_pos (u : ℝ) : 0 < 2 * (97/100) - trS u := by
  have := trS_le u; linarith

theorem trR2_eq (u : ℝ) : trR2 u = (trA u)^2 + (97/100)^2 := rfl

/-! ## The branch data lies on the unit circle -/

theorem trCosVb_sq_add (u : ℝ) : (trCosVb u)^2 + (trSinVb u)^2 = 1 := by
  have hS := trS_sq u
  have hR := trR2_pos u
  simp only [trCosVb, trSinVb, trR2] at *
  field_simp
  nlinarith [hS]

theorem trCosVa_sq_add (u : ℝ) : (trCosVa u)^2 + (trSinVa u)^2 = 1 := by
  have hS := trS_sq u
  have hR := trR2_pos u
  simp only [trCosVa, trSinVa, trR2] at *
  field_simp
  nlinarith [hS]

/-! ## The plane equation -/

/-- **The trace condition**: the plane coordinate of `trPt u cv sv` vanishes whenever
`cv^2 + sv^2 = 1`. -/
theorem trPt_plane (u cv sv : ℝ) :
    (trPt u cv sv) 0 = trA u * (2 + cv) + (97/100) * sv := by
  simp [trPt]

/-- The plane equation for the branch data: `A (2 + cos v) + c sin v = 0`. -/
theorem tr_plane_eq (u : ℝ) :
    trA u * (2 + trCosVb u) + (97/100) * trSinVb u = 0 := by
  have hR := trR2_ne_zero u
  simp only [trCosVb, trSinVb, trR2]
  field_simp
  ring

theorem tr_plane_eq_a (u : ℝ) :
    trA u * (2 + trCosVa u) + (97/100) * trSinVa u = 0 := by
  have hR := trR2_ne_zero u
  simp only [trCosVa, trSinVa, trR2]
  field_simp
  ring

/-! ## The two numerators of the coordinate formulae -/

/-- `N1(u) = c B1(u) + (3/25) A(u)`, the numerator of the first coordinate along the trace. -/
def trN1 (u : ℝ) : ℝ := (97/100) * trB1 u + (3/25) * trA u

/-- `N2(u) = c B2(u) - (59/100) A(u)`, the numerator of the second coordinate along the trace. -/
def trN2 (u : ℝ) : ℝ := (97/100) * trB2 u - (59/100) * trA u

/-- The first row of `dropA` on `(cos u, sin u)`, in the coordinates of `trA`. -/
theorem trA_apply (u : ℝ) : trA u = -(2/25) * Real.cos u - (39/100) * Real.sin u := rfl

theorem trB1_apply (u : ℝ) : trB1 u = (81/100) * Real.cos u + (53/50) * Real.sin u := rfl

theorem trB2_apply (u : ℝ) : trB2 u = (49/100) * Real.cos u + (31/25) * Real.sin u := rfl

/-! ## `trPt` as the image of the parametrisation -/

/-- The parametrised surface of the counterexample. -/
theorem psi_eq_torusMap (θ φ : ℝ) :
    (Work.Smooth.Morse.torus dropDiffeo).psi θ φ = dropVec (Work.Core.torusMap θ φ) := by
  rw [Work.Smooth.Morse.torus_psi, param_dropDiffeo]

/-- `trPt u (cos v) (sin v)` is the image under `dropVec` of the point of the standard torus with
parameters `(u, v)`. -/
theorem trPt_eq_dropVec_torusMap (u v : ℝ) :
    trPt u (Real.cos v) (Real.sin v) = dropVec (Work.Core.torusMap u v) := by
  ext i
  fin_cases i <;>
    simp [trPt, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
      Work.Core.torusMap_apply_two, dropVec_coord_zero, dropVec_coord_one,
      dropVec_coord_two, trA, trB1, trB2] <;> ring

/-! ## Periodicity and continuity -/

theorem trA_add_two_pi (u : ℝ) : trA (u + 2 * Real.pi) = trA u := by
  simp [trA, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem trB1_add_two_pi (u : ℝ) : trB1 (u + 2 * Real.pi) = trB1 u := by
  simp [trB1, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem trB2_add_two_pi (u : ℝ) : trB2 (u + 2 * Real.pi) = trB2 u := by
  simp [trB2, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem trS_add_two_pi (u : ℝ) : trS (u + 2 * Real.pi) = trS u := by
  simp [trS, trA_add_two_pi]

theorem trR2_add_two_pi (u : ℝ) : trR2 (u + 2 * Real.pi) = trR2 u := by
  simp [trR2, trA_add_two_pi]

theorem trCosVb_add_two_pi (u : ℝ) : trCosVb (u + 2 * Real.pi) = trCosVb u := by
  simp [trCosVb, trS_add_two_pi, trR2_add_two_pi, trA_add_two_pi]

theorem trSinVb_add_two_pi (u : ℝ) : trSinVb (u + 2 * Real.pi) = trSinVb u := by
  simp [trSinVb, trS_add_two_pi, trR2_add_two_pi, trA_add_two_pi]

theorem trCosVa_add_two_pi (u : ℝ) : trCosVa (u + 2 * Real.pi) = trCosVa u := by
  simp [trCosVa, trS_add_two_pi, trR2_add_two_pi, trA_add_two_pi]

theorem trSinVa_add_two_pi (u : ℝ) : trSinVa (u + 2 * Real.pi) = trSinVa u := by
  simp [trSinVa, trS_add_two_pi, trR2_add_two_pi, trA_add_two_pi]

/-! ## The key algebraic identities behind the coordinate formulae -/

/-- The algebraic identity behind the first coordinate on the `B` branch. -/
theorem tr_coord1_key_b (A B1 S : ℝ) (hS : S^2 = (97/100)^2 - 3*A^2) :
    (B1 * (2 + (-2*A^2 - (97/100)*S)/(A^2 + (97/100)^2))
      - (3/25)*(A*(-2*(97/100)+S)/(A^2 + (97/100)^2))) * (2*(97/100)+S)
      = 3*((97/100)*B1 + (3/25)*A) := by
  have hmain : (B1 * (2*(A^2 + (97/100)^2) - 2*A^2 - (97/100)*S) - (3/25)*A*(-2*(97/100)+S)) * (2*(97/100)+S)
      = 3*(A^2 + (97/100)^2)*((97/100)*B1 + (3/25)*A) := by
    linear_combination (-((97/100)*B1 + (3/25)*A)) * hS
  have hgoal : (B1 * (2 + (-2*A^2 - (97/100)*S)/(A^2 + (97/100)^2))
        - (3/25)*(A*(-2*(97/100)+S)/(A^2 + (97/100)^2))) * (2*(97/100)+S)
      = ((B1 * (2*(A^2+(97/100)^2) - 2*A^2 - (97/100)*S) - (3/25)*A*(-2*(97/100)+S)) * (2*(97/100)+S))/(A^2+(97/100)^2) := by
    field_simp
    ring
  rw [hgoal, hmain]
  field_simp

/-- The algebraic identity behind the second coordinate on the `B` branch. -/
theorem tr_coord2_key_b (A B2 S : ℝ) (hS : S^2 = (97/100)^2 - 3*A^2) :
    (B2 * (2 + (-2*A^2 - (97/100)*S)/(A^2 + (97/100)^2))
      + (59/100)*(A*(-2*(97/100)+S)/(A^2 + (97/100)^2))) * (2*(97/100)+S)
      = 3*((97/100)*B2 - (59/100)*A) := by
  have hmain : (B2 * (2*(A^2 + (97/100)^2) - 2*A^2 - (97/100)*S) + (59/100)*A*(-2*(97/100)+S)) * (2*(97/100)+S)
      = 3*(A^2 + (97/100)^2)*((97/100)*B2 - (59/100)*A) := by
    linear_combination (-((97/100)*B2 - (59/100)*A)) * hS
  have hgoal : (B2 * (2 + (-2*A^2 - (97/100)*S)/(A^2 + (97/100)^2))
        + (59/100)*(A*(-2*(97/100)+S)/(A^2 + (97/100)^2))) * (2*(97/100)+S)
      = ((B2 * (2*(A^2+(97/100)^2) - 2*A^2 - (97/100)*S) + (59/100)*A*(-2*(97/100)+S)) * (2*(97/100)+S))/(A^2+(97/100)^2) := by
    field_simp
    ring
  rw [hgoal, hmain]
  field_simp

/-- The algebraic identity behind the first coordinate on the `A` branch. -/
theorem tr_coord1_key_a (A B1 S : ℝ) (hS : S^2 = (97/100)^2 - 3*A^2) :
    (B1 * (2 + (-2*A^2 + (97/100)*S)/(A^2 + (97/100)^2))
      - (3/25)*(A*(-2*(97/100)-S)/(A^2 + (97/100)^2))) * (2*(97/100)-S)
      = 3*((97/100)*B1 + (3/25)*A) := by
  have hmain : (B1 * (2*(A^2 + (97/100)^2) - 2*A^2 + (97/100)*S) - (3/25)*A*(-2*(97/100)-S)) * (2*(97/100)-S)
      = 3*(A^2 + (97/100)^2)*((97/100)*B1 + (3/25)*A) := by
    linear_combination (-((97/100)*B1 + (3/25)*A)) * hS
  have hgoal : (B1 * (2 + (-2*A^2 + (97/100)*S)/(A^2 + (97/100)^2))
        - (3/25)*(A*(-2*(97/100)-S)/(A^2 + (97/100)^2))) * (2*(97/100)-S)
      = ((B1 * (2*(A^2+(97/100)^2) - 2*A^2 + (97/100)*S) - (3/25)*A*(-2*(97/100)-S)) * (2*(97/100)-S))/(A^2+(97/100)^2) := by
    field_simp
    ring
  rw [hgoal, hmain]
  field_simp

/-- The algebraic identity behind the second coordinate on the `A` branch. -/
theorem tr_coord2_key_a (A B2 S : ℝ) (hS : S^2 = (97/100)^2 - 3*A^2) :
    (B2 * (2 + (-2*A^2 + (97/100)*S)/(A^2 + (97/100)^2))
      + (59/100)*(A*(-2*(97/100)-S)/(A^2 + (97/100)^2))) * (2*(97/100)-S)
      = 3*((97/100)*B2 - (59/100)*A) := by
  have hmain : (B2 * (2*(A^2 + (97/100)^2) - 2*A^2 + (97/100)*S) + (59/100)*A*(-2*(97/100)-S)) * (2*(97/100)-S)
      = 3*(A^2 + (97/100)^2)*((97/100)*B2 - (59/100)*A) := by
    linear_combination (-((97/100)*B2 - (59/100)*A)) * hS
  have hgoal : (B2 * (2 + (-2*A^2 + (97/100)*S)/(A^2 + (97/100)^2))
        + (59/100)*(A*(-2*(97/100)-S)/(A^2 + (97/100)^2))) * (2*(97/100)-S)
      = ((B2 * (2*(A^2+(97/100)^2) - 2*A^2 + (97/100)*S) + (59/100)*A*(-2*(97/100)-S)) * (2*(97/100)-S))/(A^2+(97/100)^2) := by
    field_simp
    ring
  rw [hgoal, hmain]
  field_simp

/-! ## The coordinate formulae -/

/-- **The first coordinate along the `B` branch.** -/
theorem gammaB_coord_one (u : ℝ) :
    (gammaB u) 1 * (2 * (97/100) + trS u) = 3 * trN1 u := by
  have h1 : (gammaB u) 1 = trB1 u * (2 + trCosVb u) - (3/25) * trSinVb u := by
    simp [gammaB, trPt]
  rw [h1]
  have h2 := tr_coord1_key_b (trA u) (trB1 u) (trS u) (trS_sq u)
  simp only [trCosVb, trSinVb, trN1, trR2]
  exact h2

/-- **The second coordinate along the `B` branch.** -/
theorem gammaB_coord_two (u : ℝ) :
    (gammaB u) 2 * (2 * (97/100) + trS u) = 3 * trN2 u := by
  have h1 : (gammaB u) 2 = trB2 u * (2 + trCosVb u) + (59/100) * trSinVb u := by
    simp [gammaB, trPt]
  rw [h1]
  have h2 := tr_coord2_key_b (trA u) (trB2 u) (trS u) (trS_sq u)
  simp only [trCosVb, trSinVb, trN2, trR2]
  exact h2

/-- **The first coordinate along the `A` branch.** -/
theorem gammaA_coord_one (u : ℝ) :
    (gammaA u) 1 * (2 * (97/100) - trS u) = 3 * trN1 u := by
  have h1 : (gammaA u) 1 = trB1 u * (2 + trCosVa u) - (3/25) * trSinVa u := by
    simp [gammaA, trPt]
  rw [h1]
  have h2 := tr_coord1_key_a (trA u) (trB1 u) (trS u) (trS_sq u)
  simp only [trCosVa, trSinVa, trN1, trR2]
  exact h2

/-- **The second coordinate along the `A` branch.** -/
theorem gammaA_coord_two (u : ℝ) :
    (gammaA u) 2 * (2 * (97/100) - trS u) = 3 * trN2 u := by
  have h1 : (gammaA u) 2 = trB2 u * (2 + trCosVa u) + (59/100) * trSinVa u := by
    simp [gammaA, trPt]
  rw [h1]
  have h2 := tr_coord2_key_a (trA u) (trB2 u) (trS u) (trS_sq u)
  simp only [trCosVa, trSinVa, trN2, trR2]
  exact h2

/-! ## Periodicity and continuity -/

theorem trPt_add_two_pi (u cv sv : ℝ) :
    trPt (u + 2 * Real.pi) cv sv = trPt u cv sv := by
  ext i
  fin_cases i <;> simp [trPt, trA_add_two_pi, trB1_add_two_pi, trB2_add_two_pi]

theorem gammaB_add_two_pi (u : ℝ) : gammaB (u + 2 * Real.pi) = gammaB u := by
  ext i
  fin_cases i <;> simp [gammaB, trPt, trA_add_two_pi, trB1_add_two_pi, trB2_add_two_pi,
    trCosVb_add_two_pi, trSinVb_add_two_pi]

theorem gammaA_add_two_pi (u : ℝ) : gammaA (u + 2 * Real.pi) = gammaA u := by
  ext i
  fin_cases i <;> simp [gammaA, trPt, trA_add_two_pi, trB1_add_two_pi, trB2_add_two_pi,
    trCosVa_add_two_pi, trSinVa_add_two_pi]

theorem continuous_trA : Continuous trA := by
  unfold trA; fun_prop

theorem continuous_trS : Continuous trS := by
  have h := continuous_trA
  unfold trS; fun_prop

theorem continuous_trR2 : Continuous trR2 := by
  have h := continuous_trA
  unfold trR2; fun_prop

theorem continuous_trCosVb : Continuous trCosVb := by
  have hA := continuous_trA; have hS := continuous_trS; have hR := continuous_trR2
  unfold trCosVb trR2
  refine Continuous.div ?_ ?_ ?_ <;> try fun_prop
  intro u; positivity

theorem continuous_trSinVb : Continuous trSinVb := by
  have hA := continuous_trA; have hS := continuous_trS; have hR := continuous_trR2
  unfold trSinVb trR2
  refine Continuous.div ?_ ?_ ?_ <;> try fun_prop
  intro u; positivity

theorem continuous_trCosVa : Continuous trCosVa := by
  have hA := continuous_trA; have hS := continuous_trS; have hR := continuous_trR2
  unfold trCosVa trR2
  refine Continuous.div ?_ ?_ ?_ <;> try fun_prop
  intro u; positivity

theorem continuous_trSinVa : Continuous trSinVa := by
  have hA := continuous_trA; have hS := continuous_trS; have hR := continuous_trR2
  unfold trSinVa trR2
  refine Continuous.div ?_ ?_ ?_ <;> try fun_prop
  intro u; positivity

set_option maxHeartbeats 800000 in
theorem continuous_trPt : Continuous (fun p : ℝ × ℝ × ℝ => trPt p.1 p.2.1 p.2.2) := by
  unfold trPt trA trB1 trB2; fun_prop

set_option maxHeartbeats 1600000 in
theorem continuous_gammaB : Continuous gammaB := by
  have h2 := continuous_trCosVb
  have h3 := continuous_trSinVb
  unfold gammaB trPt trA trB1 trB2
  fun_prop

set_option maxHeartbeats 1600000 in
theorem continuous_gammaA : Continuous gammaA := by
  have h2 := continuous_trCosVa
  have h3 := continuous_trSinVa
  unfold gammaA trPt trA trB1 trB2
  fun_prop

/-! ## An angle parametrising a pair `(cos v, sin v)` of the unit circle -/

/-- An angle whose cosine and sine are `cv` and `sv` for a point of the unit circle. -/
noncomputable def trAng (cv sv : ℝ) : ℝ := if 0 ≤ sv then Real.arccos cv else -Real.arccos cv

theorem trAng_cos (cv sv : ℝ) (h : cv^2 + sv^2 = 1) : Real.cos (trAng cv sv) = cv := by
  have h1 : -1 ≤ cv := by nlinarith [sq_nonneg sv, h]
  have h2 : cv ≤ 1 := by nlinarith [sq_nonneg sv, h]
  unfold trAng
  split
  · exact Real.cos_arccos h1 h2
  · rw [Real.cos_neg, Real.cos_arccos h1 h2]

theorem trAng_sin (cv sv : ℝ) (h : cv^2 + sv^2 = 1) : Real.sin (trAng cv sv) = sv := by
  have hsq : 1 - cv^2 = sv^2 := by linarith
  unfold trAng
  split_ifs with hsv
  · rw [Real.sin_arccos, hsq, Real.sqrt_sq hsv]
  · rw [Real.sin_neg, Real.sin_arccos, hsq, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith : sv < 0)]
    ring

/-! ## The branches lie on the surface -/

theorem gammaB_mem_carrier (u : ℝ) :
    gammaB u ∈ (Work.Smooth.Morse.torus dropDiffeo).carrier := by
  refine ⟨(u, trAng (trCosVb u) (trSinVb u)), ?_⟩
  change (Work.Smooth.Morse.torus dropDiffeo).psi u (trAng (trCosVb u) (trSinVb u)) = gammaB u
  rw [psi_eq_torusMap]
  rw [← trPt_eq_dropVec_torusMap u (trAng (trCosVb u) (trSinVb u))]
  congr 1
  · exact trAng_cos (trCosVb u) (trSinVb u) (trCosVb_sq_add u)
  · exact trAng_sin (trCosVb u) (trSinVb u) (trCosVb_sq_add u)

theorem gammaA_mem_carrier (u : ℝ) :
    gammaA u ∈ (Work.Smooth.Morse.torus dropDiffeo).carrier := by
  refine ⟨(u, trAng (trCosVa u) (trSinVa u)), ?_⟩
  change (Work.Smooth.Morse.torus dropDiffeo).psi u (trAng (trCosVa u) (trSinVa u)) = gammaA u
  rw [psi_eq_torusMap]
  rw [← trPt_eq_dropVec_torusMap u (trAng (trCosVa u) (trSinVa u))]
  congr 1
  · exact trAng_cos (trCosVa u) (trSinVa u) (trCosVa_sq_add u)
  · exact trAng_sin (trCosVa u) (trSinVa u) (trCosVa_sq_add u)

/-! ## The branches lie in the cutting plane -/

theorem gammaB_coord_zero (u : ℝ) : (gammaB u) 0 = 0 := by
  have h1 : (gammaB u) 0 = trA u * (2 + trCosVb u) + (97/100) * trSinVb u := by
    simp [gammaB, trPt]
  rw [h1, tr_plane_eq]

theorem gammaA_coord_zero (u : ℝ) : (gammaA u) 0 = 0 := by
  have h1 : (gammaA u) 0 = trA u * (2 + trCosVa u) + (97/100) * trSinVa u := by
    simp [gammaA, trPt]
  rw [h1, tr_plane_eq_a]

/-- The branches lie in the cutting plane `{x = 0}` of the configuration. -/
theorem gammaB_mem_plane (u : ℝ) :
    (gammaB u) (dropCyc 2) = dropC (dropCyc 2) + dropU := by
  have h : dropCyc (2 : Fin 3) = 0 := by decide
  rw [h, gammaB_coord_zero u]
  simp [dropC, dropU]

theorem gammaA_mem_plane (u : ℝ) :
    (gammaA u) (dropCyc 2) = dropC (dropCyc 2) + dropU := by
  have h : dropCyc (2 : Fin 3) = 0 := by decide
  rw [h, gammaA_coord_zero u]
  simp [dropC, dropU]

/-! ## The box norm along the branches -/

/-- The box norm of the configuration in coordinates. -/
theorem boxNorm_drop_eq (y : R3) :
    Submission.boxNorm dropC dropCyc y =
      max (max |y 2| (|y 1| / (2 : ℝ) ^ (1 / 3 : ℝ))) (|y 0| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Submission.boxNorm, show dropCyc (0 : Fin 3) = 2 from by decide,
    show dropCyc (1 : Fin 3) = 1 from by decide,
    show dropCyc (2 : Fin 3) = 0 from by decide,
    show dropC (0 : Fin 3) = 0 from by simp [dropC],
    show dropC (1 : Fin 3) = 0 from by simp [dropC],
    show dropC (2 : Fin 3) = 0 from by simp [dropC],
    Submission.boxSide_zero, Submission.boxSide_one, Submission.boxSide_two]
  simp

theorem boxNorm_gammaB (u : ℝ) :
    Submission.boxNorm dropC dropCyc (gammaB u)
      = max |(gammaB u) 2| (|(gammaB u) 1| / (2 : ℝ) ^ (1 / 3 : ℝ)) := by
  rw [boxNorm_drop_eq, gammaB_coord_zero u, abs_zero, zero_div, max_eq_left]
  exact le_trans (abs_nonneg _) (le_max_left _ _)

theorem boxNorm_gammaA (u : ℝ) :
    Submission.boxNorm dropC dropCyc (gammaA u)
      = max |(gammaA u) 2| (|(gammaA u) 1| / (2 : ℝ) ^ (1 / 3 : ℝ)) := by
  rw [boxNorm_drop_eq, gammaA_coord_zero u, abs_zero, zero_div, max_eq_left]
  exact le_trans (abs_nonneg _) (le_max_left _ _)

/-! ## The trace of the plane on the surface is the union of the two branches -/

/-- **Solving the plane equation.**  A point `(X, Y)` of the unit circle on which the linear form
`A (2 + X) + c Y` vanishes is one of the two trace data. -/
theorem tr_solve (u X Y : ℝ) (hX : X^2 + Y^2 = 1)
    (hpl : trA u * (2 + X) + (97/100) * Y = 0) :
    (X = trCosVb u ∧ Y = trSinVb u) ∨ (X = trCosVa u ∧ Y = trSinVa u) := by
  have hb : (trCosVb u)^2 + (trSinVb u)^2 = 1 := trCosVb_sq_add u
  have ha : (trCosVa u)^2 + (trSinVa u)^2 = 1 := trCosVa_sq_add u
  have hpb := tr_plane_eq u
  have hpa := tr_plane_eq_a u
  have keyb : X = trCosVb u ∨ X + trCosVb u = (trA u / (97/100)) * (Y + trSinVb u) := by
    have h1 : trA u * (X - trCosVb u) + (97/100) * (Y - trSinVb u) = 0 := by linarith [hpl, hpb]
    have h2 : (X - trCosVb u) * (X + trCosVb u) + (Y - trSinVb u) * (Y + trSinVb u) = 0 := by
      nlinarith [hX, hb]
    rcases eq_or_ne X (trCosVb u) with h | h
    · exact Or.inl h
    · right
      have h3 : (97/100) * (Y - trSinVb u) = -trA u * (X - trCosVb u) := by linarith [h1]
      have h5a : (97/100) * ((X - trCosVb u) * (X + trCosVb u))
          = -(97/100) * ((Y - trSinVb u) * (Y + trSinVb u)) := by linarith [h2]
      have h5b : (97/100) * ((Y - trSinVb u) * (Y + trSinVb u))
          = (-trA u * (X - trCosVb u)) * (Y + trSinVb u) := by rw [← mul_assoc, h3]
      have h5 : (X - trCosVb u) * ((97/100) * (X + trCosVb u) - trA u * (Y + trSinVb u)) = 0 := by
        nlinarith [h5a, h5b]
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd (by linarith) h
      · have h7 : (97/100) * (X + trCosVb u) = trA u * (Y + trSinVb u) := by linarith
        field_simp
        linarith
  have keya : X = trCosVa u ∨ X + trCosVa u = (trA u / (97/100)) * (Y + trSinVa u) := by
    have h1 : trA u * (X - trCosVa u) + (97/100) * (Y - trSinVa u) = 0 := by linarith [hpl, hpa]
    have h2 : (X - trCosVa u) * (X + trCosVa u) + (Y - trSinVa u) * (Y + trSinVa u) = 0 := by
      nlinarith [hX, ha]
    rcases eq_or_ne X (trCosVa u) with h | h
    · exact Or.inl h
    · right
      have h3 : (97/100) * (Y - trSinVa u) = -trA u * (X - trCosVa u) := by linarith [h1]
      have h5a : (97/100) * ((X - trCosVa u) * (X + trCosVa u))
          = -(97/100) * ((Y - trSinVa u) * (Y + trSinVa u)) := by linarith [h2]
      have h5b : (97/100) * ((Y - trSinVa u) * (Y + trSinVa u))
          = (-trA u * (X - trCosVa u)) * (Y + trSinVa u) := by rw [← mul_assoc, h3]
      have h5 : (X - trCosVa u) * ((97/100) * (X + trCosVa u) - trA u * (Y + trSinVa u)) = 0 := by
        nlinarith [h5a, h5b]
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd (by linarith) h
      · have h7 : (97/100) * (X + trCosVa u) = trA u * (Y + trSinVa u) := by linarith
        field_simp
        linarith
  rcases keyb with hb1 | hb1
  · refine Or.inl ⟨hb1, ?_⟩
    have h3 : (97/100) * (Y - trSinVb u) = -trA u * (X - trCosVb u) := by linarith [hpl, hpb]
    rw [hb1] at h3; linarith
  rcases keya with ha1 | ha1
  · refine Or.inr ⟨ha1, ?_⟩
    have h3 : (97/100) * (Y - trSinVa u) = -trA u * (X - trCosVa u) := by linarith [hpl, hpa]
    rw [ha1] at h3; linarith
  · exfalso
    have hdiff : (97/100) * (trCosVb u - trCosVa u) = trA u * (trSinVb u - trSinVa u) := by
      have hc : (97/100 : ℝ) ≠ 0 := by norm_num
      field_simp at hb1 ha1
      linarith [hb1, ha1]
    have hLc : trR2 u * (trCosVb u - trCosVa u) = -2 * (97/100) * trS u := by
      rw [trCosVb, trCosVa, trR2]; field_simp; ring
    have hRc : trR2 u * (trSinVb u - trSinVa u) = 2 * trA u * trS u := by
      rw [trSinVb, trSinVa, trR2]; field_simp; ring
    have h15 : (97/100) * (-2 * (97/100) * trS u) = trA u * (2 * trA u * trS u) := by
      calc (97/100) * (-2 * (97/100) * trS u)
          = (97/100) * (trR2 u * (trCosVb u - trCosVa u)) := by rw [hLc]
        _ = trR2 u * ((97/100) * (trCosVb u - trCosVa u)) := by ring
        _ = trR2 u * (trA u * (trSinVb u - trSinVa u)) := by rw [hdiff]
        _ = trA u * (trR2 u * (trSinVb u - trSinVa u)) := by ring
        _ = trA u * (2 * trA u * trS u) := by rw [hRc]
    have hSpos := trS_pos u
    have hAeq : (trA u)^2 = -((97/100)^2) := by nlinarith [h15, hSpos]
    nlinarith [hAeq, sq_nonneg (trA u)]

/-- **A point of the surface in the cutting plane lies on one of the two trace branches.** -/
theorem trace_eq_branches (x : R3)
    (hx : x ∈ (Work.Smooth.Morse.torus dropDiffeo).carrier)
    (hpl : x (dropCyc 2) = dropC (dropCyc 2) + dropU) :
    (∃ u : ℝ, x = gammaB u) ∨ (∃ u : ℝ, x = gammaA u) := by
  obtain ⟨⟨θ, φ⟩, hθφ'⟩ := hx
  have hθφ : (Work.Smooth.Morse.torus dropDiffeo).psi θ φ = x := hθφ'
  have hplane : trA θ * (2 + Real.cos φ) + (97/100) * Real.sin φ = 0 := by
    have h0 : x 0 = 0 := by
      have h : dropCyc (2 : Fin 3) = 0 := by decide
      rw [h] at hpl
      simpa [dropC, dropU] using hpl
    have h1 : -2 / 25 * ((2 + Real.cos φ) * Real.cos θ)
        + -39 / 100 * ((2 + Real.cos φ) * Real.sin θ) + 97 / 100 * Real.sin φ = 0 := by
      rw [← hθφ] at h0
      rw [psi_eq_torusMap, dropVec_coord_zero, Work.Core.torusMap_apply_zero,
        Work.Core.torusMap_apply_one, Work.Core.torusMap_apply_two] at h0
      linarith [h0]
    unfold trA
    linarith [h1]
  rcases tr_solve θ (Real.cos φ) (Real.sin φ) (Real.cos_sq_add_sin_sq φ) hplane with
    ⟨hX, hY⟩ | ⟨hX, hY⟩
  · left
    refine ⟨θ, ?_⟩
    rw [← hθφ, psi_eq_torusMap, ← trPt_eq_dropVec_torusMap θ φ, hX, hY]
    rfl
  · right
    refine ⟨θ, ?_⟩
    rw [← hθφ, psi_eq_torusMap, ← trPt_eq_dropVec_torusMap θ φ, hX, hY]
    rfl
/-! ## Pythagorean angles and trigonometric bounds on intervals between them -/

/-- The angle `2 * arctan t`, whose cosine and sine are rational for rational `t`. -/
noncomputable def ang (t : ℝ) : ℝ := 2 * Real.arctan t

theorem ang_strictMono : StrictMono ang := by
  intro a b hab
  have h := Real.arctan_lt_arctan_iff.mpr hab
  simp only [ang]
  linarith

theorem ang_le_ang {t1 t2 : ℝ} (h : t1 ≤ t2) : ang t1 ≤ ang t2 := ang_strictMono.monotone h

theorem ang_lt_ang {t1 t2 : ℝ} (h : t1 < t2) : ang t1 < ang t2 := ang_strictMono h

theorem ang_pos {t : ℝ} (h : 0 < t) : 0 < ang t := by
  have := Real.arctan_pos.mpr h
  simp only [ang]; linarith

theorem ang_lt_pi {t : ℝ} (h : 0 < t) : ang t < Real.pi := by
  have h1 := Real.arctan_lt_pi_div_two t
  simp only [ang]; linarith [Real.pi_pos]

theorem ang_one : ang 1 = Real.pi / 2 := by
  simp only [ang, Real.arctan_one]; ring

theorem ang_eq_pi_div_two_iff {t : ℝ} (h : 0 < t) : ang t = Real.pi / 2 ↔ t = 1 := by
  constructor
  · intro ht
    exact ang_strictMono.injective (by rw [ht, ang_one])
  · intro ht; rw [ht, ang_one]

theorem ang_pi_div_two_lt {t : ℝ} (h : 1 < t) : Real.pi / 2 < ang t := by
  rw [← ang_one]
  exact ang_lt_ang h

theorem ang_lt_pi_div_two {t : ℝ} (h : 0 < t) (h1 : t < 1) : ang t < Real.pi / 2 := by
  rw [← ang_one]
  exact ang_lt_ang h1

theorem cos_ang (t : ℝ) : Real.cos (ang t) = (1 - t^2) / (1 + t^2) := by
  have h1 : (0:ℝ) < 1 + t^2 := by positivity
  rw [ang, Real.cos_two_mul, Real.cos_arctan, div_pow, Real.sq_sqrt (le_of_lt h1)]
  field_simp
  ring

theorem sin_ang (t : ℝ) : Real.sin (ang t) = 2 * t / (1 + t^2) := by
  have h1 : (0:ℝ) < 1 + t^2 := by positivity
  rw [ang, Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
  field_simp
  rw [Real.sq_sqrt (le_of_lt h1)]

theorem cos_ang_pos {t : ℝ} (h : 0 < t) (h1 : t < 1) : 0 < Real.cos (ang t) := by
  rw [cos_ang]
  exact div_pos (by nlinarith) (by positivity)

theorem cos_ang_neg {t : ℝ} (h : 1 < t) : Real.cos (ang t) < 0 := by
  rw [cos_ang]
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

theorem sin_ang_pos {t : ℝ} (h : 0 < t) : 0 < Real.sin (ang t) := by
  rw [sin_ang]; positivity

/-- `sin` is strictly antitone on `[π/2, π]`. -/
theorem strictAntiOn_sin_Icc : StrictAntiOn Real.sin (Set.Icc (Real.pi / 2) Real.pi) := by
  intro x hx y hy hxy
  have h1 : Real.sin x = Real.cos (x - Real.pi / 2) := (Real.cos_sub_pi_div_two x).symm
  have h2 : Real.sin y = Real.cos (y - Real.pi / 2) := (Real.cos_sub_pi_div_two y).symm
  rw [h1, h2]
  exact Real.strictAntiOn_cos ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
    ⟨by linarith [hy.1], by linarith [hy.2, Real.pi_pos]⟩ (by linarith)

/-- Bounds for `cos` on an interval between two Pythagorean angles. -/
theorem cos_bounds_ang {t1 t2 u : ℝ} (h1 : 0 < t1) (h12 : t1 ≤ t2)
    (hu1 : ang t1 ≤ u) (hu2 : u ≤ ang t2) :
    (1 - t2^2) / (1 + t2^2) ≤ Real.cos u ∧ Real.cos u ≤ (1 - t1^2) / (1 + t1^2) := by
  have h2 : 0 < t2 := lt_of_lt_of_le h1 h12
  have hu : u ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_trans (le_of_lt (ang_pos h1)) hu1, le_trans hu2 (le_of_lt (ang_lt_pi h2))⟩
  have ha : ang t1 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt (ang_pos h1), le_of_lt (ang_lt_pi h1)⟩
  have hb : ang t2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt (ang_pos h2), le_of_lt (ang_lt_pi h2)⟩
  constructor
  · rw [← cos_ang t2]
    exact (Real.strictAntiOn_cos.le_iff_ge hb hu).mpr hu2
  · rw [← cos_ang t1]
    exact (Real.strictAntiOn_cos.le_iff_ge hu ha).mpr hu1

/-- Bounds for `sin` on an interval between two Pythagorean angles below `π/2`. -/
theorem sin_bounds_ang_lo {t1 t2 u : ℝ} (h1 : 0 < t1) (h12 : t1 ≤ t2) (h2 : t2 ≤ 1)
    (hu1 : ang t1 ≤ u) (hu2 : u ≤ ang t2) :
    2 * t1 / (1 + t1^2) ≤ Real.sin u ∧ Real.sin u ≤ 2 * t2 / (1 + t2^2) := by
  have h2pos : 0 < t2 := lt_of_lt_of_le h1 h12
  have ht1 : ang t1 ≤ Real.pi / 2 := by
    rcases lt_or_eq_of_le (le_trans h12 h2) with h | h
    · exact le_of_lt (ang_lt_pi_div_two h1 h)
    · rw [h, ang_one]
  have ht2 : ang t2 ≤ Real.pi / 2 := by
    rcases lt_or_eq_of_le h2 with h | h
    · exact le_of_lt (ang_lt_pi_div_two h2pos h)
    · rw [h, ang_one]
  have ha : ang t1 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [ang_pos h1], ht1⟩
  have hb : ang t2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [ang_pos h2pos], ht2⟩
  have hu : u ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨le_trans (by linarith [ang_pos h1]) hu1, le_trans hu2 ht2⟩
  constructor
  · rw [← sin_ang t1]
    exact (Real.strictMonoOn_sin.le_iff_le ha hu).mpr hu1
  · rw [← sin_ang t2]
    exact (Real.strictMonoOn_sin.le_iff_le hu hb).mpr hu2

/-- Bounds for `sin` on an interval between two Pythagorean angles above `π/2`. -/
theorem sin_bounds_ang_hi {t1 t2 u : ℝ} (h1 : 1 ≤ t1) (h12 : t1 ≤ t2)
    (hu1 : ang t1 ≤ u) (hu2 : u ≤ ang t2) :
    2 * t2 / (1 + t2^2) ≤ Real.sin u ∧ Real.sin u ≤ 2 * t1 / (1 + t1^2) := by
  have h1pos : 0 < t1 := lt_of_lt_of_le zero_lt_one h1
  have h2pos : 0 < t2 := lt_of_lt_of_le h1pos h12
  have ht1 : Real.pi / 2 ≤ ang t1 := by
    rw [← ang_one]; exact ang_le_ang h1
  have ha : ang t1 ∈ Set.Icc (Real.pi/2) Real.pi := ⟨ht1, le_of_lt (ang_lt_pi h1pos)⟩
  have hb : ang t2 ∈ Set.Icc (Real.pi/2) Real.pi :=
    ⟨le_trans ht1 (ang_le_ang h12), le_of_lt (ang_lt_pi h2pos)⟩
  have hu : u ∈ Set.Icc (Real.pi/2) Real.pi :=
    ⟨le_trans ht1 hu1, le_trans hu2 hb.2⟩
  constructor
  · rw [← sin_ang t2]
    exact (strictAntiOn_sin_Icc.le_iff_ge hb hu).mpr hu2
  · rw [← sin_ang t1]
    exact (strictAntiOn_sin_Icc.le_iff_ge hu ha).mpr hu1

/-- Bounds for `sin` on an interval between two Pythagorean angles straddling `π/2`. -/
theorem sin_bounds_ang_mid {t1 t2 u : ℝ} (h1 : 0 < t1) (h12 : t1 ≤ t2) (h1' : t1 ≤ 1)
    (h2' : 1 ≤ t2) (hu1 : ang t1 ≤ u) (hu2 : u ≤ ang t2) :
    min (2 * t1 / (1 + t1^2)) (2 * t2 / (1 + t2^2)) ≤ Real.sin u ∧ Real.sin u ≤ 1 := by
  have h2pos : 0 < t2 := lt_of_lt_of_le h1 h12
  have hpi1 : ang t1 ≤ Real.pi / 2 := by
    rcases lt_or_eq_of_le h1' with h | h
    · exact le_of_lt (ang_lt_pi_div_two h1 h)
    · rw [h, ang_one]
  have hpi2 : Real.pi / 2 ≤ ang t2 := by
    rcases lt_or_eq_of_le h2' with h | h
    · exact le_of_lt (ang_pi_div_two_lt h)
    · rw [← h, ang_one]
  rcases le_or_gt u (Real.pi/2) with hu | hu
  · have ha : ang t1 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := ⟨by linarith [ang_pos h1], hpi1⟩
    have hmemu : u ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := ⟨by linarith [ang_pos h1], hu⟩
    have hs : Real.sin (ang t1) ≤ Real.sin u :=
      (Real.strictMonoOn_sin.le_iff_le ha hmemu).mpr hu1
    rw [sin_ang] at hs
    exact ⟨le_trans (min_le_left _ _) hs, Real.sin_le_one u⟩
  · have hb : ang t2 ∈ Set.Icc (Real.pi/2) Real.pi := ⟨hpi2, le_of_lt (ang_lt_pi h2pos)⟩
    have hmemu : u ∈ Set.Icc (Real.pi/2) Real.pi :=
      ⟨le_of_lt hu, le_trans hu2 (le_of_lt (ang_lt_pi h2pos))⟩
    have hs : Real.sin (ang t2) ≤ Real.sin u :=
      (strictAntiOn_sin_Icc.le_iff_ge hb hmemu).mpr hu2
    rw [sin_ang] at hs
    exact ⟨le_trans (min_le_right _ _) hs, Real.sin_le_one u⟩

/-! ## Trigonometric bounds on intervals in the lower half -/

theorem cos_bounds_ang_low {t1 t2 u : ℝ} (h1 : 0 < t1) (h12 : t1 ≤ t2)
    (hu1 : 2 * Real.pi - ang t2 ≤ u) (hu2 : u ≤ 2 * Real.pi - ang t1) :
    (1 - t2^2) / (1 + t2^2) ≤ Real.cos u ∧ Real.cos u ≤ (1 - t1^2) / (1 + t1^2) := by
  have h2 : 0 < t2 := lt_of_lt_of_le h1 h12
  have hv1 : ang t1 ≤ 2 * Real.pi - u := by linarith
  have hv2 : 2 * Real.pi - u ≤ ang t2 := by linarith
  have h := cos_bounds_ang h1 h12 hv1 hv2
  rwa [Real.cos_two_pi_sub] at h

theorem sin_bounds_ang_low_lo {t1 t2 u : ℝ} (h1 : 0 < t1) (h12 : t1 ≤ t2) (h2 : t2 ≤ 1)
    (hu1 : 2 * Real.pi - ang t2 ≤ u) (hu2 : u ≤ 2 * Real.pi - ang t1) :
    -(2 * t2 / (1 + t2^2)) ≤ Real.sin u ∧ Real.sin u ≤ -(2 * t1 / (1 + t1^2)) := by
  have hv1 : ang t1 ≤ 2 * Real.pi - u := by linarith
  have hv2 : 2 * Real.pi - u ≤ ang t2 := by linarith
  have h := sin_bounds_ang_lo h1 h12 h2 hv1 hv2
  rw [Real.sin_two_pi_sub] at h
  constructor <;> linarith [h.1, h.2]

theorem sin_bounds_ang_low_hi {t1 t2 u : ℝ} (h1 : 1 ≤ t1) (h12 : t1 ≤ t2)
    (hu1 : 2 * Real.pi - ang t2 ≤ u) (hu2 : u ≤ 2 * Real.pi - ang t1) :
    -(2 * t2 / (1 + t2^2)) ≤ Real.sin u ∧ Real.sin u ≤ -(2 * t2 / (1 + t2^2)) ∨
      (-(2 * t1 / (1 + t1^2)) ≤ Real.sin u ∧ Real.sin u ≤ -(2 * t2 / (1 + t2^2))) := by
  have hv1 : ang t1 ≤ 2 * Real.pi - u := by linarith
  have hv2 : 2 * Real.pi - u ≤ ang t2 := by linarith
  have h := sin_bounds_ang_hi h1 h12 hv1 hv2
  rw [Real.sin_two_pi_sub] at h
  exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem sin_bounds_ang_low_mid {t1 t2 u : ℝ} (h1 : 0 < t1) (h12 : t1 ≤ t2) (h1' : t1 ≤ 1)
    (h2' : 1 ≤ t2) (hu1 : 2 * Real.pi - ang t2 ≤ u) (hu2 : u ≤ 2 * Real.pi - ang t1) :
    -1 ≤ Real.sin u ∧ Real.sin u ≤ - min (2 * t1 / (1 + t1^2)) (2 * t2 / (1 + t2^2)) := by
  have hv1 : ang t1 ≤ 2 * Real.pi - u := by linarith
  have hv2 : 2 * Real.pi - u ≤ ang t2 := by linarith
  have h := sin_bounds_ang_mid h1 h12 h1' h2' hv1 hv2
  rw [Real.sin_two_pi_sub] at h
  exact ⟨by linarith [Real.neg_one_le_sin (2*Real.pi - u)], by linarith [h.1]⟩

/-! ## The window conditions along the two branches -/

/-- `(7/5) * 2^{1/3}`, the half-length of the box in the `y` direction. -/
noncomputable def yclip : ℝ := (7/5) * (2 : ℝ) ^ (1 / 3 : ℝ)

/-- The `z`-window along the `B` branch. -/
def psiB (u : ℝ) : ℝ := 3 * |trN2 u| - (7/5) * (2 * (97/100) + trS u)

/-- The `y`-window along the `A` branch. -/
noncomputable def psiA1 (u : ℝ) : ℝ := 3 * |trN1 u| - yclip * (2 * (97/100) - trS u)

/-- The `z`-window along the `A` branch. -/
def psiA2 (u : ℝ) : ℝ := 3 * |trN2 u| - (7/5) * (2 * (97/100) - trS u)

theorem gammaB_coord_two_eq (u : ℝ) :
    (gammaB u) 2 = 3 * trN2 u / (2 * (97/100) + trS u) := by
  rw [eq_div_iff (ne_of_gt (tr_two_c_add_pos u))]
  exact gammaB_coord_two u

theorem gammaB_coord_one_eq (u : ℝ) :
    (gammaB u) 1 = 3 * trN1 u / (2 * (97/100) + trS u) := by
  rw [eq_div_iff (ne_of_gt (tr_two_c_add_pos u))]
  exact gammaB_coord_one u

theorem gammaA_coord_two_eq (u : ℝ) :
    (gammaA u) 2 = 3 * trN2 u / (2 * (97/100) - trS u) := by
  rw [eq_div_iff (ne_of_gt (tr_two_c_sub_pos u))]
  exact gammaA_coord_two u

theorem gammaA_coord_one_eq (u : ℝ) :
    (gammaA u) 1 = 3 * trN1 u / (2 * (97/100) - trS u) := by
  rw [eq_div_iff (ne_of_gt (tr_two_c_sub_pos u))]
  exact gammaA_coord_one u

theorem psiB_iff (u : ℝ) : psiB u ≤ 0 ↔ |(gammaB u) 2| ≤ 7/5 := by
  have h := tr_two_c_add_pos u
  rw [psiB, gammaB_coord_two_eq u, abs_div, abs_of_pos h, div_le_iff₀ h, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro hh <;> linarith

theorem psiA1_iff (u : ℝ) : psiA1 u ≤ 0 ↔ |(gammaA u) 1| ≤ yclip := by
  have h := tr_two_c_sub_pos u
  rw [psiA1, gammaA_coord_one_eq u, abs_div, abs_of_pos h, div_le_iff₀ h, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro hh <;> linarith

theorem psiA2_iff (u : ℝ) : psiA2 u ≤ 0 ↔ |(gammaA u) 2| ≤ 7/5 := by
  have h := tr_two_c_sub_pos u
  rw [psiA2, gammaA_coord_two_eq u, abs_div, abs_of_pos h, div_le_iff₀ h, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro hh <;> linarith

theorem psiB_lt_iff (u : ℝ) : psiB u < 0 ↔ |(gammaB u) 2| < 7/5 := by
  have h := tr_two_c_add_pos u
  rw [psiB, gammaB_coord_two_eq u, abs_div, abs_of_pos h, div_lt_iff₀ h, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro hh <;> linarith

theorem psiA1_lt_iff (u : ℝ) : psiA1 u < 0 ↔ |(gammaA u) 1| < yclip := by
  have h := tr_two_c_sub_pos u
  rw [psiA1, gammaA_coord_one_eq u, abs_div, abs_of_pos h, div_lt_iff₀ h, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro hh <;> linarith

theorem psiA2_lt_iff (u : ℝ) : psiA2 u < 0 ↔ |(gammaA u) 2| < 7/5 := by
  have h := tr_two_c_sub_pos u
  rw [psiA2, gammaA_coord_two_eq u, abs_div, abs_of_pos h, div_lt_iff₀ h, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  constructor <;> intro hh <;> linarith

/-- A rational lower bound for `2^{1/3}`. -/
theorem rpow_third_ge : (1259/1000 : ℝ) ≤ (2:ℝ)^(1/3:ℝ) := by
  have h3 : ((1259/1000 : ℝ) ^ ((3:ℕ):ℝ)) ≤ 2 := by
    rw [Real.rpow_natCast]; norm_num
  have h := (Real.rpow_le_rpow_iff (by positivity) (by norm_num : (0:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) < (1/3:ℝ))).mpr h3
  have h2 : (((1259/1000 : ℝ) ^ ((3:ℕ):ℝ)))^(1/3:ℝ) = 1259/1000 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (1259/1000:ℝ))]
    norm_num
  rwa [h2] at h

theorem yclip_lower : (1762/1000 : ℝ) < yclip := by
  rw [yclip]
  nlinarith [rpow_third_ge]

/-- The `y`-window along the `B` branch is never the obstruction. -/
theorem branchB_y_bound (u : ℝ) : |(gammaB u) 1| < yclip := by
  have hpos := tr_two_c_add_pos u
  have hA : |trN1 u| ≤ 1252/1000 := by
    have hsq : trN1 u ^ 2 ≤ (156547717 : ℝ) / 10^8 := by
      have hc := Real.cos_sq_add_sin_sq u
      simp only [trN1, trB1, trA]
      nlinarith [hc, sq_nonneg ((7761/10000) * Real.sin u - (4907/5000) * Real.cos u)]
    have hsq2 : trN1 u ^ 2 ≤ (1252/1000 : ℝ)^2 := by
      have : (156547717 : ℝ) / 10^8 ≤ (1252/1000 : ℝ)^2 := by norm_num
      linarith
    calc |trN1 u| = Real.sqrt (trN1 u ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((1252/1000 : ℝ)^2) := Real.sqrt_le_sqrt hsq2
      _ = 1252/1000 := Real.sqrt_sq (by norm_num)
  have hS : (682/1000 : ℝ) ≤ trS u := by
    rw [trS, Real.le_sqrt (by norm_num) (le_of_lt (trS_arg_pos u))]
    have := trA_sq_le u
    nlinarith
  have hden2 : (2622/1000 : ℝ) ≤ 2 * (97/100) + trS u := by linarith
  rw [gammaB_coord_one_eq u, abs_div, abs_of_pos hpos,
    abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hbound : 3 * |trN1 u| / (2 * (97/100) + trS u) ≤ 3 * (1252/1000) / (2622/1000) :=
    div_le_div₀ (by positivity) (by linarith [hA]) (by norm_num) hden2
  have h3 : 3 * (1252/1000 : ℝ) / (2622/1000) < yclip := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2622/1000)]
    nlinarith [yclip_lower]
  linarith [hbound, h3]

/-! ## The parameters at which the trace leaves the box -/

/-- The first parameter at which the `B` branch leaves the box (through a `z`-face). -/
noncomputable def uB1 : ℝ := sInf {u : ℝ | u ∈ Set.Icc 0 (ang (7/10)) ∧ psiB u = 0}

/-- The second parameter at which the `B` branch leaves the box. -/
noncomputable def uB2 : ℝ := sInf {u : ℝ | u ∈ Set.Icc (ang (9/10)) (ang 5) ∧ psiB u = 0}

/-- The third parameter at which the `B` branch leaves the box. -/
noncomputable def uB3 : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)) ∧ psiB u = 0}

/-- The fourth parameter at which the `B` branch leaves the box. -/
noncomputable def uB4 : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)) ∧ psiB u = 0}

/-- The first parameter at which the `A` branch meets the `y`-face of the box. -/
noncomputable def yA1 : ℝ := sInf {u : ℝ | u ∈ Set.Icc (ang (7/10)) (ang (5/2)) ∧ psiA1 u = 0}

/-- The second parameter at which the `A` branch meets the `y`-face of the box. -/
noncomputable def yA2 : ℝ := sInf {u : ℝ | u ∈ Set.Icc (ang (9/2)) (ang 14) ∧ psiA1 u = 0}

/-- The third parameter at which the `A` branch meets the `y`-face of the box. -/
noncomputable def yA3 : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (3/2)) (2 * Real.pi - ang (2/5)) ∧ psiA1 u = 0}

/-- The fourth parameter at which the `A` branch meets the `y`-face of the box. -/
noncomputable def yA4 : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (1/5)) (2 * Real.pi - ang (1/15)) ∧ psiA1 u = 0}

/-- The first parameter at which the `A` branch meets the `z`-face of the box. -/
noncomputable def zA1 : ℝ := sInf {u : ℝ | u ∈ Set.Icc (ang (5/2)) (ang (9/2)) ∧ psiA2 u = 0}

/-- The second parameter at which the `A` branch meets the `z`-face of the box. -/
noncomputable def zA2 : ℝ := sInf {u : ℝ | u ∈ Set.Icc (ang 14) (ang 400) ∧ psiA2 u = 0}

/-- The third parameter at which the `A` branch meets the `z`-face of the box. -/
noncomputable def zA3 : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (2/5)) (2 * Real.pi - ang (1/5)) ∧ psiA2 u = 0}

/-- The fourth parameter at which the `A` branch meets the `z`-face of the box. -/
noncomputable def zA4 : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (1/15)) (2 * Real.pi - ang (1/1000)) ∧ psiA2 u = 0}

end

end Work.BoxShrink.PinchOff.RefuteDrop
