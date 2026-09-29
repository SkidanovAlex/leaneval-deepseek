import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C17.sigma_lead
import Submission.Work.C17.exp2_mul
import Submission.Work.C17.exp2_inv
import Submission.Work.C17.exp2_dRat
import Submission.Work.C17.lead2_rhoQ
import Submission.Work.C17.lead2_dRat_rhoQ

/-!
# Explicit coordinates of the classes `clsZ k` (`k ≤ 3`) and the determinant `Dd`

`Work.A14D.clsZ k` is the class of `∂_y^k` in the `ℚ(x)`-module `ℚ(x)e₀ ⊕ ℚ(x)e₁`
(`e₀ = f`, `e₁ = f′`, `f″ = −(P′f′ + Rf)/P`), i.e. the image of `(1,0)` under the `k`-fold
iterate of `dZ`, where

`dZ (a,b) = (ρ(a′ − b R/P), ρ(a + b′ − b P′/P))`,  `ρ = 1/y′ = (x−1)²/(x²−2x)`,

`P = x(1−x)(1−9x)`, `P′ = 1 − 20x + 27x²`, `R = 9x − 3` (Zagier's operator).

This module fixes the explicit coordinates

* `clsZ 0 = (1, 0)`, `clsZ 1 = (0, ρ)`, `clsZ 2 = (u2, v2)`, `clsZ 3 = (u3, v3)`

with `u2, v2, u3, v3` the rational functions of `Submission/Work/C17/lead_defs.lean`, together
with the anti-invariant functions `Z2 = u2 − σu2`, `Z3 = u3 − σu3`, `Y2 = w2 − σw2`,
`Y3 = w3 − σw3` (`σ = Work.C17.sigmaQ`, the deck involution `x ↦ x/(x−1)`, which fixes `y`)
and their determinant `Dd = Z2·Y3 − Z3·Y2`.
-/

namespace Work.A14D

open Polynomial

noncomputable section

/-- First coordinate of `clsZ 2`. -/
def u2 : RatFunc ℚ := -(rhos * (rhos * RZQ / PZQ))

/-- `v2 / rho`, where `v2` is the second coordinate of `clsZ 2`. -/
def w2 : RatFunc ℚ := Submission.CDT.dRat rhos - rhos * PZQ' / PZQ

/-- Second coordinate of `clsZ 2`. -/
def v2 : RatFunc ℚ := rhos * w2

/-- First coordinate of `clsZ 3`. -/
def u3 : RatFunc ℚ := rhos * (Submission.CDT.dRat u2 - v2 * RZQ / PZQ)

/-- `v3 / rho`, where `v3` is the second coordinate of `clsZ 3`. -/
def w3 : RatFunc ℚ := u2 + Submission.CDT.dRat v2 - v2 * PZQ' / PZQ

/-- Second coordinate of `clsZ 3`. -/
def v3 : RatFunc ℚ := rhos * w3

/-- The anti-invariant part `u2 − σu2`. -/
def Z2 : RatFunc ℚ := u2 - Work.C17.sigmaQ u2

/-- The anti-invariant part `u3 − σu3`. -/
def Z3 : RatFunc ℚ := u3 - Work.C17.sigmaQ u3

/-- The anti-invariant part `w2 − σw2`. -/
def Y2 : RatFunc ℚ := w2 - Work.C17.sigmaQ w2

/-- The anti-invariant part `w3 − σw3`. -/
def Y3 : RatFunc ℚ := w3 - Work.C17.sigmaQ w3

/-- The determinant of the `2 × 2` system for `Q 2, Q 3`. -/
def Dd : RatFunc ℚ := Z2 * Y3 - Z3 * Y2

theorem clsZ_zero_fst : (clsZ 0).1 = 1 := by
  show ((dZ^[((0 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).1 = 1
  rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, Function.iterate_zero_apply]

theorem clsZ_zero_snd : (clsZ 0).2 = 0 := by
  show ((dZ^[((0 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).2 = 0
  rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, Function.iterate_zero_apply]

theorem clsZ_one_fst : (clsZ 1).1 = 0 := by
  show ((dZ^[((1 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).1 = 0
  rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, Function.iterate_one]
  simp [dZ]

theorem clsZ_one_snd : (clsZ 1).2 = rhos := by
  show ((dZ^[((1 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).2 = rhos
  rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, Function.iterate_one]
  simp [dZ]

theorem clsZ_two_fst : (clsZ 2).1 = u2 := by
  show ((dZ^[((2 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).1 = u2
  rw [show ((2 : Fin 4) : ℕ) = 2 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  rw [show dZ ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos) from by simp [dZ]]
  simp only [dZ, u2, w2, v2]
  simp

theorem clsZ_two_snd : (clsZ 2).2 = v2 := by
  show ((dZ^[((2 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).2 = v2
  rw [show ((2 : Fin 4) : ℕ) = 2 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  rw [show dZ ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos) from by simp [dZ]]
  simp only [dZ, u2, w2, v2]
  simp

theorem clsZ_three_fst : (clsZ 3).1 = u3 := by
  show ((dZ^[((3 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).1 = u3
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_one]
  rw [show dZ ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos) from by simp [dZ]]
  rw [show dZ ((0 : RatFunc ℚ), rhos) = (u2, v2) from by
    simp only [dZ, u2, w2, v2]
    simp]
  simp only [dZ, u3, v3, w3]

theorem clsZ_three_snd : (clsZ 3).2 = v3 := by
  show ((dZ^[((3 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ))).2 = v3
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_one]
  rw [show dZ ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos) from by simp [dZ]]
  rw [show dZ ((0 : RatFunc ℚ), rhos) = (u2, v2) from by
    simp only [dZ, u2, w2, v2]
    simp]
  simp only [dZ, u3, v3, w3]

theorem clsZ_zero : clsZ 0 = (1, 0) := rfl

theorem clsZ_one : clsZ 1 = (0, rhos) := by
  show (dZ^[((1 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos)
  rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, Function.iterate_one]
  simp [dZ]

theorem clsZ_two : clsZ 2 = (u2, v2) := by
  show (dZ^[((2 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (u2, v2)
  rw [show ((2 : Fin 4) : ℕ) = 2 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  rw [show dZ ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos) from by simp [dZ]]
  simp only [dZ, u2, w2, v2]
  simp

theorem clsZ_three : clsZ 3 = (u3, v3) := by
  show (dZ^[((3 : Fin 4) : ℕ)]) ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (u3, v3)
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_one]
  rw [show dZ ((1 : RatFunc ℚ), (0 : RatFunc ℚ)) = (0, rhos) from by simp [dZ]]
  rw [show dZ ((0 : RatFunc ℚ), rhos) = (u2, v2) from by
    simp only [dZ, u2, w2, v2]
    simp]
  simp only [dZ, u3, v3, w3]

end

end Work.A14D
