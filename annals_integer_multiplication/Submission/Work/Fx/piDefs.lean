import Mathlib
import Submission.Work.Fx.FxCommon

/-!
# Fixed-point data for the π word (`Work.Fx.piWord`)

Frozen definitions shared by the π development:

* `qq p = 4 p` — the internal precision exponent; the internal scale is `2^(2*qq p)`,
* `C0c p = 2^(2*qq p + 1)` — the fixed-point representative of `2`,
* `Aseq k = √(2+√(2+⋯))` (mathlib's `sqrtTwoAddSeries 0 k`) — the real model sequence,
* `astep p c = 2^q * ⌊√(2^(2q+1)+c)⌋` — one fixed-point square-root step,
* `aval p k` — the integer iterate (approximates `2^(2q) * Aseq k`),
* `Dval p`, `Nval p`, `uval p` — the final extraction of `u ≈ 2^p π`:
  `Nval p = Dval p * 2^(2p+1) + 2^(q-1)`, `uval p = Nval p / 2^q` (floor),
* `SZ p = 8p + 8` — the uniform bound on `isz` of every intermediate value.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Internal precision exponent. -/
def qq (p : ℕ) : ℕ := 4 * p

/-- The fixed-point representative of `2` at scale `2^(2q)`. -/
def C0c (p : ℕ) : ℤ := 2 ^ (2 * qq p + 1)

/-- Real model sequence: `k` nested square roots starting from `0`. -/
noncomputable def Aseq (k : ℕ) : ℝ := Real.sqrtTwoAddSeries 0 k

/-- One fixed-point square-root step: `c ↦ 2^q * ⌊√(2^(2q+1) + c)⌋`. -/
def astep (p : ℕ) (c : ℤ) : ℤ := 2 ^ qq p * (Nat.sqrt ((C0c p + c).toNat) : ℤ)

/-- The integer iterate approximating `2^(2q) * Aseq k`. -/
def aval (p : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => astep p (aval p k)

/-- `⌊√(2^(2q+1) - aval p p)⌋`. -/
def Dval (p : ℕ) : ℤ := (Nat.sqrt ((C0c p - aval p p).toNat) : ℤ)

/-- Numerator of the final rounding. -/
def Nval (p : ℕ) : ℤ := Dval p * 2 ^ (2 * p + 1) + 2 ^ (qq p - 1)

/-- The final integer approximation of `2^p * π`. -/
def uval (p : ℕ) : ℤ := (Nval p).fdiv (2 ^ qq p)

/-- Uniform size bound for intermediate values. -/
def SZ (p : ℕ) : ℕ := 8 * p + 8

theorem aval_zero (p : ℕ) : aval p 0 = 0 := rfl

theorem aval_succ (p k : ℕ) : aval p (k + 1) = astep p (aval p k) := rfl

theorem sq_nonneg' (p k : ℕ) : 0 ≤ aval p k := by
  induction k with
  | zero => simp [aval]
  | succ k ih =>
    rw [aval_succ, astep]
    exact mul_nonneg (by positivity) (by positivity)

theorem Aseq_zero : Aseq 0 = 0 := by simp [Aseq]

theorem Aseq_succ (k : ℕ) : Aseq (k + 1) = Real.sqrt (2 + Aseq k) := by
  simp [Aseq, Real.sqrtTwoAddSeries]

theorem two_sub_Aseq_pos (k : ℕ) : 0 < 2 - Aseq k := by
  have := Real.sqrtTwoAddSeries_lt_two k
  simp only [Aseq]
  linarith

end Work.Fx
