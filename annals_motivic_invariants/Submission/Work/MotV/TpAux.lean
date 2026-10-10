import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, node TP: shared auxiliary definitions

This file holds the two objects used in every statement about node TP
(`Work.MotV.tp`, `Submission/Work/MotV/tp.lean`): the weight

  `wt v h y i = (v h) ^ i * (v (y i)) ^ 5`

of the `i`-th twisted coordinate (Kummer coordinate) of a point `y` of the twisted Klein curve
`kleinTw a b h y = 0`, and the exponent `rr j` with which the `j`-th twisted quadric is scaled in
the fifth-power identities of `tp_ident`.

`rr j` is the representative in `{0,…,4}` of `4 * k (mod 5)` where `k = 3 * j` is the index of the
quadric whose square monomial is `y_j ^ 2`; it is the common residue `i + l (mod 5)` of the three
index pairs `(j, j)`, `(j+2, j+3)`, `(j+1, j+4)` of that quadric.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

/-- The weight `wt v h y i = (v h)^i * (v (y i))^5`. -/
def wt {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
    (h : F) (y : Fin 5 → F) (i : Fin 5) : Γ₀ :=
  (v h) ^ (i : ℕ) * (v (y i)) ^ 5

/-- The twist exponent of the quadric whose square monomial is `y_j ^ 2`: the residue of `4 * k`
modulo `5`, where `2 * k = j` in `Fin 5` (so `k = 3 * j`). -/
def rr (j : Fin 5) : ℕ := ((4 * (3 * j) : Fin 5) : ℕ)

/-- In `Fin 5`, `2 * (3 * j) = j`. -/
lemma two_mul_three_mul (j : Fin 5) : (2 * (3 * j) : Fin 5) = j := by
  fin_cases j <;> rfl

/-- The three index pairs of the quadric `k = 3 * j`, whose square monomial is `y_j ^ 2`. -/
lemma two_mul_three_mul_add (j : Fin 5) :
    (2 * (3 * j) + 2 : Fin 5) = j + 2 ∧ (2 * (3 * j) + 3 : Fin 5) = j + 3 ∧
      ((2 * (3 * j) + 1 : Fin 5) = j + 1 ∧ (2 * (3 * j) + 4 : Fin 5) = j + 4) := by
  fin_cases j <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every element of `Γ₀` is nonnegative. -/
lemma zero_le_wt {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (h : F) (y : Fin 5 → F) (i : Fin 5) : 0 ≤ wt v h y i :=
  zero_le

/-- `wt` is positive iff it is nonzero. -/
lemma wt_pos_iff {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (h : F) (y : Fin 5 → F) (i : Fin 5) :
    0 < wt v h y i ↔ wt v h y i ≠ 0 :=
  zero_lt_iff

/-! ## §2 The two general facts about the ordered value group `Γ₀` -/

/-- A strictly dominant term determines the valuation of the sum: if `t₁` is strictly larger
than both `t₂` and `t₃` then `t₁ + t₂ + t₃ ≠ 0`. -/
lemma sum_ne_zero_of_dominant {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {t₁ t₂ t₃ : F} (h₀ : t₁ + t₂ + t₃ = 0)
    (h₂ : v t₂ < v t₁) (h₃ : v t₃ < v t₁) : False := by
  have h23 : v (t₂ + t₃) < v t₁ :=
    lt_of_le_of_lt (Valuation.map_add_le_max' v t₂ t₃) (max_lt h₂ h₃)
  have h1 : v (t₁ + (t₂ + t₃)) = v t₁ := Valuation.map_add_eq_of_lt_left v h23
  rw [← add_assoc, h₀, Valuation.map_zero] at h1
  exact (ne_of_gt (lt_of_le_of_lt zero_le h₂)) h1.symm

/-- A product of two elements of a linearly ordered commutative group with zero which are `≤ M`
is strictly smaller than `M * M` as soon as one of the two factors is. -/
lemma mul_lt_mul_self {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {M x y : Γ₀}
    (hM : 0 < M) (hx : x ≤ M) (hy : y ≤ M) (h : x < M ∨ y < M) : x * y < M * M := by
  rcases h with h | h
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy zero_le) (mul_lt_mul_of_pos_right h hM)
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hx zero_le) (mul_lt_mul_of_pos_left h hM)

/-- Raising to the fifth power is strictly monotone on `Γ₀`; hence the comparison of two
fifth powers scaled by the same nonzero element `L ^ r` is the comparison of the bases. -/
lemma pow5_mul_lt_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {L : Γ₀}
    (hL : L ≠ 0) (r : ℕ) {x y : Γ₀} : x ^ 5 * L ^ r < y ^ 5 * L ^ r ↔ x < y := by
  have hpos : 0 < L ^ r := pow_pos (zero_lt_iff.mpr hL) r
  rw [mul_lt_mul_iff_left₀ hpos, pow_lt_pow_iff_left₀ (zero_le) (zero_le) (by norm_num)]

end

end Work.MotV
