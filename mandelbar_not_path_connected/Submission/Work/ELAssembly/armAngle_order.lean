import Mathlib
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.armChain_nest
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-!
# The order of the arm angles of the `b₂`-nest

Every level-`n` arm angle of the certificate is affine in the geometric factor
`y n = 64⁻ⁿ ∈ (0, 1]`: the six closed forms are `Work.ELNest.armA1_closed`, …, `armC2_closed`
(`Submission/Work/ELNest/armChain_nest.lean`):

    armA1 n = 22/63 + (289/21483)  * y n     armA2 n = 25/63 - (41/21483)  * y n
    armB1 n = 25/63 + (1156/21483) * y n     armB2 n = 37/63 - (164/21483) * y n
    armC1 n = 37/63 + (4624/21483) * y n     armC2 n = 22/63 - (656/21483) * y n

with `y n` strictly decreasing and `0 < y n ≤ 1`.  Hence the two `+`-families (`A₁`, `B₁`, `C₁`)
decrease toward their arm endpoint, the three `-`-families (`A₂`, `B₂`, `C₂`) increase toward
their arm endpoint, and the bounds in `armAngle_order` follow by comparing with `y n = 0` and
`y n = 1`.  The endpoint values `22/63`, `25/63`, `37/63`, `1`, `0` and the root angles
`α₁ = 371/1023 = 22/63 + 289/21483`, `α₂ = 404/1023 = 25/63 - 41/21483` are the corresponding
comparison points.
-/

/-! ## Arithmetic of the geometric factor `y n = 64⁻ⁿ` -/

/-- `64⁻ⁿ` is positive. -/
private lemma y64_pos (n : ℕ) : (0 : ℝ) < ((64 : ℝ) ^ n)⁻¹ := by positivity

/-- `64⁻ⁿ ≤ 1`. -/
private lemma y64_le_one (n : ℕ) : ((64 : ℝ) ^ n)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- For `d > 0` the product `d · 64⁻ⁿ` is strictly decreasing in `n`. -/
private lemma mul_y64_anti (d : ℝ) (hd : 0 < d) (n : ℕ) :
    d * ((64 : ℝ) ^ (n + 1))⁻¹ < d * ((64 : ℝ) ^ n)⁻¹ := by
  rw [Work.ELNest.inv_pow_succ_64]
  exact mul_lt_mul_of_pos_left (div_lt_self (y64_pos n) (by norm_num)) hd

/-- For `0 ≤ d` one has `d · 64⁻ⁿ ≤ d`. -/
private lemma mul_y64_le (d : ℝ) (hd : 0 ≤ d) (n : ℕ) :
    d * ((64 : ℝ) ^ n)⁻¹ ≤ d :=
  mul_le_of_le_one_right hd (y64_le_one n)

/-- For `d > 0` one has `0 < d · 64⁻ⁿ`. -/
private lemma mul_y64_pos (d : ℝ) (hd : 0 < d) (n : ℕ) :
    0 < d * ((64 : ℝ) ^ n)⁻¹ := mul_pos hd (y64_pos n)

theorem armAngle_order :
    (∀ n : ℕ, Work.ELNest.armA1 (n + 1) < Work.ELNest.armA1 n) ∧
    (∀ n : ℕ, Work.ELNest.armA1 n ≤ Work.EL.alpha1) ∧
    (∀ n : ℕ, (22 : ℝ) / 63 ≤ Work.ELNest.armA1 n) ∧
    (∀ n : ℕ, Work.ELNest.armA2 n < Work.ELNest.armA2 (n + 1)) ∧
    (∀ n : ℕ, Work.EL.alpha2 ≤ Work.ELNest.armA2 n) ∧
    (∀ n : ℕ, Work.ELNest.armA2 n < 25 / 63) ∧
    (∀ n : ℕ, Work.ELNest.armB1 (n + 1) < Work.ELNest.armB1 n) ∧
    (∀ n : ℕ, 25 / 63 < Work.ELNest.armB1 n) ∧
    (∀ n : ℕ, Work.ELNest.armB1 n < 37 / 63) ∧
    (∀ n : ℕ, Work.ELNest.armB2 n < Work.ELNest.armB2 (n + 1)) ∧
    (∀ n : ℕ, 25 / 63 < Work.ELNest.armB2 n) ∧
    (∀ n : ℕ, Work.ELNest.armB2 n < 37 / 63) ∧
    (∀ n : ℕ, Work.ELNest.armC1 (n + 1) < Work.ELNest.armC1 n) ∧
    (∀ n : ℕ, 37 / 63 < Work.ELNest.armC1 n) ∧
    (∀ n : ℕ, Work.ELNest.armC1 n < 1) ∧
    (∀ n : ℕ, Work.ELNest.armC2 n < Work.ELNest.armC2 (n + 1)) ∧
    (∀ n : ℕ, 0 < Work.ELNest.armC2 n) ∧
    (∀ n : ℕ, Work.ELNest.armC2 n < 22 / 63) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `armA1` is strictly decreasing
    intro n
    rw [Work.ELNest.armA1_closed (n + 1), Work.ELNest.armA1_closed n]
    linarith [mul_y64_anti (289 / 21483) (by norm_num) n]
  · -- `armA1 n ≤ α₁`
    intro n
    rw [Work.ELNest.armA1_closed n]
    have ha : Work.EL.alpha1 = 22 / 63 + 289 / 21483 := by
      unfold Work.EL.alpha1; norm_num
    rw [ha]
    linarith [mul_y64_le (289 / 21483) (by norm_num) n]
  · -- `22/63 ≤ armA1 n`
    intro n
    rw [Work.ELNest.armA1_closed n]
    linarith [mul_y64_pos (289 / 21483) (by norm_num) n]
  · -- `armA2` is strictly increasing
    intro n
    rw [Work.ELNest.armA2_closed n, Work.ELNest.armA2_closed (n + 1)]
    linarith [mul_y64_anti (41 / 21483) (by norm_num) n]
  · -- `α₂ ≤ armA2 n`
    intro n
    rw [Work.ELNest.armA2_closed n]
    have ha : Work.EL.alpha2 = 25 / 63 - 41 / 21483 := by
      unfold Work.EL.alpha2; norm_num
    rw [ha]
    linarith [mul_y64_le (41 / 21483) (by norm_num) n]
  · -- `armA2 n < 25/63`
    intro n
    rw [Work.ELNest.armA2_closed n]
    linarith [mul_y64_pos (41 / 21483) (by norm_num) n]
  · -- `armB1` is strictly decreasing
    intro n
    rw [Work.ELNest.armB1_closed (n + 1), Work.ELNest.armB1_closed n]
    linarith [mul_y64_anti (1156 / 21483) (by norm_num) n]
  · -- `25/63 < armB1 n`
    intro n
    rw [Work.ELNest.armB1_closed n]
    linarith [mul_y64_pos (1156 / 21483) (by norm_num) n]
  · -- `armB1 n < 37/63`
    intro n
    rw [Work.ELNest.armB1_closed n]
    have h := mul_y64_le (1156 / 21483) (by norm_num) n
    have : (25 : ℝ) / 63 + 1156 / 21483 < 37 / 63 := by norm_num
    linarith
  · -- `armB2` is strictly increasing
    intro n
    rw [Work.ELNest.armB2_closed n, Work.ELNest.armB2_closed (n + 1)]
    linarith [mul_y64_anti (164 / 21483) (by norm_num) n]
  · -- `25/63 < armB2 n`
    intro n
    rw [Work.ELNest.armB2_closed n]
    have h := mul_y64_le (164 / 21483) (by norm_num) n
    have : (25 : ℝ) / 63 < 37 / 63 - 164 / 21483 := by norm_num
    linarith
  · -- `armB2 n < 37/63`
    intro n
    rw [Work.ELNest.armB2_closed n]
    linarith [mul_y64_pos (164 / 21483) (by norm_num) n]
  · -- `armC1` is strictly decreasing
    intro n
    rw [Work.ELNest.armC1_closed (n + 1), Work.ELNest.armC1_closed n]
    linarith [mul_y64_anti (4624 / 21483) (by norm_num) n]
  · -- `37/63 < armC1 n`
    intro n
    rw [Work.ELNest.armC1_closed n]
    linarith [mul_y64_pos (4624 / 21483) (by norm_num) n]
  · -- `armC1 n < 1`
    intro n
    rw [Work.ELNest.armC1_closed n]
    have h := mul_y64_le (4624 / 21483) (by norm_num) n
    have : (37 : ℝ) / 63 + 4624 / 21483 < 1 := by norm_num
    linarith
  · -- `armC2` is strictly increasing
    intro n
    rw [Work.ELNest.armC2_closed n, Work.ELNest.armC2_closed (n + 1)]
    linarith [mul_y64_anti (656 / 21483) (by norm_num) n]
  · -- `0 < armC2 n`
    intro n
    rw [Work.ELNest.armC2_closed n]
    have h := mul_y64_le (656 / 21483) (by norm_num) n
    have : (0 : ℝ) < 22 / 63 - 656 / 21483 := by norm_num
    linarith
  · -- `armC2 n < 22/63`
    intro n
    rw [Work.ELNest.armC2_closed n]
    linarith [mul_y64_pos (656 / 21483) (by norm_num) n]

end Work.ELAssembly
