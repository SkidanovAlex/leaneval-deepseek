import Mathlib
import Submission.Work.ELPull.Cert.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELPull

open Work.ELPull.Cert

/-! ## Helper lemmas for the angle arithmetic of the arm rotation

The certificate data `levelPair n Z` is the far arc of the arm `Z` contracted towards the arm
endpoints by the factor `64^n`.  Since `Tq^[4] q = fract (16 q)` and `16·((64^n)⁻¹) ≤ 1/4`
for `n ≥ 1`, the perturbation caused by the contraction stays far below the threshold needed
for the image to remain inside the rotated arm. -/

/-- The `(n+1)`-st iterate of the angle-doubling map on `ℚ` is the fractional part of
`(-2)^(n+1) q`. -/
private theorem Tq_iterate_eq_fract (n : ℕ) (q : ℚ) :
    Tq^[n+1] q = Int.fract (((-2 : ℚ) ^ (n+1)) * q) := by
  induction n with
  | zero => simp [Tq]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Tq]
    have key : Int.fract (-2 * Int.fract (((-2 : ℚ) ^ (n+1)) * q))
        = Int.fract (-2 * (((-2 : ℚ) ^ (n+1)) * q)) := by
      rw [Int.fract_eq_fract]
      refine ⟨2 * ⌊((-2 : ℚ) ^ (n+1)) * q⌋, ?_⟩
      rw [← Int.self_sub_floor (((-2 : ℚ) ^ (n+1)) * q)]
      push_cast
      ring
    rw [key]
    congr 1
    rw [pow_succ]
    ring

/-- The fourth iterate of the angle-doubling map on `ℚ` is `q ↦ fract (16 q)`. -/
private theorem Tq_four (q : ℚ) : Tq^[4] q = Int.fract (16 * q) := by
  have h : Tq^[3+1] q = Int.fract (((-2 : ℚ) ^ (3+1)) * q) := Tq_iterate_eq_fract 3 q
  norm_num at h
  exact h

/-- `Tq^[4] x` evaluated by exhibiting a representative `v ∈ [0,1)` of `16 x` modulo `1`. -/
private theorem Tq_four_eq_of {x v : ℚ} (h0 : 0 ≤ v) (h1 : v < 1)
    (h : ∃ m : ℤ, 16 * x - v = (m : ℚ)) : Tq^[4] x = v := by
  rw [Tq_four, Int.fract_eq_iff]
  exact ⟨h0, h1, h⟩

/-- `16 / 64^n ≤ 1/4` for `n ≥ 1`. -/
private theorem div64_16_le (n : ℕ) (hn : 1 ≤ n) : (16 : ℚ) / 64 ^ n ≤ 1 / 4 := by
  have h64 : (64 : ℚ) ≤ 64 ^ n := by
    calc (64 : ℚ) = 64 ^ 1 := by norm_num
      _ ≤ 64 ^ n := pow_le_pow_right₀ (by norm_num) hn
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < 64 ^ n)]
  linarith

/-- `δ · (16/64^n) ≤ δ/4` for `δ ≥ 0` and `n ≥ 1`. -/
private theorem pert_le (δ : ℚ) (hδ : 0 ≤ δ) (n : ℕ) (hn : 1 ≤ n) :
    δ * ((16 : ℚ) / 64 ^ n) ≤ δ / 4 := by
  calc δ * ((16 : ℚ) / 64 ^ n) ≤ δ * (1 / 4) :=
        mul_le_mul_of_nonneg_left (div64_16_le n hn) hδ
    _ = δ / 4 := by ring

/-- `δ · (16/64^n) ≥ δ/4` for `δ ≤ 0` and `n ≥ 1`. -/
private theorem pert_ge (δ : ℚ) (hδ : δ ≤ 0) (n : ℕ) (hn : 1 ≤ n) :
    δ / 4 ≤ δ * ((16 : ℚ) / 64 ^ n) := by
  have := mul_le_mul_of_nonpos_right (div64_16_le n hn) hδ
  linarith [this]

theorem armRot_level (Z : Fin 3) (n : ℕ) (hn : 1 ≤ n) :
    InArcQ (Tq^[4] (Cert.levelPair n Z).1) (Cert.arm (Cert.armRot Z)).1 (Cert.arm (Cert.armRot Z)).2 ∧
    InArcQ (Tq^[4] (Cert.levelPair n Z).2) (Cert.arm (Cert.armRot Z)).1 (Cert.arm (Cert.armRot Z)).2 := by
  have hZ : Z = 0 ∨ Z = 1 ∨ Z = 2 := by fin_cases Z <;> simp
  rcases hZ with h | h | h
  · -- `Z = 0`: the arm `A = (22/63, 25/63)` rotates to the arm `C = (37/63, 85/63)`.
    rw [h]
    have hδ2 : (404 / 1023 - 25 / 63 : ℚ) ≤ 0 := by norm_num
    set E1 : ℚ := (371 / 1023 - 22 / 63) * ((16 : ℚ) / 64 ^ n) with hE1def
    set E2 : ℚ := (404 / 1023 - 25 / 63) * ((16 : ℚ) / 64 ^ n) with hE2def
    have hE1le : E1 ≤ (867 / 64449) / 4 := by
      rw [hE1def]
      have heq : (371 / 1023 - 22 / 63 : ℚ) = 867 / 64449 := by norm_num
      rw [heq]
      exact pert_le (867 / 64449) (by norm_num) n hn
    have hE2ge : (-123 / 64449) / 4 ≤ E2 := by
      rw [hE2def]
      have h := pert_ge (404 / 1023 - 25 / 63 : ℚ) hδ2 n hn
      have heq : (404 / 1023 - 25 / 63 : ℚ) / 4 = (-123 / 64449) / 4 := by norm_num
      rw [heq] at h
      exact h
    have hE1pos : 0 < E1 := by
      rw [hE1def]; exact mul_pos (by norm_num) (by positivity)
    have hE2neg : E2 < 0 := by
      rw [hE2def]; exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)
    have hval1 : Tq^[4] (levelPair n 0).1 = 37 / 63 + E1 := by
      refine Tq_four_eq_of (by linarith) (by linarith) ?_
      refine ⟨5, ?_⟩
      simp only [arm_val_0, farArc_val_0]
      rw [hE1def]; push_cast; ring
    have hval2 : Tq^[4] (levelPair n 0).2 = 22 / 63 + E2 := by
      refine Tq_four_eq_of (by linarith) (by linarith) ?_
      refine ⟨6, ?_⟩
      simp only [arm_val_0, farArc_val_0]
      rw [hE2def]; push_cast; ring
    constructor
    · rw [hval1]
      simp only [qq, armRot_val_0, arm_val_2]
      rw [InArcQ_iff_of (by norm_num) (by norm_num) (by linarith) (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · rw [hval2]
      simp only [qq, armRot_val_0, arm_val_2]
      rw [InArcQ_iff_of_lt (by norm_num) (by norm_num) (by linarith) (by linarith)]
      linarith
  · -- `Z = 1`: the arm `B = (25/63, 37/63)` rotates to the arm `A = (22/63, 25/63)`.
    rw [h]
    have hδ2 : (593 / 1023 - 37 / 63 : ℚ) ≤ 0 := by norm_num
    set E1 : ℚ := (461 / 1023 - 25 / 63) * ((16 : ℚ) / 64 ^ n) with hE1def
    set E2 : ℚ := (593 / 1023 - 37 / 63) * ((16 : ℚ) / 64 ^ n) with hE2def
    have hE1le : E1 ≤ (867 / 64449) := by
      rw [hE1def]
      have heq : (461 / 1023 - 25 / 63 : ℚ) = 4 * (867 / 64449) := by norm_num
      rw [heq]
      calc 4 * (867 / 64449) * ((16 : ℚ) / 64 ^ n)
          ≤ 4 * (867 / 64449) * (1 / 4) :=
            mul_le_mul_of_nonneg_left (div64_16_le n hn) (by norm_num)
        _ = 867 / 64449 := by ring
    have hE2ge : (-123 / 64449) ≤ E2 := by
      rw [hE2def]
      have h := pert_ge (593 / 1023 - 37 / 63 : ℚ) hδ2 n hn
      have heq : (593 / 1023 - 37 / 63 : ℚ) / 4 = (-123 / 64449) := by norm_num
      rw [heq] at h
      exact h
    have hE1pos : 0 < E1 := by
      rw [hE1def]; exact mul_pos (by norm_num) (by positivity)
    have hE2neg : E2 < 0 := by
      rw [hE2def]; exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)
    have hval1 : Tq^[4] (levelPair n 1).1 = 22 / 63 + E1 := by
      refine Tq_four_eq_of (by linarith) (by linarith) ?_
      refine ⟨6, ?_⟩
      simp only [arm_val_1, farArc_val_1]
      rw [hE1def]; push_cast; ring
    have hval2 : Tq^[4] (levelPair n 1).2 = 25 / 63 + E2 := by
      refine Tq_four_eq_of (by linarith) (by linarith) ?_
      refine ⟨9, ?_⟩
      simp only [arm_val_1, farArc_val_1]
      rw [hE2def]; push_cast; ring
    constructor
    · rw [hval1]
      simp only [qq, armRot_val_1, arm_val_0]
      rw [InArcQ_iff_of (by norm_num) (by norm_num) (by linarith) (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · rw [hval2]
      simp only [qq, armRot_val_1, arm_val_0]
      rw [InArcQ_iff_of (by norm_num) (by norm_num) (by linarith) (by linarith)]
      exact ⟨by linarith, by linarith⟩
  · -- `Z = 2`: the arm `C = (37/63, 85/63)` rotates to the arm `B = (25/63, 37/63)`.
    rw [h]
    have hδ2 : (1349 / 1023 - 85 / 63 : ℚ) ≤ 0 := by norm_num
    set E1 : ℚ := (821 / 1023 - 37 / 63) * ((16 : ℚ) / 64 ^ n) with hE1def
    set E2 : ℚ := (1349 / 1023 - 85 / 63) * ((16 : ℚ) / 64 ^ n) with hE2def
    have hE1le : E1 ≤ (1156 / 21483) := by
      rw [hE1def]
      have heq : (821 / 1023 - 37 / 63 : ℚ) = 4 * (1156 / 21483) := by norm_num
      rw [heq]
      calc 4 * (1156 / 21483) * ((16 : ℚ) / 64 ^ n)
          ≤ 4 * (1156 / 21483) * (1 / 4) :=
            mul_le_mul_of_nonneg_left (div64_16_le n hn) (by norm_num)
        _ = 1156 / 21483 := by ring
    have hE2ge : (-492 / 64449) ≤ E2 := by
      rw [hE2def]
      have h := pert_ge (1349 / 1023 - 85 / 63 : ℚ) hδ2 n hn
      have heq : (1349 / 1023 - 85 / 63 : ℚ) / 4 = (-492 / 64449) := by norm_num
      rw [heq] at h
      exact h
    have hE1pos : 0 < E1 := by
      rw [hE1def]; exact mul_pos (by norm_num) (by positivity)
    have hE2neg : E2 < 0 := by
      rw [hE2def]; exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)
    have hval1 : Tq^[4] (levelPair n 2).1 = 25 / 63 + E1 := by
      refine Tq_four_eq_of (by linarith) (by linarith) ?_
      refine ⟨9, ?_⟩
      simp only [arm_val_2, farArc_val_2]
      rw [hE1def]; push_cast; ring
    have hval2 : Tq^[4] (levelPair n 2).2 = 37 / 63 + E2 := by
      refine Tq_four_eq_of (by linarith) (by linarith) ?_
      refine ⟨21, ?_⟩
      simp only [arm_val_2, farArc_val_2]
      rw [hE2def]; push_cast; ring
    constructor
    · rw [hval1]
      simp only [qq, armRot_val_2, arm_val_1]
      rw [InArcQ_iff_of (by norm_num) (by norm_num) (by linarith) (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · rw [hval2]
      simp only [qq, armRot_val_2, arm_val_1]
      rw [InArcQ_iff_of (by norm_num) (by norm_num) (by linarith) (by linarith)]
      exact ⟨by linarith, by linarith⟩

end Work.ELPull
