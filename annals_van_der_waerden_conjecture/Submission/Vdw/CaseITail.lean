import Mathlib
import Submission.Commons.NumberTheory.Nat.omega_color_sum_weighted_le
import Submission.Vdw.SquarefullTail

open scoped BigOperators

set_option autoImplicit false

/-!
# Case I, CI-4: the squarefull tail bound (assembly)

Assembles the CI-4 estimate for the Case-I summation.  The ingredients:

* the discrete transfer (`SquarefullSum.squarefull_tail_cpow_le_pairWeight`):
  a squarefull sum with weight `c^ω(D)/D` is at most the `(a,b)`-parametrized
  pair double sum with the separated weights `c^ω(a)·c^ω(b)/(a²b³)`;
* the indicator decay (`SquarefullTail.pairWeight_tail_le`):
  `1_{Y < a²b³} ≤ (a²b³)^t / Y^t` and the product split;
* the power-weighted ω-coloring bound
  (`Commons.NumberTheory.Nat.omega_color_sum_weighted_le`, local
  `omega_color_pow_le`): for `s ≥ 0`,
  `Σ_{a≤A} c^ω(a)·a^(-s) ≤ (Σ_{k≤A} k^(-s))^c`;
* the polylog bound `SquarefullTail.sum_nat_rpow_neg_le_log`:
  `Σ_{k≤A} k^(-s) ≤ 1 + log A` for `s ≥ 1`.

**Result** (`squarefull_tail_bound`): for `c ≥ 1`, `t ∈ (0, 1/2]`, naturals
`1 ≤ Y < Z`,

`Σ_{Y < D ≤ Z, D squarefull} c^ω(D)/D ≤ (1 + log Z)^(2c) / Y^t`.

Everything in `namespace Submission.Vdw`.
-/

namespace Submission.Vdw

/-- Local form of the commons power-weighted ω-coloring bound (with the local
`omega` definition): `Σ_{a≤A} c^ω(a)·a^(-s) ≤ (Σ_{k≤A} k^(-s))^c`, `s ≥ 0`. -/
lemma omega_color_pow_le (c A : ℕ) (hc : 1 ≤ c) (s : ℝ) (hs : 0 ≤ s) :
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ omega a * (a : ℝ) ^ (-s)) ≤
      (∑ k ∈ Finset.Icc 1 A, (k : ℝ) ^ (-s)) ^ c := by
  simpa [omega] using (Commons.NumberTheory.Nat.omega_color_sum_weighted_le c A hc s hs)

/-- For `1 ≤ a`, `(a²)^t = a^(2t)` (real powers). -/
lemma sq_rpow_eq_rpow_two_mul (a : ℕ) (ha : 1 ≤ a) {t : ℝ} :
    ((a : ℝ) ^ 2) ^ t = (a : ℝ) ^ (2 * t) := by
  have ha0 : 0 ≤ (a : ℝ) := by exact_mod_cast (Nat.zero_le a)
  have hcast : (a : ℝ) ^ (2 : ℕ) = (a : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast (a : ℝ) 2).symm
  calc
    ((a : ℝ) ^ 2) ^ t = ((a : ℝ) ^ (2 : ℝ)) ^ t := by rw [hcast]
    _ = (a : ℝ) ^ (2 * t) := (Real.rpow_mul ha0 2 t).symm

/-- For `1 ≤ a`: `a^(-2) · (a²)^t = a^(2t - 2)`. -/
lemma inv_sq_mul_sq_rpow (a : ℕ) (ha : 1 ≤ a) {t : ℝ} :
    (a : ℝ) ^ (-2 : ℝ) * ((a : ℝ) ^ 2) ^ t = (a : ℝ) ^ (2 * t - 2) := by
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp ha)
  rw [sq_rpow_eq_rpow_two_mul a ha]
  rw [← Real.rpow_add hapos (-2 : ℝ) (2 * t)]
  congr 1
  ring

/-- For `1 ≤ b`: `b^(-3) · (b³)^t = b^(3t - 3)`. -/
lemma inv_cube_mul_cube_rpow (b : ℕ) (hb : 1 ≤ b) {t : ℝ} :
    (b : ℝ) ^ (-3 : ℝ) * ((b : ℝ) ^ 3) ^ t = (b : ℝ) ^ (3 * t - 3) := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hb)
  have hcube : ((b : ℝ) ^ 3) ^ t = (b : ℝ) ^ (3 * t) := by
    have hb0 : 0 ≤ (b : ℝ) := by exact_mod_cast (Nat.zero_le b)
    have hcast : (b : ℝ) ^ (3 : ℕ) = (b : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast (b : ℝ) 3).symm
    calc
      ((b : ℝ) ^ 3) ^ t = ((b : ℝ) ^ (3 : ℝ)) ^ t := by rw [hcast]
      _ = (b : ℝ) ^ (3 * t) := (Real.rpow_mul hb0 3 t).symm
  rw [hcube]
  rw [← Real.rpow_add hbpos (-3 : ℝ) (3 * t)]
  congr 1
  ring

/-- `a^(-2) = 1 / a²` (real powers, `a` natural). -/
lemma rpow_neg_two_eq (a : ℕ) : (a : ℝ) ^ (-2 : ℝ) = 1 / (a : ℝ) ^ 2 := by
  have ha : 0 ≤ (a : ℝ) := by positivity
  calc
    (a : ℝ) ^ (-2 : ℝ) = ((a : ℝ) ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_neg ha]
    _ = ((a : ℝ) ^ 2)⁻¹ := by
      congr 1
      exact Real.rpow_natCast (a : ℝ) 2
    _ = 1 / (a : ℝ) ^ 2 := by rw [inv_eq_one_div]

/-- `b^(-3) = 1 / b³`. -/
lemma rpow_neg_three_eq (b : ℕ) : (b : ℝ) ^ (-3 : ℝ) = 1 / (b : ℝ) ^ 3 := by
  have hb : 0 ≤ (b : ℝ) := by positivity
  calc
    (b : ℝ) ^ (-3 : ℝ) = ((b : ℝ) ^ (3 : ℝ))⁻¹ := by rw [Real.rpow_neg hb]
    _ = ((b : ℝ) ^ 3)⁻¹ := by
      congr 1
      exact Real.rpow_natCast (b : ℝ) 3
    _ = 1 / (b : ℝ) ^ 3 := by rw [inv_eq_one_div]

/-- One coordinate of the separated weight, `Σ_a c^ω(a)·a^(-s)` with `s ≥ 1`,
is at most `(1 + log A)^c`. -/
lemma coord_color_sum_le_log (c A : ℕ) (hc : 1 ≤ c) (s : ℝ) (hs1 : 1 ≤ s) :
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ omega a * (a : ℝ) ^ (-s)) ≤
      (1 + Real.log (A : ℝ)) ^ c := by
  have hs0 : 0 ≤ s := le_trans zero_le_one hs1
  by_cases hA : 1 ≤ A
  · calc
      (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ omega a * (a : ℝ) ^ (-s)) ≤
          (∑ k ∈ Finset.Icc 1 A, (k : ℝ) ^ (-s)) ^ c := omega_color_pow_le c A hc s hs0
      _ ≤ (1 + Real.log (A : ℝ)) ^ c := by
        exact pow_le_pow_left₀
          (Finset.sum_nonneg (by intro k hk; exact Real.rpow_nonneg (by positivity) (-s)))
          (sum_nat_rpow_neg_le_log A hA hs1) c
  · have hA0 : A = 0 := by omega
    subst A
    have hsum : (∑ a ∈ Finset.Icc 1 0, (c : ℝ) ^ omega a * (a : ℝ) ^ (-s)) = 0 := by simp
    rw [hsum]
    positivity

/-- **CI-4 core.**  For `c ≥ 1`, `0 < t ≤ 1/2`, naturals `1 ≤ Y < Z`, the sum
of `c^ω(D)/D` over squarefull `D` with `Y < D ≤ Z` is at most
`(1 + log Z)^(2c) / Y^t`. -/
theorem squarefull_tail_bound (c : ℕ) (hc : 1 ≤ c) (t : ℝ) (ht0 : 0 < t) (ht12 : t ≤ (1 : ℝ) / 2)
    (Y Z : ℕ) (hY : 1 ≤ Y) (hZ : Y < Z) :
    (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) ≤
      ((1 + Real.log (Z : ℝ)) ^ (2 * c)) / (Y : ℝ) ^ t := by
  classical
  let U : ℕ → ℝ := fun a => (c : ℝ) ^ omega a * (a : ℝ) ^ (-2 : ℝ)
  let V : ℕ → ℝ := fun b => (c : ℝ) ^ omega b * (b : ℝ) ^ (-3 : ℝ)
  have hU : ∀ a : ℕ, 0 ≤ U a := by
    intro a
    dsimp [U]
    exact mul_nonneg (pow_nonneg (by exact_mod_cast (Nat.zero_le c)) _)
      (Real.rpow_nonneg (by positivity) (-2 : ℝ))
  have hV : ∀ b : ℕ, 0 ≤ V b := by
    intro b
    dsimp [V]
    exact mul_nonneg (pow_nonneg (by exact_mod_cast (Nat.zero_le c)) _)
      (Real.rpow_nonneg (by positivity) (-3 : ℝ))
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hY)
  -- step 1: squarefull sum ≤ pair double sum (discrete transfer; per-coordinate denominators)
  have h1 := squarefull_tail_cpow_le_pairWeight (c : ℝ) (by exact_mod_cast hc : 1 ≤ (c : ℝ)) Y Z hY
  -- step 2: drop the `≤ Z` conjunct
  have h2 :
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) ≤
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 then
          (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hx : 0 ≤ (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) := by
      have hden : 0 < (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by
        exact mul_pos (pow_pos (by exact_mod_cast (Nat.succ_le_iff.mp ha1)) 2)
          (pow_pos (by exact_mod_cast (Nat.succ_le_iff.mp hb1)) 3)
      exact div_nonneg (mul_nonneg (pow_nonneg (by exact_mod_cast (Nat.zero_le c)) _)
        (pow_nonneg (by exact_mod_cast (Nat.zero_le c)) _)) (le_of_lt hden)
    by_cases hc1 : Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z
    · have hc1' : Y < a ^ 2 * b ^ 3 := hc1.1
      simp [hc1, hc1']
    · by_cases hc2 : Y < a ^ 2 * b ^ 3
      · have hc3 : ¬ a ^ 2 * b ^ 3 ≤ Z := by
          intro hz
          exact hc1 ⟨hc2, hz⟩
        simp [hc1, hc2, hc3, hx]
      · simp [hc1, hc2]
  -- step 3: pointwise re-express as `U a * V b`
  have h3 : (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 then
          (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) =
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 then U a * V b else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hc1 : Y < a ^ 2 * b ^ 3
    · have hterm : (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) =
          U a * V b := by
        dsimp [U, V]
        rw [rpow_neg_two_eq, rpow_neg_three_eq]
        field_simp
      simp [hc1, hterm]
    · simp [hc1]
  -- step 4: apply the indicator decay `pairWeight_tail_le`
  have h4 := pairWeight_tail_le t ht0 Y Z hY U V hU hV
  -- step 5: coordinate sums
  have hs1 : 1 ≤ 2 - 2 * t := by nlinarith [ht12]
  have hs2 : 1 ≤ 3 - 3 * t := by nlinarith [ht12]
  have hAcoord : (∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) ≤ (1 + Real.log (Z : ℝ)) ^ c := by
    have hrew : (∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) =
        (∑ a ∈ Finset.Icc 1 Z, (c : ℝ) ^ omega a * (a : ℝ) ^ (-(2 - 2 * t))) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hstep : U a * ((a : ℝ) ^ 2) ^ t = (c : ℝ) ^ omega a * (a : ℝ) ^ (2 * t - 2) := by
        dsimp [U]
        rw [mul_assoc]
        rw [inv_sq_mul_sq_rpow a ha1]
      have hexp : (a : ℝ) ^ (2 * t - 2) = (a : ℝ) ^ (-(2 - 2 * t)) := by
        congr 1
        ring
      rw [hstep, hexp]
    rw [hrew]
    exact coord_color_sum_le_log c Z hc (2 - 2 * t) hs1
  have hBcoord : (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t) ≤ (1 + Real.log (Z : ℝ)) ^ c := by
    have hrew : (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t) =
        (∑ b ∈ Finset.Icc 1 Z, (c : ℝ) ^ omega b * (b : ℝ) ^ (-(3 - 3 * t))) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hstep : V b * ((b : ℝ) ^ 3) ^ t = (c : ℝ) ^ omega b * (b : ℝ) ^ (3 * t - 3) := by
        dsimp [V]
        rw [mul_assoc]
        rw [inv_cube_mul_cube_rpow b hb1]
      have hexp : (b : ℝ) ^ (3 * t - 3) = (b : ℝ) ^ (-(3 - 3 * t)) := by
        congr 1
        ring
      rw [hstep, hexp]
    rw [hrew]
    exact coord_color_sum_le_log c Z hc (3 - 3 * t) hs2
  -- step 6: chain together
  have hnA : 0 ≤ (∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) := by
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hU a) (Real.rpow_nonneg (by positivity) t)
  have hnB : 0 ≤ (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t) := by
    apply Finset.sum_nonneg
    intro b hb
    exact mul_nonneg (hV b) (Real.rpow_nonneg (by positivity) t)
  have hmul : (∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) *
        (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t) ≤
      (1 + Real.log (Z : ℝ)) ^ (2 * c) := by
    calc
      (∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) *
          (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t)
          ≤ (1 + Real.log (Z : ℝ)) ^ c * (1 + Real.log (Z : ℝ)) ^ c := by
        have hnL : 0 ≤ (1 + Real.log (Z : ℝ)) ^ c := by
          have hz2 : 2 ≤ Z := by omega
          have hz1 : 1 ≤ (Z : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hz2)
          exact pow_nonneg (by linarith [Real.log_nonneg hz1]) c
        exact mul_le_mul hAcoord hBcoord hnB hnL
      _ = (1 + Real.log (Z : ℝ)) ^ (2 * c) := by
        rw [← pow_add]
        congr 1
        ring
  have hdenpos : 0 < (Y : ℝ) ^ t := Real.rpow_pos_of_pos hYpos t
  have hfinal2 : (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) ≤
      ((∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) *
        (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t)) / (Y : ℝ) ^ t := by
    calc
      (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0)
          ≤ (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
              if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
                (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) := h1
      _ ≤ (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
              if Y < a ^ 2 * b ^ 3 then
                (c : ℝ) ^ omega a * (c : ℝ) ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) := h2
      _ = (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
              if Y < a ^ 2 * b ^ 3 then U a * V b else 0) := h3
      _ ≤ ((∑ a ∈ Finset.Icc 1 Z, U a * ((a : ℝ) ^ 2) ^ t) *
          (∑ b ∈ Finset.Icc 1 Z, V b * ((b : ℝ) ^ 3) ^ t)) / (Y : ℝ) ^ t := by
        simpa [U, V] using h4
  exact le_trans hfinal2 (div_le_div_of_nonneg_right hmul (le_of_lt hdenpos))

end Submission.Vdw
