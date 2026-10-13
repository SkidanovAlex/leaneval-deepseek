import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

variable {n : ℕ}

/-- A power of a real number of absolute value at most `1` again has absolute value at most
`1`. -/
lemma abs_pow_le_one (x : ℝ) (hx : |x| ≤ 1) (k : ℕ) : |x ^ k| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg x) hx

/-- A product of powers of real numbers of absolute value at most `1` has absolute value at
most `1`. -/
lemma abs_prod_pow_le_one (s : Finset (Fin n)) (a : Fin n → ℕ) (y : Fin n → ℝ)
    (hy : ∀ i, |y i| ≤ 1) : |∏ i ∈ s, y i ^ a i| ≤ 1 := by
  rw [Finset.abs_prod]
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    calc |y j ^ a j| * ∏ i ∈ s, |y i ^ a i|
        ≤ 1 * ∏ i ∈ s, |y i ^ a i| :=
          mul_le_mul (abs_pow_le_one (y j) (hy j) (a j)) le_rfl
            (Finset.prod_nonneg (fun i _ => abs_nonneg _)) zero_le_one
      _ = ∏ i ∈ s, |y i ^ a i| := by rw [one_mul]
      _ ≤ 1 := ih

/-- Telescoping estimate for a single variable: if `|x|, |y| ≤ 1` and `|x - y| ≤ ρ` then
`|x ^ k - y ^ k| ≤ k ρ`. -/
lemma abs_pow_sub_pow_le (x y ρ : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hxy : |x - y| ≤ ρ) :
    ∀ k : ℕ, |x ^ k - y ^ k| ≤ (k : ℝ) * ρ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hdecomp : x ^ (k + 1) - y ^ (k + 1) = x ^ k * (x - y) + y * (x ^ k - y ^ k) := by
      rw [pow_succ, pow_succ]; ring
    rw [hdecomp]
    calc |x ^ k * (x - y) + y * (x ^ k - y ^ k)|
        ≤ |x ^ k * (x - y)| + |y * (x ^ k - y ^ k)| := abs_add_le _ _
      _ = |x ^ k| * |x - y| + |y| * |x ^ k - y ^ k| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * ρ + 1 * ((k : ℝ) * ρ) :=
          add_le_add (mul_le_mul (abs_pow_le_one x hx k) hxy (abs_nonneg _) zero_le_one)
            (mul_le_mul hy ih (abs_nonneg _) zero_le_one)
      _ = ((k + 1 : ℕ) : ℝ) * ρ := by push_cast; ring

/-- Telescoping estimate for a product over a finite set of coordinates: if `|x i|, |y i| ≤ 1`
and `|x i - y i| ≤ ρ` for all `i`, then
`|∏ x i ^ a i - ∏ y i ^ a i| ≤ (∑ a i) ρ`. -/
lemma abs_prod_sub_prod_le (s : Finset (Fin n)) (a : Fin n → ℕ) (x y : Fin n → ℝ) (ρ : ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) (hxy : ∀ i, |x i - y i| ≤ ρ) :
    |∏ i ∈ s, x i ^ a i - ∏ i ∈ s, y i ^ a i| ≤ ((∑ i ∈ s, a i : ℕ) : ℝ) * ρ := by
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hdecomp : x j ^ a j * (∏ i ∈ s, x i ^ a i) - y j ^ a j * (∏ i ∈ s, y i ^ a i)
        = x j ^ a j * ((∏ i ∈ s, x i ^ a i) - (∏ i ∈ s, y i ^ a i))
          + (x j ^ a j - y j ^ a j) * (∏ i ∈ s, y i ^ a i) := by ring
    rw [hdecomp]
    have hP : |x j ^ a j| ≤ 1 := abs_pow_le_one (x j) (hx j) (a j)
    have hQ : |∏ i ∈ s, y i ^ a i| ≤ 1 := abs_prod_pow_le_one s a y hy
    have hpow : |x j ^ a j - y j ^ a j| ≤ (a j : ℝ) * ρ :=
      abs_pow_sub_pow_le (x j) (y j) ρ (hx j) (hy j) (hxy j) (a j)
    calc |x j ^ a j * ((∏ i ∈ s, x i ^ a i) - (∏ i ∈ s, y i ^ a i))
            + (x j ^ a j - y j ^ a j) * (∏ i ∈ s, y i ^ a i)|
        ≤ |x j ^ a j * ((∏ i ∈ s, x i ^ a i) - (∏ i ∈ s, y i ^ a i))|
            + |(x j ^ a j - y j ^ a j) * (∏ i ∈ s, y i ^ a i)| := abs_add_le _ _
      _ = |x j ^ a j| * |(∏ i ∈ s, x i ^ a i) - (∏ i ∈ s, y i ^ a i)|
            + |x j ^ a j - y j ^ a j| * |∏ i ∈ s, y i ^ a i| := by rw [abs_mul, abs_mul]
      _ ≤ |(∏ i ∈ s, x i ^ a i) - (∏ i ∈ s, y i ^ a i)| + |x j ^ a j - y j ^ a j| :=
          add_le_add (mul_le_of_le_one_left (abs_nonneg _) hP)
            (mul_le_of_le_one_right (abs_nonneg _) hQ)
      _ ≤ (((∑ i ∈ s, a i : ℕ) : ℝ) * ρ) + (a j : ℝ) * ρ := add_le_add ih hpow
      _ = (((a j) + ∑ i ∈ s, a i : ℕ) : ℝ) * ρ := by push_cast; ring

/-- The evaluation of a monomial `x ^ α` is `(∑ α)`-Lipschitz, hence `d · n`-Lipschitz on the
cube `[-1,1]^n`. -/
theorem abs_eval_sub_le {n d : ℕ} (α : ExpVec n d) {x y : Fin n → ℝ} {ρ : ℝ}
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) (hρ : ∀ i, |x i - y i| ≤ ρ) :
    |ExpVec.eval α x - ExpVec.eval α y| ≤ (d : ℝ) * (n : ℝ) * ρ := by
  rw [ExpVec.eval_eq_prod α x, ExpVec.eval_eq_prod α y]
  by_cases hn : n = 0
  · subst hn
    simp
  · have hρnn : 0 ≤ ρ := by
      have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      exact (abs_nonneg (x i0 - y i0)).trans (hρ i0)
    have hmain : |∏ i, x i ^ ExpVec.toFun α i - ∏ i, y i ^ ExpVec.toFun α i|
        ≤ ((∑ i, ExpVec.toFun α i : ℕ) : ℝ) * ρ :=
      abs_prod_sub_prod_le Finset.univ (ExpVec.toFun α) x y ρ hx hy hρ
    have hle : ((∑ i, ExpVec.toFun α i : ℕ) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast ExpVec.toFun_sum_le α
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    calc |∏ i, x i ^ ExpVec.toFun α i - ∏ i, y i ^ ExpVec.toFun α i|
        ≤ ((∑ i, ExpVec.toFun α i : ℕ) : ℝ) * ρ := hmain
      _ ≤ (d : ℝ) * ρ := mul_le_mul_of_nonneg_right hle hρnn
      _ ≤ (d : ℝ) * (n : ℝ) * ρ := by
          have hstep : ρ ≤ (n : ℝ) * ρ := by
            calc ρ = 1 * ρ := by ring
              _ ≤ (n : ℝ) * ρ := mul_le_mul_of_nonneg_right hn1 hρnn
          calc (d : ℝ) * ρ ≤ (d : ℝ) * ((n : ℝ) * ρ) := mul_le_mul_of_nonneg_left hstep hd
            _ = (d : ℝ) * (n : ℝ) * ρ := by ring

end Work.WilkiesH.Interp
