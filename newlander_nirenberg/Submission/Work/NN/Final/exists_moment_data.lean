import Mathlib
import Submission.Work.NN.Final.MomentSetup
import Submission.Work.NN.Final.Bfun_functional
import Submission.Work.NN.Final.mkappa_pos

/-!
# Existence of Seeley moment data

We produce sequences `a, b : ℕ → ℝ` with `b m ≥ 2`, `b m → ∞`, the moment identities
`∑' m, a m * (-(b m))^j = 1` for every `j`, and summability of `∑' m, |a m| * (b m)^j`.

The construction uses the entire function `Bfun u = ∏_{p ≥ 1} (1 - u/3^p)` (built from the
recursion in `MomentSetup`), with `mkappa = Bfun 1 ≠ 0`.  Writing
`ma m = mcoef m / mkappa` and `mb m = 3^(m+1) - 1`, the functional equation
`Bfun (3u) = (1-u) Bfun u` gives `Bfun (3^i) = 0` for `i ≥ 1` and `Bfun 1 = mkappa`, hence
`∑' m, ma m * (3^m)^i = δ_{i0}`.  For a polynomial `q` this yields `∑' m, ma m * q (3^m) = q 0`,
and applying it to `q = (fun u => 1 - 3*u)^j = (-(mb ·))^j` gives `∑' m, ma m * (-(mb m))^j = 1`.
-/

namespace Work.NN.Final

/-- `Bfun (3^(j+1)) = 0`: the zeros of `∏ (1 - u/3^p)` at the powers `3, 9, 27, …`. -/
lemma Bfun_pow_three (j : ℕ) : Bfun ((3:ℝ)^(j+1)) = 0 := by
  induction j with
  | zero => have h := Bfun_functional 1; simpa using h
  | succ k ih =>
    have h := Bfun_functional ((3:ℝ)^(k+1))
    rw [show (3:ℝ)^(k+1+1) = 3 * (3:ℝ)^(k+1) by rw [pow_succ]; ring]
    rw [h, ih, mul_zero]

/-- The weights `a m = mcoef m / mkappa`. -/
noncomputable def ma (m : ℕ) : ℝ := mcoef m / mkappa

/-- The scales `b m = 3^(m+1) - 1`. -/
noncomputable def mb (m : ℕ) : ℝ := (3:ℝ)^(m+1) - 1

lemma ma_summable_mul_pow (i : ℕ) : Summable (fun m => ma m * ((3:ℝ)^m)^i) := by
  apply Summable.of_norm_bounded (g := fun m => (1/mkappa) * (((3:ℝ)^i/2)^m / (m.factorial:ℝ)))
  · exact (Real.summable_pow_div_factorial ((3:ℝ)^i/2)).mul_left (1/mkappa)
  · intro m
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |ma m| = (1/mkappa) * |mcoef m| := by
      rw [ma, abs_div, abs_of_pos mkappa_pos, div_eq_mul_inv, one_div]; ring
    have h2 : |((3:ℝ)^m)^i| = ((3:ℝ)^i)^m := by
      rw [abs_of_nonneg (by positivity), ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h2, h1]
    have h3 : |mcoef m| ≤ 1 / ((m.factorial:ℝ) * (2:ℝ)^m) := mcoef_bound m
    calc (1/mkappa) * |mcoef m| * ((3:ℝ)^i)^m
        ≤ (1/mkappa) * (1 / ((m.factorial:ℝ) * (2:ℝ)^m)) * ((3:ℝ)^i)^m := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h3 (div_nonneg zero_le_one (le_of_lt mkappa_pos))
      _ = (1/mkappa) * (((3:ℝ)^i/2)^m / (m.factorial:ℝ)) := by
            rw [div_pow]; field_simp

lemma ma_moment (i : ℕ) : ∑' m, ma m * ((3:ℝ)^m)^i = (if i = 0 then 1 else 0) := by
  have hBfun1 : Bfun 1 = mkappa := by rw [Bfun, mkappa]; congr 1; ext n; rw [one_pow, mul_one]
  have hB : ∑' m, mcoef m * ((3:ℝ)^m)^i = Bfun ((3:ℝ)^i) := by
    rw [Bfun]; apply tsum_congr; intro n; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [show (fun m => ma m * ((3:ℝ)^m)^i) = (fun m => (1/mkappa) * (mcoef m * ((3:ℝ)^m)^i)) by
        ext m; rw [ma]; ring]
  rw [tsum_mul_left, hB]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [ite_eq_left rfl, pow_zero, hBfun1, one_div, inv_mul_cancel₀ (ne_of_gt mkappa_pos)]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [ite_eq_right (by omega : ¬ (k + 1 = 0)), Bfun_pow_three k, mul_zero]

lemma mb_moment (j : ℕ) : ∑' m, ma m * (-(mb m))^j = 1 := by
  have hexp : ∀ m, (-(mb m))^j
      = ∑ i ∈ Finset.range (j+1), (Nat.choose j i : ℝ) * (-(3:ℝ))^i * ((3:ℝ)^m)^i := by
    intro m
    rw [show -(mb m) = (-(3 * (3:ℝ)^m)) + 1 by rw [mb]; ring]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [one_pow, mul_one, show -(3 * (3:ℝ)^m) = (-3) * (3:ℝ)^m by ring, mul_pow]
    ring
  calc ∑' m, ma m * (-(mb m))^j
      = ∑' m, ma m * (∑ i ∈ Finset.range (j+1), (Nat.choose j i : ℝ) * (-(3:ℝ))^i * ((3:ℝ)^m)^i) := by
          apply tsum_congr; intro m; rw [hexp]
    _ = ∑' m, ∑ i ∈ Finset.range (j+1), ((Nat.choose j i : ℝ) * (-(3:ℝ))^i) * (ma m * ((3:ℝ)^m)^i) := by
          apply tsum_congr; intro m; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i hi; ring
    _ = ∑ i ∈ Finset.range (j+1), ∑' m, ((Nat.choose j i : ℝ) * (-(3:ℝ))^i) * (ma m * ((3:ℝ)^m)^i) := by
          apply Summable.tsum_finsetSum; intro i hi
          exact (ma_summable_mul_pow i).mul_left _
    _ = ∑ i ∈ Finset.range (j+1), ((Nat.choose j i : ℝ) * (-(3:ℝ))^i) * (∑' m, ma m * ((3:ℝ)^m)^i) := by
          apply Finset.sum_congr rfl; intro i hi; rw [tsum_mul_left]
    _ = ∑ i ∈ Finset.range (j+1), ((Nat.choose j i : ℝ) * (-(3:ℝ))^i) * (if i = 0 then 1 else 0) := by
          apply Finset.sum_congr rfl; intro i hi; rw [ma_moment]
    _ = 1 := by
          rw [Finset.sum_eq_single 0]
          · norm_num
          · intro i hi hne; rw [ite_eq_right hne, mul_zero]
          · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos j)) h

lemma mb_summable (j : ℕ) : Summable (fun m => |ma m| * (mb m)^j) := by
  apply Summable.of_nonneg_of_le
    (g := fun m => |ma m| * (mb m)^j)
    (f := fun m => (3:ℝ)^j/mkappa * (((3:ℝ)^j/2)^m / (m.factorial:ℝ)))
  · intro m
    exact mul_nonneg (abs_nonneg _)
      (pow_nonneg (by rw [mb]; linarith [show (1:ℝ) ≤ (3:ℝ)^(m+1) from one_le_pow₀ (by norm_num)]) j)
  · intro m
    have h1 : |ma m| = (1/mkappa) * |mcoef m| := by
      rw [ma, abs_div, abs_of_pos mkappa_pos, div_eq_mul_inv, one_div]; ring
    have hbb0 : 0 ≤ mb m := by
      rw [mb]; linarith [show (1:ℝ) ≤ (3:ℝ)^(m+1) from one_le_pow₀ (by norm_num)]
    have hbb : (mb m)^j ≤ ((3:ℝ)^(m+1))^j := by
      apply pow_le_pow_left₀ hbb0
      rw [mb]; exact sub_le_self _ (by norm_num)
    have hc : (0:ℝ) ≤ (1/mkappa) * |mcoef m| :=
      mul_nonneg (div_nonneg zero_le_one (le_of_lt mkappa_pos)) (abs_nonneg _)
    have hc2 : (0:ℝ) ≤ 1/mkappa := div_nonneg zero_le_one (le_of_lt mkappa_pos)
    calc |ma m| * (mb m)^j
        ≤ (1/mkappa) * |mcoef m| * ((3:ℝ)^(m+1))^j := by
            rw [h1]; exact mul_le_mul_of_nonneg_left hbb hc
      _ ≤ (1/mkappa) * (1/((m.factorial:ℝ)*(2:ℝ)^m)) * ((3:ℝ)^(m+1))^j := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left (mcoef_bound m) hc2
      _ = (3:ℝ)^j/mkappa * (((3:ℝ)^j/2)^m / (m.factorial:ℝ)) := by
            rw [show ((3:ℝ)^(m+1))^j = ((3:ℝ)^j)^m * (3:ℝ)^j by
                  rw [← pow_mul, ← pow_mul, Nat.mul_comm, Nat.mul_add, Nat.mul_one, pow_add]]
            rw [div_pow]; field_simp
  · exact (Real.summable_pow_div_factorial ((3:ℝ)^j/2)).mul_left ((3:ℝ)^j/mkappa)

theorem exists_moment_data : ∃ (a : ℕ → ℝ) (b : ℕ → ℝ), (∀ m, 2 ≤ b m) ∧ Filter.Tendsto b Filter.atTop Filter.atTop ∧ (∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1) ∧ (∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j) := by
  refine ⟨ma, mb, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [mb, pow_succ]
    have h : (1:ℝ) ≤ (3:ℝ)^m := one_le_pow₀ (by norm_num)
    nlinarith [h]
  · have h3 : Filter.Tendsto (fun m : ℕ => (3:ℝ)^m) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h4 : Filter.Tendsto (fun m : ℕ => (3:ℝ)^(m+1)) Filter.atTop Filter.atTop := by
      have : (fun m : ℕ => (3:ℝ)^(m+1)) = fun m => (3:ℝ) * (3:ℝ)^m := by ext m; rw [pow_succ]; ring
      rw [this]; exact h3.const_mul_atTop (by norm_num)
    rw [show mb = fun m : ℕ => (3:ℝ)^(m+1) + (-1) by ext m; rw [mb]; ring]
    exact Filter.tendsto_atTop_add_const_right _ (-1) h4
  · intro j; exact mb_moment j
  · intro j; exact mb_summable j

end Work.NN.Final
