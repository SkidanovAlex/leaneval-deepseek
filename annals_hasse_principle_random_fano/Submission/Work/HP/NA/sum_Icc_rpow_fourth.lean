import Mathlib

/-!
# A truncated geometric bound for the Hasse-principle argument

The goal is the elementary estimate

`∑_{e=2}^{r} p^{(e+1)/4} · 2 · p^{rN-e} ≤ 10 · p^{rN} / p^{5/4}`

for integers `p ≥ 2`, `N ≥ 1`.  Writing `x = p`, the summand equals

`2 · x^{rN} · x^{-5/4} · (x^{-3/4})^{e-2}`,

so the whole sum is `2 x^{rN} x^{-5/4}` times the geometric sum
`∑_{e=2}^{r} (x^{-3/4})^{e-2}`, which is at most `5` because `x^{-3/4} ≤ 2^{-3/4} ≤ 4/5`.

The three helper lemmas below isolate the two algebraic inputs
(`term_rpow_eq` rewrites a single summand, `geom_Icc_bound` bounds the resulting
geometric sum) and the numerical bound `x^{-3/4} ≤ 4/5`.
-/

namespace Work.HP.NA

/-- Truncated geometric series bound: for `0 ≤ s ≤ 4/5` the sum
`∑_{e=2}^{r} s^{e-2}` is at most `5`. -/
lemma geom_Icc_bound (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 4 / 5) (r : ℕ) :
    ∑ e ∈ Finset.Icc 2 r, s ^ (e - 2) ≤ 5 := by
  have hs1 : s < 1 := by linarith
  have hkey : (∑ e ∈ Finset.Icc 2 r, s ^ (e - 2)) = ∑ k ∈ Finset.range (r - 1), s ^ k := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_add_right_sub_eq (a := 0) (b := r - 1) (c := 2) (f := fun k => s ^ k)]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hkey, Finset.range_eq_Ico]
  calc ∑ k ∈ Finset.Ico 0 (r - 1), s ^ k ≤ s ^ 0 / (1 - s) := geom_sum_Ico_le_of_lt_one hs0 hs1
    _ = 1 / (1 - s) := by norm_num
    _ ≤ 5 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - s)]
        linarith

/-- For real `x ≥ 2` the real power `x^{-3/4}` lies in `[0, 4/5]`. -/
lemma rpow_neg_three_quarters_bounds (x : ℝ) (hx : 2 ≤ x) :
    0 ≤ x ^ (-((3 : ℝ) / 4)) ∧ x ^ (-((3 : ℝ) / 4)) ≤ 4 / 5 := by
  have hx0 : 0 ≤ x := by linarith
  refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
  have h1 : x ^ (-((3 : ℝ) / 4)) ≤ (2 : ℝ) ^ (-((3 : ℝ) / 4)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
  have h2 : (2 : ℝ) ^ (-((3 : ℝ) / 4)) ≤ 4 / 5 := by
    rw [← Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 4)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  linarith

/-- Rewriting a single summand of the target sum: for `x > 0`, `2 ≤ e` and `e ≤ rN`,
`x^{(e+1)/4} · (2 x^{rN-e}) = (2 x^{rN} x^{-5/4}) · (x^{-3/4})^{e-2}`. -/
lemma term_rpow_eq (x : ℝ) (hx : 0 < x) (r N e : ℕ) (he : 2 ≤ e) (hle : e ≤ r * N) :
    x ^ (((e : ℝ) + 1) / 4) * (2 * x ^ (r * N - e))
      = (2 * x ^ (r * N) * x ^ (-((5 : ℝ) / 4))) * (x ^ (-((3 : ℝ) / 4))) ^ (e - 2) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have h1 : x ^ (r * N - e) = x ^ ((r : ℝ) * N - e) := by
    rw [← Real.rpow_natCast x (r * N - e), Nat.cast_sub hle, Nat.cast_mul]
  have h2 : x ^ (((e : ℝ) + 1) / 4) * x ^ ((r : ℝ) * N - e)
      = x ^ ((r : ℝ) * N + (1 - 3 * (e : ℝ)) / 4) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have h3 : x ^ ((r : ℝ) * N + (1 - 3 * (e : ℝ)) / 4)
      = x ^ ((r : ℝ) * N) * x ^ ((1 - 3 * (e : ℝ)) / 4) := by
    rw [Real.rpow_add hx]
  have h4 : x ^ ((r : ℝ) * N) = x ^ (r * N) := by
    rw [← Nat.cast_mul, Real.rpow_natCast]
  have h5 : x ^ ((1 - 3 * (e : ℝ)) / 4)
      = x ^ (-((5 : ℝ) / 4)) * (x ^ (-((3 : ℝ) / 4))) ^ (e - 2) := by
    have hw : (x ^ (-((3 : ℝ) / 4))) ^ (e - 2) = x ^ ((-((3 : ℝ) / 4)) * ((e : ℝ) - 2)) := by
      rw [show ((e : ℝ) - 2) = ((e - 2 : ℕ) : ℝ) by rw [Nat.cast_sub he]; norm_num]
      rw [Real.rpow_mul hx0, Real.rpow_natCast]
    rw [hw, ← Real.rpow_add hx]
    congr 1; ring
  rw [h1]
  calc x ^ (((e : ℝ) + 1) / 4) * (2 * x ^ ((r : ℝ) * N - e))
      = 2 * (x ^ (((e : ℝ) + 1) / 4) * x ^ ((r : ℝ) * N - e)) := by ring
    _ = 2 * x ^ ((r : ℝ) * N + (1 - 3 * (e : ℝ)) / 4) := by rw [h2]
    _ = 2 * (x ^ ((r : ℝ) * N) * x ^ ((1 - 3 * (e : ℝ)) / 4)) := by rw [h3]
    _ = 2 * (x ^ (r * N) * x ^ ((1 - 3 * (e : ℝ)) / 4)) := by rw [h4]
    _ = 2 * (x ^ (r * N) * (x ^ (-((5 : ℝ) / 4)) * (x ^ (-((3 : ℝ) / 4))) ^ (e - 2))) := by
          rw [h5]
    _ = (2 * x ^ (r * N) * x ^ (-((5 : ℝ) / 4))) * (x ^ (-((3 : ℝ) / 4))) ^ (e - 2) := by ring

theorem sum_Icc_rpow_fourth (p r N : ℕ) (hp : 2 ≤ p) (hN : 1 ≤ N) :
    (∑ e ∈ Finset.Icc 2 r,
        (p : ℝ) ^ (((e : ℝ) + 1) / 4) * (2 * (p : ℝ) ^ (r * N - e)))
      ≤ 10 * (p : ℝ) ^ (r * N) / (p : ℝ) ^ ((5 : ℝ) / 4) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hx0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- rewrite each summand
  have hterm : ∀ e ∈ Finset.Icc 2 r,
      (p : ℝ) ^ (((e : ℝ) + 1) / 4) * (2 * (p : ℝ) ^ (r * N - e))
        = (2 * (p : ℝ) ^ (r * N) * (p : ℝ) ^ (-((5 : ℝ) / 4)))
            * ((p : ℝ) ^ (-((3 : ℝ) / 4))) ^ (e - 2) := by
    intro e he
    rw [Finset.mem_Icc] at he
    obtain ⟨he2, her⟩ := he
    have heN : e ≤ r * N := by
      have hrN : r ≤ r * N := by
        have h := Nat.mul_le_mul_left r hN
        rwa [Nat.mul_one] at h
      exact le_trans her hrN
    exact term_rpow_eq (p : ℝ) hx0 r N e he2 heN
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  have hs0 : 0 ≤ (p : ℝ) ^ (-((3 : ℝ) / 4)) := (rpow_neg_three_quarters_bounds (p : ℝ) hp2).1
  have hs : (p : ℝ) ^ (-((3 : ℝ) / 4)) ≤ 4 / 5 := (rpow_neg_three_quarters_bounds (p : ℝ) hp2).2
  have hg : (∑ e ∈ Finset.Icc 2 r, ((p : ℝ) ^ (-((3 : ℝ) / 4))) ^ (e - 2)) ≤ 5 :=
    geom_Icc_bound _ hs0 hs r
  have hC : 0 ≤ 2 * (p : ℝ) ^ (r * N) * (p : ℝ) ^ (-((5 : ℝ) / 4)) := by
    have h1 : (0 : ℝ) ≤ (p : ℝ) ^ (r * N) := pow_nonneg (le_of_lt hx0) _
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ (-((5 : ℝ) / 4)) := Real.rpow_nonneg (le_of_lt hx0) _
    exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
  calc 2 * (p : ℝ) ^ (r * N) * (p : ℝ) ^ (-((5 : ℝ) / 4))
          * (∑ e ∈ Finset.Icc 2 r, ((p : ℝ) ^ (-((3 : ℝ) / 4))) ^ (e - 2))
      ≤ 2 * (p : ℝ) ^ (r * N) * (p : ℝ) ^ (-((5 : ℝ) / 4)) * 5 := by
          apply mul_le_mul_of_nonneg_left hg hC
    _ = 10 * (p : ℝ) ^ (r * N) / (p : ℝ) ^ ((5 : ℝ) / 4) := by
          rw [Real.rpow_neg (le_of_lt hx0) ((5 : ℝ) / 4), div_eq_mul_inv]
          ring

end Work.HP.NA
