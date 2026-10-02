import Submission.Work.Deep.GKO.NarrowImports

namespace Work.Deep.GKO.OneFact

/-- Taylor bound: for `y ≥ 0`, `Real.exp y ≥ y^4 / 24` (the `k = 4` term of the
exponential series). -/
private lemma exp_ge_poly4 {y : ℝ} (hy : 0 ≤ y) : y ^ 4 / 24 ≤ Real.exp y := by
  have hsum := Real.sum_le_exp_of_nonneg hy 5
  have hterm : y ^ 4 / (Nat.factorial 4 : ℝ) ≤
      ∑ i ∈ Finset.range 5, y ^ i / (Nat.factorial i : ℝ) := by
    refine Finset.single_le_sum (s := Finset.range 5)
      (f := fun i => y ^ i / (Nat.factorial i : ℝ)) ?_ ?_
    · intro i _
      exact div_nonneg (pow_nonneg hy i) (by positivity)
    · norm_num
  have h4 : y ^ 4 / (Nat.factorial 4 : ℝ) = y ^ 4 / 24 := by norm_num
  rw [h4] at hterm
  linarith

theorem union_bound_numeric {n : ℕ} (hn : 2 ≤ n) :
    2 * (n : ℝ) * Real.exp (-(2 * (2 * (n : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 / ((n : ℝ) / 2))) < 1 := by
  set N : ℝ := (n : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa [hNdef] using this
  have hNpos : 0 < N := by linarith
  set u : ℝ := N ^ ((1 : ℝ) / 3) with hudef
  have hupos : 0 < u := Real.rpow_pos_of_pos hNpos _
  have hu1 : 1 ≤ u := by
    rw [hudef]
    exact Real.one_le_rpow (by linarith : (1 : ℝ) ≤ N) (by norm_num)
  have hN23 : N ^ ((2 : ℝ) / 3) = u ^ 2 := by
    rw [hudef, show (2 : ℝ) / 3 = (1 : ℝ) / 3 * 2 by norm_num, Real.rpow_mul hNpos.le,
      Real.rpow_ofNat]
  have hu3 : u ^ 3 = N := by
    rw [hudef, ← Real.rpow_natCast (N ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hNpos.le]
    norm_num
  have hexp : 2 * (2 * N ^ ((2 : ℝ) / 3)) ^ 2 / (N / 2) = 16 * u := by
    rw [hN23, ← hu3]
    field_simp
    ring
  rw [hexp, ← hu3]
  have hpoly : (16 * u) ^ 4 / 24 ≤ Real.exp (16 * u) := exp_ge_poly4 (by positivity)
  have h48 : (48 : ℝ) < 65536 * u := by nlinarith
  have h2u3 : 2 * u ^ 3 < (16 * u) ^ 4 / 24 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 24)]
    have h : 48 * u ^ 3 < 65536 * u ^ 4 := by
      calc 48 * u ^ 3 < (65536 * u) * u ^ 3 := mul_lt_mul_of_pos_right h48 (by positivity)
        _ = 65536 * u ^ 4 := by ring
    have h16 : (16 * u) ^ 4 = 65536 * u ^ 4 := by ring
    rw [h16]
    nlinarith
  have hlt : 2 * u ^ 3 < Real.exp (16 * u) := lt_of_lt_of_le h2u3 hpoly
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  exact hlt

end Work.Deep.GKO.OneFact
