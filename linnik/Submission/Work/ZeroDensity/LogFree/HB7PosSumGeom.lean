import Mathlib

namespace Work.ZeroDensity.LogFree

/-- The exponential series `∑' n, min 1 (exp((M - n) L))` is dominated by `M + 2`
when `1 ≤ L`.  The first `M` terms each equal `1`, and the tail is a geometric
series with ratio `exp(-L) ≤ 1/2`. -/
theorem HB7PosSumGeom (M : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    (∑' n : ℕ, min 1 (Real.exp (((M : ℝ) - (n : ℝ)) * L))) ≤ (M : ℝ) + 2 := by
  have hLpos : 0 < L := by linarith
  -- the geometric ratio `exp(-L)` is in `[0,1)`
  have hnorm : ‖Real.exp (-L)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    rw [Real.exp_lt_one_iff]
    linarith
  -- shifted terms `f (k + M)` are exactly the powers of `exp(-L)`
  have hstep : ∀ k : ℕ,
      min 1 (Real.exp (((M:ℝ) - ((k + M : ℕ):ℝ)) * L)) = Real.exp (-L) ^ k := by
    intro k
    have h1 : ((k + M : ℕ) : ℝ) = (k:ℝ) + (M:ℝ) := by push_cast; ring
    rw [h1]
    have h2 : ((M:ℝ) - ((k:ℝ) + (M:ℝ))) * L = (k:ℝ) * (-L) := by ring
    rw [h2, Real.exp_nat_mul]
    refine min_eq_right ?_
    exact pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
  have hsumm_shift : Summable (fun k : ℕ =>
      min 1 (Real.exp (((M:ℝ) - ((k + M : ℕ):ℝ)) * L))) := by
    have : (fun k : ℕ => min 1 (Real.exp (((M:ℝ) - ((k + M : ℕ):ℝ)) * L)))
        = (fun k : ℕ => Real.exp (-L) ^ k) := funext hstep
    rw [this]
    exact summable_geometric_iff_norm_lt_one.mpr hnorm
  have hsumm : Summable (fun n : ℕ => min 1 (Real.exp (((M:ℝ) - (n:ℝ)) * L))) :=
    (summable_nat_add_iff M).mp hsumm_shift
  -- the first `M` terms all equal `1`
  have hrange : (∑ i ∈ Finset.range M, min 1 (Real.exp (((M:ℝ) - (i:ℝ)) * L))) = (M:ℝ) := by
    have hterm : ∀ i ∈ Finset.range M, min 1 (Real.exp (((M:ℝ) - (i:ℝ)) * L)) = 1 := by
      intro i hi
      have hiM : i < M := Finset.mem_range.mp hi
      refine min_eq_left ?_
      refine Real.one_le_exp ?_
      have hcast : (M:ℝ) - (i:ℝ) = ((M - i : ℕ) : ℝ) := (Nat.cast_sub (le_of_lt hiM)).symm
      rw [hcast]
      have h1 : (1:ℝ) ≤ ((M - i : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ M - i by omega)
      nlinarith [hL]
    rw [Finset.sum_congr rfl hterm]
    simp
  have hsplit := Summable.sum_add_tsum_nat_add M hsumm
  -- the tail is the geometric series with ratio `exp(-L)`
  have hgeo : (∑' k : ℕ, min 1 (Real.exp (((M:ℝ) - ((k + M : ℕ):ℝ)) * L)))
      = (1 - Real.exp (-L))⁻¹ := by
    rw [show (fun k => min 1 (Real.exp (((M:ℝ) - ((k + M : ℕ):ℝ)) * L)))
        = (fun k => Real.exp (-L)^k) from funext hstep]
    exact tsum_geometric_of_norm_lt_one hnorm
  rw [← hsplit]
  rw [hrange, hgeo]
  -- bound the geometric tail by `2`
  have hc_le : Real.exp (-L) ≤ 1/2 := by
    have h1 : Real.exp (-L) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1:ℝ) ≤ 1/2 := by
      have h2' : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have h3 : Real.exp (-1:ℝ) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
      rw [h3]
      exact one_div_le_one_div_of_le (by norm_num) h2'
    linarith
  have hr : (1 - Real.exp (-L))⁻¹ ≤ 2 := by
    have hpos : (0:ℝ) < 1/2 := by norm_num
    have hhalf : (1:ℝ)/2 ≤ 1 - Real.exp (-L) := by linarith
    calc (1 - Real.exp (-L))⁻¹ = 1 / (1 - Real.exp (-L)) := (one_div _).symm
      _ ≤ 1 / (1/2) := one_div_le_one_div_of_le hpos hhalf
      _ = 2 := by norm_num
  linarith

end Work.ZeroDensity.LogFree
