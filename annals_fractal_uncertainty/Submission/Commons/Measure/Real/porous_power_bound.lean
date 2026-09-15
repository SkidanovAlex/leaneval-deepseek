import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Measure.Real

/-- For `0 < x`, `x ≠ 1` and `0 < y`, we have `x ^ (log y / log x) = y`. -/
lemma rpow_log_div_log_of_pos {x y : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) (hy : 0 < y) :
    x ^ (Real.log y / Real.log x) = y := by
  have hlogx : Real.log x ≠ 0 := by
    intro h
    rcases (Real.log_eq_zero.mp h) with h' | h' | h'
    · linarith
    · exact hx1 h'
    · linarith
  rw [Real.rpow_def_of_pos hx, mul_div_cancel₀ _ hlogx, Real.exp_log hy]

/-- The pure real-variable estimate behind the geometric iteration for porous sets: if `R / L^N ≤ α₀` then the `N`-fold factor `(L-1)^N` times the remaining scale `R/L^N` is bounded by `R · (α₀/R)^γ` with the explicit exponent `γ = log(L/(L-1))/log L`.  (Take logarithms of `R/(L^N α₀) ≤ 1`.) -/
theorem porous_power_bound (L : ℕ) (hL : 2 ≤ L) (N : ℕ) (R α₀ : ℝ) (hR : 0 < R)
    (hα₀ : 0 < α₀) (hN : R / (L : ℝ) ^ N ≤ α₀) :
    (((L - 1 : ℕ) : ℝ) ^ N) * (R / (L : ℝ) ^ N) ≤
      R * (α₀ / R) ^ (Real.log ((L : ℝ) / ((L : ℝ) - 1)) / Real.log (L : ℝ)) := by
  have _hα0 : 0 < α₀ := hα₀
  set Lr : ℝ := (L : ℝ) with hLrdef
  have hLrpos : 0 < Lr := by rw [hLrdef]; exact_mod_cast (by omega : 0 < L)
  have hLr1 : 1 < Lr := by rw [hLrdef]; exact_mod_cast (by omega : 1 < L)
  have hLm1pos : 0 < Lr - 1 := by linarith
  have hcast : ((L - 1 : ℕ) : ℝ) = Lr - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L), hLrdef]; norm_num
  set t : ℝ := Lr / (Lr - 1) with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos hLrpos hLm1pos
  have ht1 : 1 < t := by rw [htdef]; exact (one_lt_div hLm1pos).mpr (by linarith)
  set γ : ℝ := Real.log t / Real.log Lr with hγdef
  have hγpos : 0 < γ := by
    rw [hγdef]; exact div_pos (Real.log_pos ht1) (Real.log_pos hLr1)
  have hLrNpos : 0 < Lr ^ N := pow_pos hLrpos N
  -- hN : R / Lr^N ≤ α₀  ⟹  (Lr^N)⁻¹ ≤ α₀ / R
  have hx : (Lr ^ N)⁻¹ ≤ α₀ / R := by
    rw [inv_le_iff_one_le_mul₀ hLrNpos]
    rw [div_mul_eq_mul_div, one_le_div hR]
    exact (div_le_iff₀ hLrNpos).mp hN
  -- Lr^γ = t
  have hLrγ : Lr ^ γ = t := by
    rw [Real.rpow_def_of_pos hLrpos, hγdef]
    rw [mul_div_cancel₀ _ (ne_of_gt (Real.log_pos hLr1))]
    exact Real.exp_log htpos
  -- the key identity  ((Lr^N)⁻¹)^γ = ((Lr-1)/Lr)^N
  have hkey : ((Lr ^ N)⁻¹) ^ γ = ((Lr - 1) / Lr) ^ N := by
    rw [Real.inv_rpow (le_of_lt hLrNpos)]
    have h1 : (Lr ^ N) ^ γ = t ^ N := by
      rw [← Real.rpow_natCast Lr N, ← Real.rpow_mul (le_of_lt hLrpos), mul_comm (N : ℝ) γ,
        Real.rpow_mul (le_of_lt hLrpos), hLrγ]
      exact Real.rpow_natCast t N
    rw [h1, ← inv_pow]
    congr 1
    rw [htdef, inv_div]
  have hfinal : ((Lr - 1) / Lr) ^ N ≤ (α₀ / R) ^ γ := by
    calc ((Lr - 1) / Lr) ^ N = ((Lr ^ N)⁻¹) ^ γ := hkey.symm
      _ ≤ (α₀ / R) ^ γ :=
          Real.rpow_le_rpow (le_of_lt (inv_pos.mpr hLrNpos)) hx (le_of_lt hγpos)
  rw [hcast, show (Lr - 1) ^ N * (R / Lr ^ N) = R * ((Lr - 1) / Lr) ^ N by rw [div_pow]; ring]
  exact mul_le_mul_of_nonneg_left hfinal (le_of_lt hR)

end Commons.Measure.Real