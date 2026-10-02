import Mathlib.Analysis.Real.Sqrt

namespace Commons.Data.Real

theorem exvol_arith {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (n : ℕ)
    (hn : 1000 / δ ^ 2 ≤ (n : ℝ)) :
    (1 - 3 * δ) * (((1 + δ) * Real.sqrt (n : ℝ)) * (((1 + δ) * Real.sqrt (n : ℝ)) - 1)) <
      (1 - δ) * ((n : ℝ) - 1) := by
  have hδsq_pos : 0 < δ ^ 2 := by positivity
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set x : ℝ := Real.sqrt (n : ℝ) with hxdef
  have hx_nonneg : 0 ≤ x := by rw [hxdef]; exact Real.sqrt_nonneg _
  have hx_sq : x ^ 2 = (n : ℝ) := by rw [hxdef]; exact Real.sq_sqrt hn_nonneg
  have h1m3δ_pos : 0 < 1 - 3 * δ := by linarith
  have h1pδ_pos : 0 < 1 + δ := by linarith
  -- 1000 ≤ δ² n
  have h2 : (1000 : ℝ) ≤ δ ^ 2 * (n : ℝ) := by
    rw [div_le_iff₀ hδsq_pos] at hn
    nlinarith [hn]
  -- 5000 ≤ δ²(5+3δ) n
  have h5δ : (5 : ℝ) ≤ 5 + 3 * δ := by linarith
  have hbig : (5000 : ℝ) ≤ δ ^ 2 * (5 + 3 * δ) * (n : ℝ) := by
    have h := mul_le_mul h5δ h2 (by norm_num : (0 : ℝ) ≤ 1000)
      (by linarith : (0 : ℝ) ≤ 5 + 3 * δ)
    nlinarith [h]
  have hxterm : (0 : ℝ) ≤ (1 - 3 * δ) * (1 + δ) * x := by
    apply mul_nonneg
    · exact mul_nonneg h1m3δ_pos.le h1pδ_pos.le
    · exact hx_nonneg
  have h1mδ_le : (1 - δ) ≤ 1 := by linarith
  -- exact algebraic identity
  have hP_eq : (1 - δ) * ((n : ℝ) - 1) - (1 - 3 * δ) * (((1 + δ) * x) * (((1 + δ) * x) - 1))
      = δ ^ 2 * (5 + 3 * δ) * (n : ℝ) + (1 - 3 * δ) * (1 + δ) * x - (1 - δ) := by
    have hn_eq : (n : ℝ) = x ^ 2 := hx_sq.symm
    rw [hn_eq]; ring
  have hpos : 0 < δ ^ 2 * (5 + 3 * δ) * (n : ℝ) + (1 - 3 * δ) * (1 + δ) * x - (1 - δ) := by
    linarith [hbig, hxterm, h1mδ_le]
  have hP : 0 < (1 - δ) * ((n : ℝ) - 1) -
      (1 - 3 * δ) * (((1 + δ) * x) * (((1 + δ) * x) - 1)) := by
    rw [hP_eq]; exact hpos
  linarith [hP]

end Commons.Data.Real