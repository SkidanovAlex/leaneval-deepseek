import Submission.Work.Deep.Sparse.Prelude
namespace Work.Deep.Sparse

/-- The sparsity hypothesis of the probabilistic core at a high-degree vertex: when the
degree exceeds the colour count `k`, the number of ordered pairs of non-adjacent neighbours is
at least `δ D^2 / 2`, which is the quantity required by the concentration input.  Here `D` is
the ceiling of the degree bound `Δ` and `k` is the number of colours. -/
theorem pt_hsp_arith {δ Δ : ℝ} {k D : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : (10 : ℝ) ^ 24 / δ ^ 8 ≤ Δ)
    (hDlt : (D : ℝ) < Δ + 1) (hk : (1 - δ / 100) * (Δ + 1) - 1 ≤ (k : ℝ)) :
    (δ / 2) * (D : ℝ) ^ 2 ≤ ((k : ℝ) - 1) * ((k : ℝ) - 2) - (1 - δ) * Δ ^ 2 := by
  -- ## Consequences of the threshold hypothesis `10^24 / δ^8 ≤ Δ`
  have hδ8pos : (0 : ℝ) < δ ^ 8 := by positivity
  have hδ8le1 : δ ^ 8 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hδ7le : δ ^ 7 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hΔge : (10 : ℝ) ^ 24 ≤ Δ := by
    have : (10 : ℝ) ^ 24 ≤ (10 : ℝ) ^ 24 / δ ^ 8 := by
      rw [le_div_iff₀ hδ8pos]; nlinarith only [hδ8le1]
    linarith
  have hδΔ100 : (100 : ℝ) ≤ δ * Δ := by
    have h : (100 : ℝ) / δ ≤ (10 : ℝ) ^ 24 / δ ^ 8 := by
      rw [div_le_div_iff₀ hδ0 hδ8pos]
      nlinarith only [hδ7le, hδ0.le]
    have h2 : (100 : ℝ) / δ ≤ Δ := le_trans h hΔ
    rw [div_le_iff₀ hδ0] at h2
    nlinarith only [h2]
  have hΔpos : (0 : ℝ) < Δ := by linarith only [hΔge]
  -- ## Facts about `k`
  have hc99 : (99 / 100 : ℝ) ≤ 1 - δ / 100 := by linarith only [hδ1]
  have hy3 : (0 : ℝ) ≤ (1 - δ / 100) * (Δ + 1) - 3 := by nlinarith only [hc99, hΔge]
  have hk1 : (1 - δ / 100) * (Δ + 1) - 2 ≤ (k : ℝ) - 1 := by linarith only [hk]
  have hk2 : (1 - δ / 100) * (Δ + 1) - 3 ≤ (k : ℝ) - 2 := by linarith only [hk]
  have hk1nn : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith only [hk1, hy3]
  have hprod : ((1 - δ / 100) * (Δ + 1) - 2) * ((1 - δ / 100) * (Δ + 1) - 3)
      ≤ ((k : ℝ) - 1) * ((k : ℝ) - 2) := mul_le_mul hk1 hk2 hy3 hk1nn
  -- ## `D ≤ Δ + 1`
  have hDle : (D : ℝ) ≤ Δ + 1 := le_of_lt hDlt
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hDsq : (D : ℝ) ^ 2 ≤ (Δ + 1) ^ 2 := by nlinarith only [hDle, hDnn]
  have hstep : (δ / 2) * (D : ℝ) ^ 2 ≤ (δ / 2) * (Δ + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left hDsq (by linarith only [hδ0])
  -- ## The arithmetic core
  have hkey : (δ / 2) * (Δ + 1) ^ 2 ≤
      ((1 - δ / 100) * (Δ + 1) - 2) * ((1 - δ / 100) * (Δ + 1) - 3) - (1 - δ) * Δ ^ 2 := by
    nlinarith only [hδΔ100, hδ0, hδ1, hΔge]
  linarith only [hstep, hkey, hprod]

end Work.Deep.Sparse
