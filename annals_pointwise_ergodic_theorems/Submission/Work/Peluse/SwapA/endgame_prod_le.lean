import Mathlib

namespace Work.Peluse.SwapA

/-- The final arithmetic of the assembly: if each of the three factors `Δ`, `η'`, `M/(M+H)` of the
endgame product is bounded below by a `γ`-power (with `0 < γ ≤ 1`), then so is the product, raised to
any power `K`. -/
theorem endgame_prod_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    {Δ η' M H B G M₀ C_E : ℝ} {E K : ℕ}
    (hB0 : 0 < B) (hG0 : 0 < G) (hM₀0 : 0 < M₀) (hCE0 : 0 < C_E)
    (hΔ : B * γ ^ E ≤ Δ) (hη : G * γ ^ E ≤ η') (hM : M₀ * γ ^ K ≤ M / (M + H))
    (hM0 : 0 < M) (hH0 : 0 < H) :
    C_E * (B * G ^ 2 * M₀) ^ K * γ ^ ((3 * E + K) * K)
      ≤ C_E * (Δ * η' ^ 2 * M / (M + H)) ^ K := by
  have hγE : 0 < γ ^ E := pow_pos hγ0 E
  have hγK : 0 < γ ^ K := pow_pos hγ0 K
  have hγp : 0 ≤ γ ^ (3 * E + K) := (pow_pos hγ0 _).le
  have hBγ : 0 ≤ B * γ ^ E := (mul_pos hB0 hγE).le
  have hGγ : 0 ≤ G * γ ^ E := (mul_pos hG0 hγE).le
  have hM₀γ : 0 ≤ M₀ * γ ^ K := (mul_pos hM₀0 hγK).le
  have hΔpos : 0 ≤ Δ := le_trans hBγ hΔ
  have hηpos : 0 ≤ η' := le_trans hGγ hη
  have hΔη : 0 ≤ Δ * η' ^ 2 := mul_nonneg hΔpos (pow_nonneg hηpos 2)
  -- Multiply the three factor estimates.
  have hprod : (B * γ ^ E) * (G * γ ^ E) ^ 2 * (M₀ * γ ^ K)
      ≤ Δ * η' ^ 2 * (M / (M + H)) := by
    have hsq : (G * γ ^ E) ^ 2 ≤ η' ^ 2 := pow_le_pow_left₀ hGγ hη 2
    have h1 : (B * γ ^ E) * (G * γ ^ E) ^ 2 ≤ Δ * η' ^ 2 :=
      mul_le_mul hΔ hsq (pow_nonneg hGγ 2) hΔpos
    exact mul_le_mul h1 hM hM₀γ hΔη
  -- The left-hand side is `B * G ^ 2 * M₀` times the single power `γ ^ (3 * E + K)`.
  have key : (B * γ ^ E) * (G * γ ^ E) ^ 2 * (M₀ * γ ^ K)
      = (B * G ^ 2 * M₀) * γ ^ (3 * E + K) := by
    have h3 : 3 * E + K = E + (E + (E + K)) := by omega
    rw [mul_pow, h3, pow_add, pow_add, pow_add]
    ring
  have hbase : (B * G ^ 2 * M₀) * γ ^ (3 * E + K) ≤ Δ * η' ^ 2 * (M / (M + H)) := by
    rw [← key]; exact hprod
  have hx0 : 0 ≤ (B * G ^ 2 * M₀) * γ ^ (3 * E + K) :=
    mul_nonneg (mul_nonneg (mul_pos hB0 (pow_pos hG0 2)).le hM₀0.le) hγp
  have hpow : ((B * G ^ 2 * M₀) * γ ^ (3 * E + K)) ^ K
      ≤ (Δ * η' ^ 2 * (M / (M + H))) ^ K := pow_le_pow_left₀ hx0 hbase K
  -- Distribute the `K`-th power over the product.
  have hgen : ∀ (X c : ℝ) (p n : ℕ), (X * c ^ p) ^ n = X ^ n * c ^ (p * n) := by
    intro X c p n
    rw [mul_pow, ← pow_mul]
  calc C_E * (B * G ^ 2 * M₀) ^ K * γ ^ ((3 * E + K) * K)
      = C_E * ((B * G ^ 2 * M₀) * γ ^ (3 * E + K)) ^ K := by rw [hgen]; ring
    _ ≤ C_E * (Δ * η' ^ 2 * (M / (M + H))) ^ K := mul_le_mul_of_nonneg_left hpow hCE0.le
    _ = C_E * (Δ * η' ^ 2 * M / (M + H)) ^ K := by rw [mul_div_assoc]

end Work.Peluse.SwapA
