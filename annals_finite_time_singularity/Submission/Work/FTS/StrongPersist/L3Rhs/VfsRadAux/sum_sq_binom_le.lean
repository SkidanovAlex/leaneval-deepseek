import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Choose.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs.VfsRadAux

theorem sum_sq_binom_le (q : ℕ) (hq : q ≤ 3) (X Y : ℕ → ℝ)
    (hY : ∀ j ≤ 3, |Y j| ≤ 24000) :
    ((∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (X b * Y (q - b))) ^ 2)
      ≤ 256 * 24000 ^ 2 * ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
  -- Rewrite the summand so that Cauchy–Schwarz applies with the coefficient
  -- `f b = C(q,b)·Y(q-b)` against the factor `X b`.
  have hsum_eq : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (X b * Y (q - b)))
      = ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) * X b := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsum_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + 1))
      (fun b => (q.choose b : ℝ) * Y (q - b)) X
  -- The squared coefficient sum is controlled by `4 · (8 · 24000)² = 256 · 24000²`.
  have hf2 : ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) ^ 2
      ≤ 256 * 24000 ^ 2 := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        ((q.choose b : ℝ) * Y (q - b)) ^ 2 ≤ 64 * 24000 ^ 2 := by
      intro b hb
      have hc0 : (0 : ℝ) ≤ (q.choose b : ℝ) := by positivity
      have hc : (q.choose b : ℝ) ^ 2 ≤ 64 := by
        have h' : (q.choose b : ℝ) ≤ 8 := by
          have h1 : q.choose b ≤ 2 ^ q := Nat.choose_le_two_pow q b
          have h2 : 2 ^ q ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hq
          have h3 : q.choose b ≤ 8 := le_trans h1 (by simpa using h2)
          exact_mod_cast h3
        nlinarith [h', hc0]
      have hy : (Y (q - b)) ^ 2 ≤ 24000 ^ 2 := by
        have h := hY (q - b) (by omega)
        exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
      calc ((q.choose b : ℝ) * Y (q - b)) ^ 2
          = (q.choose b : ℝ) ^ 2 * (Y (q - b)) ^ 2 := by ring
        _ ≤ 64 * 24000 ^ 2 := mul_le_mul hc hy (sq_nonneg _) (by norm_num)
    calc ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) ^ 2
        ≤ (Finset.range (q + 1)).card • (64 * 24000 ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((q + 1 : ℕ) : ℝ) * (64 * 24000 ^ 2) := by
            simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ 256 * 24000 ^ 2 := by
          have hq1 : ((q + 1 : ℕ) : ℝ) ≤ 4 := by
            have : q + 1 ≤ 4 := by omega
            exact_mod_cast this
          have hc0 : (0 : ℝ) ≤ 64 * 24000 ^ 2 := by norm_num
          have := mul_le_mul_of_nonneg_right hq1 hc0
          nlinarith [this]
  have hX2 : ∑ b ∈ Finset.range (q + 1), (X b) ^ 2 ≤ ∑ b ∈ Finset.range 4, (X b) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro b hb
      simp only [Finset.mem_range] at hb ⊢
      omega
    · intro b _ _
      exact sq_nonneg _
  calc (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) * X b) ^ 2
      ≤ (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y (q - b)) ^ 2)
          * ∑ b ∈ Finset.range (q + 1), (X b) ^ 2 := hcs
    _ ≤ (256 * 24000 ^ 2) * ∑ b ∈ Finset.range 4, (X b) ^ 2 :=
        mul_le_mul hf2 hX2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)

end Work.FTS.StrongPersist.L3Rhs.VfsRadAux
