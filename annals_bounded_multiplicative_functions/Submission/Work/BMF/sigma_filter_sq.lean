import Mathlib
import Submission.Work.BMF.sq_sum_div_card_le_sum_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Elementary rearrangement: for `K > 0`, `Q ≤ N` and `K ≤ Q + N`,
`Q²/K - Q ≤ N²/K - N`. -/
lemma sq_div_sub_le_of_le_add {K Q N : ℝ} (hK : 0 < K) (hQN : Q ≤ N) (hKN : K ≤ Q + N) :
    Q ^ 2 / K - Q ≤ N ^ 2 / K - N := by
  have h1 : Q - N ≤ 0 := by linarith
  have h2 : 0 ≤ Q + N - K := by linarith
  have h3 : (Q - N) * (Q + N - K) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
  have h4 : (Q - N) * (Q + N - K) / K ≤ 0 := div_nonpos_of_nonpos_of_nonneg h3 hK.le
  have hid : (Q - N) * (Q + N - K) / K = Q ^ 2 / K - Q - (N ^ 2 / K - N) := by
    field_simp
    ring
  rw [hid] at h4
  linarith

theorem sigma_filter_sq {K P : Type*} [DecidableEq K] [DecidableEq P] (KF : Finset K) (G : K → Finset P)
    (Kbd Q : ℝ) (hKbd : 0 < Kbd) (hKF : (KF.card : ℝ) ≤ Kbd) (hQ : 0 ≤ Q)
    (hsum : Q ≤ ∑ k ∈ KF, ((G k).card : ℝ)) :
    Q ^ 2 / Kbd - Q ≤ ((KF.sigma fun k => ((G k).product (G k)).filter (fun q : P × P => q.1 ≠ q.2)).card : ℝ) := by
  classical
  set N : ℝ := ∑ k ∈ KF, ((G k).card : ℝ) with hN
  set S2 : ℝ := ∑ k ∈ KF, ((G k).card : ℝ) ^ 2 with hS2
  have hQN : Q ≤ N := hsum
  have hNnonneg : 0 ≤ N := by
    rw [hN]; exact Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  -- each block is the off-diagonal of `G k`
  have hoff : ∀ k : K, ((G k).product (G k)).filter (fun q : P × P => q.1 ≠ q.2) = (G k).offDiag := by
    intro k
    ext q
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.product_eq_sprod, Finset.mem_product]
    tauto
  -- the right-hand side equals `∑ (n k ^ 2 - n k)`
  have hRHS : ((KF.sigma fun k => ((G k).product (G k)).filter (fun q : P × P => q.1 ≠ q.2)).card : ℝ)
      = ∑ k ∈ KF, (((G k).card : ℝ) ^ 2 - ((G k).card : ℝ)) := by
    rw [Finset.card_sigma, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hoff k, Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self ((G k).card)), Nat.cast_mul]
    ring
  rw [hRHS, Finset.sum_sub_distrib, ← hS2, ← hN]
  -- Cauchy–Schwarz
  have hCS : N ^ 2 / Kbd ≤ S2 := by
    have h := sq_sum_div_card_le_sum_sq KF (fun k => ((G k).card : ℝ)) Kbd hKbd hKF
    simpa only [hN, hS2] using h
  have hS2geN : N ≤ S2 := by
    rw [hN, hS2]
    apply Finset.sum_le_sum
    intro k _
    rcases Nat.eq_zero_or_pos (G k).card with h0 | h0
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ ((G k).card : ℝ) := by exact_mod_cast h0
      nlinarith
  rcases lt_or_ge Kbd Q with hQK | hQK
  · -- `Kbd < Q`: compare with the value at `N`
    have hKN : Kbd ≤ Q + N := by linarith
    have hstep := sq_div_sub_le_of_le_add hKbd hQN hKN
    linarith
  · -- `Q ≤ Kbd`: left side non-positive, right side non-negative
    have h1 : Q ^ 2 / Kbd - Q ≤ 0 := by
      have h2 : Q ^ 2 / Kbd ≤ Q := by
        rw [div_le_iff₀ hKbd]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hQ (show Q - Kbd ≤ 0 by linarith)]
      linarith
    have h3 : 0 ≤ S2 - N := by linarith
    linarith

end Work.BMF
