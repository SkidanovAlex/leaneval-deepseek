import Mathlib
import Submission.Work.BMF.N7.vk_per_term_bound
import Submission.Work.BMF.N7.vk_exp_decay_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

open Finset

/-- **Assembly.**  If every summand of the dyadic `V_K` sum is dominated by the uniform factor
`B := exp (2 cζ L^{1/7} - (c₀^{-17/7}/5) L^{3/7})`, and if `2(L+2)·B ≤ A L^{6/7}`, then the
whole dyadic sum is `≤ A L^{6/7}`.  The only combinatorial input is
`#(Icc j₀ (J-1)) ≤ J ≤ (L+2)/log 2 ≤ 2(L+2)`. -/
private lemma dyadic_sum_bound_of_decay (c₀ cζ A : ℝ)
    (hper : ∀ (L δ : ℝ) (j : ℕ),
      3 ≤ L → 0 ≤ δ → δ ≤ cζ * L ^ (-(6 / 7 : ℝ)) →
      (L / c₀) ^ (6 / 7 : ℝ) ≤ (j : ℝ) * Real.log 2 →
      (j : ℝ) * Real.log 2 ≤ L + 2 →
      (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2))) ≤
        Real.exp (2 * cζ * L ^ (1 / 7 : ℝ) - c₀ ^ (-(17 / 7) : ℝ) / 5 * L ^ (3 / 7 : ℝ)))
    (hdec : ∀ L : ℝ, 3 ≤ L →
      2 * (L + 2) * Real.exp (2 * cζ * L ^ (1 / 7 : ℝ) - c₀ ^ (-(17 / 7) : ℝ) / 5 * L ^ (3 / 7 : ℝ))
        ≤ A * L ^ (6 / 7 : ℝ)) :
    ∀ (L δ : ℝ) (j₀ J : ℕ),
      3 ≤ L → 0 ≤ δ → δ ≤ cζ * L ^ (-(6 / 7 : ℝ)) →
      (L / c₀) ^ (6 / 7 : ℝ) ≤ (j₀ : ℝ) * Real.log 2 →
      1 ≤ (j₀ : ℝ) * Real.log 2 →
      j₀ ≤ J → (J : ℝ) * Real.log 2 ≤ L + 2 →
      (∑ j ∈ Finset.Icc j₀ (J - 1),
          (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2)))) ≤ A * L ^ (6 / 7 : ℝ) := by
  intro L δ j₀ J hL hδ0 hδle hj₀L hj₀one hj₀J hJ
  set B : ℝ := Real.exp (2 * cζ * L ^ (1 / 7 : ℝ) - c₀ ^ (-(17 / 7) : ℝ) / 5 * L ^ (3 / 7 : ℝ))
    with hBdef
  have hBpos : 0 < B := Real.exp_pos _
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ j ∈ Finset.Icc j₀ (J - 1),
      (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2))) ≤ B := by
    intro j hj
    obtain ⟨hjge, hjle⟩ := Finset.mem_Icc.mp hj
    have ht_ge : (j₀ : ℝ) * Real.log 2 ≤ (j : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hjge) hlog2pos.le
    have hlow : (L / c₀) ^ (6 / 7 : ℝ) ≤ (j : ℝ) * Real.log 2 := le_trans hj₀L ht_ge
    have ht_le : (j : ℝ) * Real.log 2 ≤ L + 2 := by
      have hjJ : (j : ℝ) ≤ (J : ℝ) := by
        have : j ≤ J := by omega
        exact_mod_cast this
      have hstep : (j : ℝ) * Real.log 2 ≤ (J : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hjJ hlog2pos.le
      linarith
    exact hper L δ j hL hδ0 hδle hlow ht_le
  have hJ1 : 1 ≤ J := le_trans (by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · subst h
      simp only [Nat.cast_zero, zero_mul] at hj₀one
      linarith
    · exact h) hj₀J
  have hcard : ((Finset.Icc j₀ (J - 1)).card : ℝ) ≤ 2 * (L + 2) := by
    have h1 : (Finset.Icc j₀ (J - 1)).card ≤ J := by
      have hsub : Finset.Icc j₀ (J - 1) ⊆ Finset.range J := by
        intro x hx
        rw [Finset.mem_range]
        have hx2 := (Finset.mem_Icc.mp hx).2
        omega
      have h := Finset.card_le_card hsub
      rwa [Finset.card_range] at h
    have h1' : ((Finset.Icc j₀ (J - 1)).card : ℝ) ≤ (J : ℝ) := by exact_mod_cast h1
    have h2 : (J : ℝ) ≤ 2 * (L + 2) := by
      have hloghalf : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hJle : (J : ℝ) ≤ (L + 2) / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]; linarith
      have hdiv : (L + 2) / Real.log 2 ≤ 2 * (L + 2) := by
        rw [div_le_iff₀ hlog2pos]
        have hp : 0 ≤ (L + 2) * (2 * Real.log 2 - 1) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hp]
      linarith
    linarith
  calc ∑ j ∈ Finset.Icc j₀ (J - 1),
        (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2)))
      ≤ ∑ _j ∈ Finset.Icc j₀ (J - 1), B := Finset.sum_le_sum hterm
    _ = ((Finset.Icc j₀ (J - 1)).card : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (L + 2) * B := by
          apply mul_le_mul_of_nonneg_right hcard hBpos.le
    _ = 2 * (L + 2) * Real.exp (2 * cζ * L ^ (1 / 7 : ℝ) - c₀ ^ (-(17 / 7) : ℝ) / 5 * L ^ (3 / 7 : ℝ)) := by
          rw [hBdef]
    _ ≤ A * L ^ (6 / 7 : ℝ) := hdec L hL

theorem dyadic_vk_sum_bound (c₀ cζ : ℝ) (hc₀ : 0 < c₀) (hcζ : 0 < cζ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L δ : ℝ) (j₀ J : ℕ),
      3 ≤ L → 0 ≤ δ → δ ≤ cζ * L ^ (-(6 / 7 : ℝ)) →
      (L / c₀) ^ (6 / 7 : ℝ) ≤ (j₀ : ℝ) * Real.log 2 →
      1 ≤ (j₀ : ℝ) * Real.log 2 →
      j₀ ≤ J → (J : ℝ) * Real.log 2 ≤ L + 2 →
      (∑ j ∈ Finset.Icc j₀ (J - 1),
          (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2)))) ≤ A * L ^ (6 / 7 : ℝ) := by
  obtain ⟨A, hApos, hdec⟩ :=
    vk_exp_decay_bound (c₀ ^ (-(17 / 7 : ℝ)) / 5) (2 * cζ)
      (div_pos (Real.rpow_pos_of_pos hc₀ _) (by norm_num)) (by linarith)
  exact ⟨A, hApos, dyadic_sum_bound_of_decay c₀ cζ A (vk_per_term_bound c₀ cζ hc₀ hcζ) hdec⟩

end Work.BMF.N7
