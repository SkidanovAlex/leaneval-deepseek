import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.prop72_core
import Submission.Work.GM.S3.prop71_main
import Submission.Work.GM.S3.window_integral_le_Rtilde

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators

/- ## A corrected form of GM Proposition 7.1

The statement of `Work.GM.S3.prop71_main` writes the error term `+ C N^{-20}` *inside* the body of
`∫ v in pbox, …` (the body of an integral notation extends as far right as possible), so its
right-hand side is `C N³ ∫_{pbox} (g + C N^{-20}) = C N³ ∫_{pbox} g + (9/4) C² N^{-17}`, which is a
*weaker* statement than GM's `C N³ ∫_{pbox} g + O(N^{-20})`: the error term acquires a factor `N³`
and cannot be absorbed into `O(N^{-20})` any more.  (`Work.GM.S3.prop71_rhs_domination` records this
reading and proves the implication in the *other* direction.)

For the use of Prop 7.1 in §10 (and in `norm_Iterm_le_Rtilde_of_good` below) the error term has to
be outside the integral, so we repeat the last assembly step of `prop71_main` with the corrected
reading.  The intermediate `hfinC` of `prop71_main`'s proof already *is* the corrected form; only
the final domination by `prop71_rhs_domination` is dropped. -/
open Submission.LargeValues (M) in
theorem prop71_main_window :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (M N)) →
      Submission.GM.Separated W ((M N) ^ ε) →
    ∀ m : ℤ × ℤ × ℤ,
      ‖Submission.GM.Iterm N W m‖ ≤ C * (N : ℝ) ^ 3 *
        (∫ v in pbox, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
          then ‖Rprod W v‖ else 0))
        + C * (N : ℝ) ^ (-20 : ℤ) := by
  intro ε η hε hη
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (133 : ℝ) / 6 ≤ (j : ℝ) * η := by
    obtain ⟨j, hj⟩ := exists_nat_ge (133 / (6 * η))
    refine ⟨j, ?_⟩
    have h3 : 133 / (6 * η) * η = 133 / 6 := by field_simp
    have h2 : 133 / (6 * η) * η ≤ (j : ℝ) * η :=
      mul_le_mul_of_nonneg_right hj (le_of_lt hη)
    rwa [h3] at h2
  obtain ⟨K, hKpos, hin⟩ := prop71_inner_uniform
  obtain ⟨Cj, hCjpos, hdec⟩ := prop71_inner_decay j
  obtain ⟨Ctail, hCtailpos, hCtailspec⟩ := prop71_tail_arith η hη j hj
  refine ⟨max (max K ((9 / 4) * Cj * Ctail)) 1, ?_, 1, ?_⟩
  · have h1 : K ≤ max (max K ((9 / 4) * Cj * Ctail)) 1 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  intro N hN W hW hsep m
  have hsep1 : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s| := by
    intro t ht s hs hts
    refine le_trans ?_ (hsep t ht s hs hts)
    have := Real.one_le_rpow (Submission.LargeValues.M_ge_one hN) (le_of_lt hε)
    simpa using this
  have hcard : (W.card : ℝ) ≤ 2 * M N :=
    prop71_card_bound N hN W hW hsep1
  have hmain : (0 : ℝ) ≤
      ∫ v in pbox, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) := by
    rw [← MeasureTheory.integral_indicator measurableSet_pbox]
    apply MeasureTheory.integral_nonneg
    intro v
    by_cases hv : v ∈ pbox
    · rw [Set.indicator_of_mem hv]
      split <;> positivity
    · rw [Set.indicator_of_notMem hv]
      norm_num
  have hbox := prop71_box_integral_bound K Cj hKpos hCjpos j hin hdec N hN η hη W m
  have hfin := prop71_final_arith η hη j hj K Cj Ctail (le_of_lt hKpos) (le_of_lt hCjpos)
    (le_of_lt hCtailpos) hCtailspec N hN W hcard
    (∫ v in pbox, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0))
    (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) hmain hbox
  have hC'le : max K ((9 / 4) * Cj * Ctail) ≤ max (max K ((9 / 4) * Cj * Ctail)) 1 :=
    le_max_left _ _
  have hzpow : (0 : ℝ) ≤ (N : ℝ) ^ (-20 : ℤ) := zpow_nonneg (by positivity) _
  have hfinC : (N : ℝ) ^ 3 * (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      (max (max K ((9 / 4) * Cj * Ctail)) 1) *
        ((N : ℝ) ^ 3 * (∫ v in pbox, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
          then ‖Rprod W v‖ else 0))) +
      (max (max K ((9 / 4) * Cj * Ctail)) 1) * (N : ℝ) ^ (-20 : ℤ) :=
    le_trans hfin (add_le_add (mul_le_mul_of_nonneg_right hC'le (by positivity))
      (mul_le_mul_of_nonneg_right hC'le hzpow))
  refine le_trans (norm_Iterm_le N W m) ?_
  simpa only [pbox, Rprod, phas, mul_assoc] using hfinC

/-! ## The per-`m` bound used in §10 -/

theorem norm_Iterm_le_Rtilde_of_good :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ B : ℝ, ∀ ψ₁ ψ₂ : ℝ → ℝ, Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
      (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) → (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) →
      0 < (N : ℝ) * B →
    ∀ m₁ m₂ m₃ : ℤ,
      B * (Submission.LargeValues.M N) ^ η ≤ |((m₂ : ℤ) : ℝ)| / 2 →
      (∀ v ∈ Work.GM.S3.pbox, |Work.GM.S3.phas (m₁, m₂, m₃) v| ≤
          (Submission.LargeValues.M N) ^ η / (N : ℝ) → v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2) →
      ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ ≤
        C * ((N : ℝ) ^ 2 / B) *
          (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 m₁ (-m₂) m₃ v) *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 m₁ (-m₂) m₃ v))
        + C * (N : ℝ) ^ (-20 : ℤ) := by
  intro ε η hε hη
  obtain ⟨C₁, hC₁pos, N₀₁, hmain71⟩ := prop71_main_window ε η hε hη
  refine ⟨C₁ * Real.sqrt 2, by positivity, max N₀₁ 1, ?_⟩
  intro N hN W hW hsep B ψ₁ ψ₂ hb1 hb2 hψ1ge hψ2ge hNB m₁ m₂ m₃ hspace hgood
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀₁ 1) hN
  have hNne : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hBne : B ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNB
    exact lt_irrefl 0 hNB
  have h71 := hmain71 N (le_trans (le_max_left N₀₁ 1) hN) W hW hsep (m₁, m₂, m₃)
  have hwin := window_integral_le_Rtilde (W := W) (N := N) (B := B) (η := η)
      (ψ₁ := ψ₁) (ψ₂ := ψ₂) (C₀ := 4)
      (by norm_num) hb1 hb2 hψ1ge hψ2ge hη hNB hspace hgood
  set A : ℝ := ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
      Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ v) *
      Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ v) with hA
  have h71' : ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ ≤
      C₁ * (N : ℝ) ^ 3 *
        (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
          (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
        + C₁ * (N : ℝ) ^ (-20 : ℤ) := h71
  have hwin' : (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
      ≤ Real.sqrt 2 * A / ((N : ℝ) * B) := hwin
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcoef : (0 : ℝ) ≤ C₁ * (N : ℝ) ^ 3 :=
    mul_nonneg (le_of_lt hC₁pos) (pow_nonneg (by positivity) 3)
  have key : C₁ * (N : ℝ) ^ 3 * (Real.sqrt 2 * A / ((N : ℝ) * B)) =
      (C₁ * Real.sqrt 2) * ((N : ℝ) ^ 2 / B) * A := by
    field_simp <;> ring
  have htail : C₁ * (N : ℝ) ^ (-20 : ℤ) ≤
      (C₁ * Real.sqrt 2) * (N : ℝ) ^ (-20 : ℤ) := by
    have hle : C₁ ≤ C₁ * Real.sqrt 2 := by nlinarith [hC₁pos, hsqrt2]
    exact mul_le_mul_of_nonneg_right hle (zpow_nonneg (le_of_lt hNpos) _)
  calc ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖
      ≤ C₁ * (N : ℝ) ^ 3 *
          (∫ v in pbox, (if |phas (m₁, m₂, m₃) v| ≤
            (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
          + C₁ * (N : ℝ) ^ (-20 : ℤ) := h71'
    _ ≤ C₁ * (N : ℝ) ^ 3 * (Real.sqrt 2 * A / ((N : ℝ) * B)) +
          C₁ * (N : ℝ) ^ (-20 : ℤ) := by
        have h := mul_le_mul_of_nonneg_left hwin' hcoef
        linarith [h]
    _ = (C₁ * Real.sqrt 2) * ((N : ℝ) ^ 2 / B) * A +
          C₁ * (N : ℝ) ^ (-20 : ℤ) := by
        rw [key]
    _ ≤ (C₁ * Real.sqrt 2) * ((N : ℝ) ^ 2 / B) * A +
          (C₁ * Real.sqrt 2) * (N : ℝ) ^ (-20 : ℤ) := by
        linarith [htail]

end Work.GM.S3
