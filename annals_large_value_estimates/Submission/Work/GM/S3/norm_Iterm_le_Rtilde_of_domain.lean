import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_domain
import Submission.Work.GM.S3.window_defs
import Submission.Work.GM.S3.window_integral_domain
import Submission.Work.GM.S3.norm_Iterm_le_Rtilde_of_window
import Submission.Work.GM.S3.prop72_core
import Submission.Work.GM.S3.pdom_defs
import Submission.Work.GM.S3.box_integral_bound_of_set
import Submission.Work.GM.S3.prop71_card_bound
import Submission.Work.GM.S3.prop71_final_arith

namespace Work.GM.S3

/-!
## A corrected form of GM Prop 7.1 restricted to the true domain

`Work.GM.S3.prop71_main_window` is GM Prop 7.1 with the error term `+ C N^{-20}` *outside* the
`v`-integral (the body of an integral notation extends as far right as possible, so in
`Work.GM.S3.prop71_main` and in `Work.GM.S3.prop71_domain` the `+ C N^{-20}` is swallowed by the
integral and the resulting bound is `C N³ ∫ (g + C N^{-20})`, which carries an extra `C² N^{-17}`
and is *weaker*).  `prop71_domain_window` below is the combination of the two corrections: the
domain of the `v`-integral is the true domain `pdom = pbox ∩ {v₂/v₁ ∈ [1/2,2]}` of
`Submission.Work.GM.S3.pdom_defs`, and the error term sits outside the integral.

The proof is the proof of `Work.GM.S3.prop71_domain` (equivalently of
`Work.GM.S3.prop71_main_window`) with `Work.GM.S3.box_integral_bound_of_set` in place of
`prop71_box_integral_bound` and the final `rhs_domination_of_set` step *dropped*, because the
intermediate `hfinC` of that proof already has the error term outside the integral.
-/

open Submission.LargeValues (M) in
/-- Sharpened GM Prop 7.1 on the true domain, with the error term outside the integral:
`‖Iterm N W m‖ ≤ C N³ ∫_{pdom} 1_{|phas m v| ≤ (MN)^η/N}‖Rprod W v‖ dv + C N^{-20}`. -/
theorem prop71_domain_window :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (M N)) →
      Submission.GM.Separated W ((M N) ^ ε) →
    ∀ m : ℤ × ℤ × ℤ,
      ‖Submission.GM.Iterm N W m‖ ≤ C * (N : ℝ) ^ 3 *
        (∫ v in pdom, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
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
      ∫ v in pdom, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) := by
    rw [← MeasureTheory.integral_indicator measurableSet_pdom]
    apply MeasureTheory.integral_nonneg
    intro v
    by_cases hv : v ∈ pdom
    · rw [Set.indicator_of_mem hv]
      split <;> positivity
    · rw [Set.indicator_of_notMem hv]
      norm_num
  have hbox := box_integral_bound_of_set K Cj hKpos hCjpos j hin hdec pdom measurableSet_pdom
    pdom_subset_pbox (fun N m v hv => innerInt_eq_zero_of_not_mem_pdom hv) N hN η hη W m
  have hfin := prop71_final_arith η hη j hj K Cj Ctail (le_of_lt hKpos) (le_of_lt hCjpos)
    (le_of_lt hCtailpos) hCtailspec N hN W hcard
    (∫ v in pdom, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0))
    (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) hmain hbox
  have hC'le : max K ((9 / 4) * Cj * Ctail) ≤ max (max K ((9 / 4) * Cj * Ctail)) 1 :=
    le_max_left _ _
  have hzpow : (0 : ℝ) ≤ (N : ℝ) ^ (-20 : ℤ) := zpow_nonneg (by positivity) _
  have hfinC : (N : ℝ) ^ 3 * (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      (max (max K ((9 / 4) * Cj * Ctail)) 1) *
        ((N : ℝ) ^ 3 * (∫ v in pdom, (if |phas m v| ≤ (M N) ^ η / (N : ℝ)
          then ‖Rprod W v‖ else 0))) +
      (max (max K ((9 / 4) * Cj * Ctail)) 1) * (N : ℝ) ^ (-20 : ℤ) :=
    le_trans hfin (add_le_add (mul_le_mul_of_nonneg_right hC'le (by positivity))
      (mul_le_mul_of_nonneg_right hC'le hzpow))
  refine le_trans (norm_Iterm_le N W m) ?_
  simpa only [pdom, Rprod, phas, mul_assoc] using hfinC


/-- **The per-`m` estimate of GM 7.2 with NO `hgood` hypothesis (true-domain version).**

This is `Work.GM.S3.norm_Iterm_le_Rtilde_of_window` with the two parameters `c₁ c₂` and the
hypothesis `hgood` (`∀ v ∈ pbox, |phas m v| ≤ (MN)^η/N → v.2/v.1 ∈ Icc c₁ c₂`) *removed*; the
plateau of `ψ₂` is fixed at `[1/2,2]` (i.e. `hψ₂ge : ∀ x ∈ Icc (1/2) 2, 1 ≤ ψ₂ x`, exactly the
clause of the target lemma).  It says: for **every** frequency triple `(m₁,m₂,m₃)` with
`B (MN)^η ≤ |m₂|/2`,

  `‖Iterm N W (m₁,m₂,m₃)‖ ≤ C (N²/B) ∫_{1/2}^{2} ‖R(v)‖ R̃(arg1 m₁(-m₂)m₃ v) R̃(arg2 m₁(-m₂)m₃ v) dv
                            + C N^{-20}`.

Why `hgood` is free: the `u₃`-weight `w2v` forces `v₂/v₁ ∈ [1/2,2]`, so the constraint region of
any `m` lies in the true domain, and on it `v₂/v₁ ∈ [1/2,2]` automatically.  Proof: combine
`Work.GM.S3.prop71_domain` (sharpened Prop 7.1, `pbox`-integral restricted to `v₂/v₁ ∈ [1/2,2]`)
with `Work.GM.S3.window_integral_domain` (the same window step, no `hgood`), exactly as
`norm_Iterm_le_Rtilde_of_window` combines `prop71_main_window` with
`window_integral_le_Rtilde_Icc`. -/
theorem norm_Iterm_le_Rtilde_of_domain :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ B : ℝ, ∀ ψ₁ ψ₂ : ℝ → ℝ, Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
      (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) → (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) →
      0 < (N : ℝ) * B →
    ∀ m₁ m₂ m₃ : ℤ,
      B * (Submission.LargeValues.M N) ^ η ≤ |((m₂ : ℤ) : ℝ)| / 2 →
      ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ ≤
        C * ((N : ℝ) ^ 2 / B) *
          (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 m₁ (-m₂) m₃ v) *
            Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 m₁ (-m₂) m₃ v))
        + C * (N : ℝ) ^ (-20 : ℤ) := by
  intro ε η hε hη
  obtain ⟨C₁, hC₁pos, N₀₁, hmain71⟩ := prop71_domain_window ε η hε hη
  refine ⟨C₁ * Real.sqrt 2, by positivity, max N₀₁ 1, ?_⟩
  intro N hN W hW hsep B ψ₁ ψ₂ hb1 hb2 hψ1ge hψ2ge hNB m₁ m₂ m₃ hspace
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
  have hwin := window_integral_domain (W := W) (N := N) (B := B) (η := η)
      (ψ₁ := ψ₁) (ψ₂ := ψ₂) (C₀ := 4) (m₁ := m₁) (m₂ := m₂) (m₃ := m₃)
      (by norm_num) hb1 hb2 hψ1ge hψ2ge hη hNB hspace
  set A : ℝ := ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ *
      Rtilde W N B ψ₁ ψ₂ (arg1 m₁ (-m₂) m₃ v) *
      Rtilde W N B ψ₁ ψ₂ (arg2 m₁ (-m₂) m₃ v) with hA
  have h71' : ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ ≤
      C₁ * (N : ℝ) ^ 3 *
        (∫ v in pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2},
          (if |phas (m₁, m₂, m₃) v| ≤
            (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))
        + C₁ * (N : ℝ) ^ (-20 : ℤ) := by simpa only [pdom] using h71
  have hwin' : (∫ v in pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2},
        (if |phas (m₁, m₂, m₃) v| ≤
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
          (∫ v in pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2},
            (if |phas (m₁, m₂, m₃) v| ≤
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
