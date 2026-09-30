import Mathlib
import Submission.Work.BMF.mr_direct.eboundR_defs
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.pSetBR_mem_range
import Submission.Work.BMF.mr_direct.ebDR_norm_sq_le_one
import Submission.Work.BMF.mr_direct.card_diff_natIcc_range_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators

-- ===== my own helper lemmas =====

private lemma ebDR_eq_zero_of_mem_natIcc (b c : ℕ → ℂ) (K P Q A B : ℝ)
    (hrange : ∀ i ∈ pSetBR K P Q A B,
      ebnn i ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) ∧
        ebnn i ∉ Work.BMF.natIcc A B)
    {n : ℕ} (hn : n ∈ Work.BMF.natIcc A B) :
    ebDR b c K P Q A B n = 0 := by
  have hempty : ebFiberR K P Q A B n = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi heq
    have h2 := (hrange i hi).2
    rw [heq] at h2
    exact h2 hn
  simp [ebDR, hempty]

private lemma ebDR_term_le (b c : ℕ → ℂ) (K P Q A B : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hK : 1 ≤ K)
    (hnorm : ∀ n, ‖ebDR b c K P Q A B n‖ ^ 2 ≤ 1) :
    ∀ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
      ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Real.exp 2 / A ^ 2 := by
  intro n hn
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hBpos : 0 < B := lt_of_lt_of_le hApos hAB
  have hA'pos : 0 < A * Real.exp (-(1 / K)) := by positivity
  have hbnd : (0 : ℝ) ≤ B * Real.exp (1 / K) := by positivity
  have hn_ge : A * Real.exp (-(1 / K)) ≤ (n : ℝ) :=
    ((Work.BMF.mrDirect.mem_natIcc hbnd).mp hn).1
  have hsqq : (A * Real.exp (-(1 / K))) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hA'pos.le hn_ge 2
  have h1 : ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (hnorm n) (by positivity)
  have h2 : 1 / (n : ℝ) ^ 2 ≤ 1 / (A * Real.exp (-(1 / K))) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hA'pos 2) hsqq
  have h3 : 1 / (A * Real.exp (-(1 / K))) ^ 2 = Real.exp (2 / K) / A ^ 2 := by
    have hexp : (Real.exp (-(1 / K))) ^ 2 = Real.exp (-(2 / K)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [mul_pow, hexp, Real.exp_neg]
    field_simp
  have h4 : Real.exp (2 / K) / A ^ 2 ≤ Real.exp 2 / A ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hKpos]
    linarith [hK]
  linarith [h1, h2, h3, h4]

theorem ebDR_sum_div_sq_le (b c : ℕ → ℂ) (K P Q A B : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hK : 1 ≤ K)
    (hnorm : ∀ n, ‖ebDR b c K P Q A B n‖ ^ 2 ≤ 1)
    (hrange : ∀ i ∈ pSetBR K P Q A B,
      ebnn i ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) ∧
        ebnn i ∉ Work.BMF.natIcc A B) :
    (∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
        ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (8 * B / K + 8) * Real.exp 2 / A ^ 2 := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hterm0 := ebDR_term_le b c K P Q A B hA hAB hK hnorm
  set L : Finset ℕ := Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) with hL
  set M : Finset ℕ := Work.BMF.natIcc A B with hM
  have htK : (0 : ℝ) ≤ 1 / K := le_of_lt (one_div_pos.mpr hKpos)
  have hsub : M ⊆ L := by
    rw [hM, hL]
    apply Work.BMF.mrDirect.natIcc_mono
    · exact mul_le_of_le_one_right (by linarith) (Real.exp_le_one_iff.mpr (by linarith))
    · exact le_mul_of_one_le_right (by linarith) (Real.one_le_exp htK)
  have hmidzero : ∀ n ∈ M,
      ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2 = 0 := by
    intro n hn
    have hn' : n ∈ Work.BMF.natIcc A B := by rw [hM] at hn; exact hn
    have h := ebDR_eq_zero_of_mem_natIcc b c K P Q A B hrange hn'
    simp [h]
  have hsplit : (∑ n ∈ L, ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2)
      = ∑ n ∈ L \ M, ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2 := by
    have h := Finset.sum_sdiff hsub
      (f := fun n => ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2)
    rw [Finset.sum_eq_zero hmidzero, add_zero] at h
    exact h.symm
  rw [hsplit]
  calc ∑ n ∈ L \ M, ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ (L \ M).card • (Real.exp 2 / A ^ 2) :=
        Finset.sum_le_card_nsmul (L \ M) _ (Real.exp 2 / A ^ 2)
          (fun n hn => hterm0 n (Finset.mem_sdiff.mp hn).1)
    _ = ((L \ M).card : ℝ) * (Real.exp 2 / A ^ 2) := by rw [nsmul_eq_mul]
    _ ≤ (8 * B / K + 8) * (Real.exp 2 / A ^ 2) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := card_diff_natIcc_range_le A B K hA hAB hK
        have heq : L \ M = (Work.BMF.natIcc (A * Real.exp (-(1 / K)))
              (B * Real.exp (1 / K))).filter (fun n => n ∉ Work.BMF.natIcc A B) := by
          rw [hL, hM, Finset.sdiff_eq_filter]
        rw [heq]; exact h
    _ = (8 * B / K + 8) * Real.exp 2 / A ^ 2 := by ring

theorem eboundR_integral_le (C₀ : ℝ) (hC₀ : Work.BMF.mrDirect.MVConst C₀)
    (b c : ℕ → ℂ) (K P Q A B S : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * A)
    (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (hS : 0 ≤ S) :
    (∫ t in (-S)..S, ‖Work.BMF.mrDirect.eboundR b c K P Q A B t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * (B * Real.exp (1 / K))) *
          ((8 * B / K + 8) * Real.exp 2 / A ^ 2) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := lt_of_lt_of_le hApos hAB
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hNA : 0 < A * Real.exp (-(1 / K)) := by positivity
  have hAB' : A * Real.exp (-(1 / K)) ≤ B * Real.exp (1 / K) := by
    have htK : (0 : ℝ) ≤ 1 / K := le_of_lt (one_div_pos.mpr hKpos)
    have h1 : Real.exp (-(1 / K)) ≤ Real.exp (1 / K) :=
      Real.exp_le_exp.mpr (by linarith)
    calc A * Real.exp (-(1 / K)) ≤ B * Real.exp (-(1 / K)) :=
          mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le
      _ ≤ B * Real.exp (1 / K) := mul_le_mul_of_nonneg_left h1 hBpos.le
  have hrange : ∀ i ∈ pSetBR K P Q A B,
      ebnn i ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) ∧
        ebnn i ∉ Work.BMF.natIcc A B :=
    fun i hi => pSetBR_mem_range K P Q A B hA hAB hK i hi
  have heq : ∀ t : ℝ, Work.BMF.mrDirect.eboundR b c K P Q A B t
      = ∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
          ebDR b c K P Q A B n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) :=
    fun t => eboundR_eq_fiber_sum b c K P Q A B t _
      (fun i hi => (hrange i hi).1)
  have hint : (∫ t in (-S)..S, ‖Work.BMF.mrDirect.eboundR b c K P Q A B t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
            ebDR b c K P Q A B n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun z => ‖z‖ ^ 2) (heq t)
  have hmv := Work.BMF.mrDirect.MVConst.mv_natIcc hC₀ (ebDR b c K P Q A B)
    (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)) S hNA hAB' hS
  have hsum := ebDR_sum_div_sq_le b c K P Q A B hA hAB hK
    (ebDR_norm_sq_le_one b c K P Q A B hA hP hPQ hb hc) hrange
  have hcoef : 0 ≤ 2 * S + 3 * C₀ * (B * Real.exp (1 / K)) := by
    have hC0nn : 0 ≤ C₀ := Work.BMF.mrDirect.MVConst.nonneg hC₀
    have hBnn : 0 ≤ B * Real.exp (1 / K) := by positivity
    have h3 : 0 ≤ 3 * C₀ * (B * Real.exp (1 / K)) :=
      mul_nonneg (mul_nonneg (by norm_num) hC0nn) hBnn
    linarith
  calc (∫ t in (-S)..S, ‖Work.BMF.mrDirect.eboundR b c K P Q A B t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
            ebDR b c K P Q A B n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := hint
    _ ≤ (2 * S + 3 * C₀ * (B * Real.exp (1 / K))) *
          ∑ n ∈ Work.BMF.natIcc (A * Real.exp (-(1 / K))) (B * Real.exp (1 / K)),
            ‖ebDR b c K P Q A B n‖ ^ 2 / (n : ℝ) ^ 2 := hmv
    _ ≤ (2 * S + 3 * C₀ * (B * Real.exp (1 / K))) *
          ((8 * B / K + 8) * Real.exp 2 / A ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hcoef

end Work.BMF.mr_direct
