import Mathlib
import Submission.Work.GM.Trace.Defs
import Submission.Work.GM.Trace.trace_two_identity
import Submission.Work.GM.Trace.poisson_hfun
import Submission.Work.GM.Trace.hhat_decay_deriv
import Submission.Work.GM.Trace.sep_card_le
import Submission.Work.GM.Trace.summable_hhat_row
import Submission.Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le

namespace Work.GM.Trace

open Complex Finset
open scoped BigOperators
open Submission.GM Submission.LargeValues

/-! ## The `m ≠ 0` tail of the Poisson sum at `t = 0` -/

/-- `m ↦ |m|^{-100}` is summable on `ℤ`. -/
theorem summable_abs_rpow_neg_int : Summable (fun m : ℤ => |(m:ℝ)| ^ (-(100:ℝ))) :=
  Real.summable_abs_int_rpow (by norm_num)

/-- Pointwise: `|m|^{-100}` equals the `p`-series summand of the commons (which is `0` at `m = 0`). -/
theorem abs_rpow_neg_eq_ite (m : ℤ) :
    |(m:ℝ)| ^ (-(100:ℝ)) = if (1:ℝ) ≤ |(m:ℝ)| then ((|(m:ℝ)|)^100)⁻¹ else 0 := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0
    rw [if_neg (by norm_num : ¬ ((1:ℝ) ≤ |(((0:ℤ)):ℝ)|)), Int.cast_zero, abs_zero,
      Real.zero_rpow (by norm_num : (-(100:ℝ)) ≠ 0)]
  · have h : (1:ℝ) ≤ |(m:ℝ)| := by
      have hz : (1:ℤ) ≤ |m| := Int.one_le_abs hm0
      have hz' : ((1:ℤ):ℝ) ≤ ((|m|:ℤ):ℝ) := by exact_mod_cast hz
      rw [Int.cast_abs, Int.cast_one] at hz'
      exact hz'
    rw [if_pos h, Real.rpow_neg (abs_nonneg _)]
    simp

/-- The `m ≠ 0` tail of the Poisson sum at `t = 0`: if `‖ĥ_0(ξ)‖ ≤ Cd/|ξ|^100` for `ξ ≠ 0`, then
`‖Σ'_{m ≠ 0} ĥ_0(mN)‖ ≤ Cd · T / N^100` for any `T ≥ Σ'_m |m|^{-100}`. -/
theorem tsum_hhat_tail_bound (N : ℕ) (hN : 1 ≤ N) (Cd T : ℝ) (hCd : 0 ≤ Cd)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖hhat 0 ξ‖ ≤ Cd / |ξ| ^ 100)
    (hT : (∑' m : ℤ, |(m:ℝ)| ^ (-(100:ℝ))) ≤ T) :
    ‖∑' m : ℤ, (if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ)))‖
      ≤ Cd * T / (N:ℝ)^100 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  -- summability of the tail
  have hsumm0 : Summable (fun m : ℤ => (if m = 0 then (0:ℂ) else hhat 0 ((m:ℝ) * (N:ℝ)))) := by
    refine Summable.of_norm_bounded (summable_abs_rpow_neg_int.mul_left Cd) (fun m => ?_)
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl, norm_zero]
      rw [show |(((0:ℤ):ℝ))| = 0 by norm_num, Real.zero_rpow (by norm_num : (-(100:ℝ)) ≠ 0),
        mul_zero]
    · rw [if_neg hm]
      have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
      have hξ : (m:ℝ) * (N:ℝ) ≠ 0 := mul_ne_zero hmR hNne
      have hmpos : 0 < |(m:ℝ)| := abs_pos.mpr hmR
      have h1 : ‖hhat 0 ((m:ℝ) * (N:ℝ))‖ ≤ Cd / |(m:ℝ) * (N:ℝ)| ^ 100 := hdec _ hξ
      have h2 : |(m:ℝ) * (N:ℝ)| ^ 100 = |(m:ℝ)| ^ 100 * (N:ℝ) ^ 100 := by
        rw [abs_mul, abs_of_nonneg hNpos.le, mul_pow]
      have h3 : |(m:ℝ)| ^ 100 ≤ |(m:ℝ) * (N:ℝ)| ^ 100 := by
        rw [h2]
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN1R)
      have h4 : Cd / |(m:ℝ) * (N:ℝ)| ^ 100 ≤ Cd / |(m:ℝ)| ^ 100 :=
        div_le_div_of_nonneg_left hCd (by positivity) h3
      have h5 : Cd / |(m:ℝ)| ^ 100 = Cd * |(m:ℝ)| ^ (-(100:ℝ)) := by
        rw [div_eq_mul_inv, Real.rpow_neg (abs_nonneg _)]
        simp
      linarith [h1, h4, h5.le, h5.ge]
  -- the majorant
  have hmaj : Summable (fun m : ℤ => (Cd / (N:ℝ)^100) * |(m:ℝ)| ^ (-(100:ℝ))) :=
    summable_abs_rpow_neg_int.mul_left _
  calc ‖∑' m : ℤ, (if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ)))‖
      ≤ ∑' m : ℤ, ‖(if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ)))‖ :=
        norm_tsum_le_tsum_norm hsumm0.norm
    _ ≤ ∑' m : ℤ, (Cd / (N:ℝ)^100) * |(m:ℝ)| ^ (-(100:ℝ)) := by
        refine hsumm0.norm.tsum_le_tsum (fun m => ?_) hmaj
        by_cases hm : m = 0
        · subst hm
          rw [if_pos rfl, norm_zero]
          rw [show |(((0:ℤ):ℝ))| = 0 by norm_num, Real.zero_rpow (by norm_num : (-(100:ℝ)) ≠ 0),
            mul_zero]
        · rw [if_neg hm]
          have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
          have hξ : (m:ℝ) * (N:ℝ) ≠ 0 := mul_ne_zero hmR hNne
          have h1 : ‖hhat 0 ((m:ℝ) * (N:ℝ))‖ ≤ Cd / |(m:ℝ) * (N:ℝ)| ^ 100 := hdec _ hξ
          have h2 : |(m:ℝ) * (N:ℝ)| ^ 100 = |(m:ℝ)| ^ 100 * (N:ℝ) ^ 100 := by
            rw [abs_mul, abs_of_nonneg hNpos.le, mul_pow]
          have h3 : Cd / |(m:ℝ) * (N:ℝ)| ^ 100
              = (Cd / (N:ℝ)^100) * (|(m:ℝ)| ^ 100)⁻¹ := by
            rw [h2, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
            ring
          have h4 : ((|(m:ℝ)|)^100)⁻¹ = |(m:ℝ)| ^ (-(100:ℝ)) := by
            rw [Real.rpow_neg (abs_nonneg _)]
            simp
          rw [h3, h4] at h1
          exact h1
    _ = (Cd / (N:ℝ)^100) * ∑' m : ℤ, |(m:ℝ)| ^ (-(100:ℝ)) := tsum_mul_left
    _ ≤ (Cd / (N:ℝ)^100) * T := by
        refine mul_le_mul_of_nonneg_left hT (by positivity)
    _ = Cd * T / (N:ℝ)^100 := by ring

-- GM 4.4 with its error term: `tr(M_W M_W*) = N·|W|·Azero + O(N^{-50})`, uniformly over the
-- Prop 3.1 setting.  Via `Work.GM.Trace.trace_two_identity` the trace is
-- `|W| · Σ_{n∈[N,2N]} h_0(n/N)`, and `Work.GM.Trace.poisson_hfun` (at `t = 0`) writes that as
-- `|W| · N · (ĥ_0(0) + Σ'_{m≠0} ĥ_0(mN))`; the tail is bounded by
-- `|W| · N · Σ_{m≠0} C_j (|m|N)^{-j} ≤ |W| · 2 C_j N^{-j+1}` using
-- `Work.GM.Trace.hhat_decay_deriv` with `j = 100`, and `|W| ≤ M N + 1` comes from separation
-- (`ε > 0`), so the error is `≤ N^{-50}` for `N ≥ N₀`.
theorem trace_two_estimate (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ‖Matrix.trace (Submission.LargeValues.MWmat N W *
          (Submission.LargeValues.MWmat N W).conjTranspose) -
        ((N : ℝ) * (W.card : ℝ) * Work.GM.Trace.Azero : ℝ)‖
        ≤ Work.GM.Trace.tinyN N := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  obtain ⟨Cd, hCd0, hCd⟩ := hhat_decay_deriv 100
  have hTle : (∑' m : ℤ, |(m:ℝ)| ^ (-(100:ℝ))) ≤ C0 := by
    rw [tsum_congr (fun m => abs_rpow_neg_eq_ite m)]
    have h := hC0 100 1 (by norm_num) (by norm_num)
    simpa using h
  have hdec0 : ∀ ξ : ℝ, ξ ≠ 0 → ‖hhat 0 ξ‖ ≤ Cd / |ξ| ^ 100 := by
    intro ξ hξ
    have h := hCd 0 ξ hξ
    simpa using h
  refine ⟨max 2 (Nat.ceil (2 * Cd * C0) + 2), ?_⟩
  intro N hN W hWmem hWsep
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  -- the separation lower bound
  have hM1 : 1 ≤ M N := M_ge_one hN1
  have hMε : 1 ≤ (M N) ^ ε := Real.one_le_rpow hM1 hε.le
  have hcard : (W.card : ℝ) ≤ M N + 1 :=
    sep_card_le W (M N) ((M N)^ε) (le_of_lt (M_pos hN1)) hMε hWmem hWsep
  have hMN2 : M N ≤ (N:ℝ)^2 := by
    rw [M]
    calc (N:ℝ) ^ (6 / 5 : ℝ) ≤ (N:ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
      _ = (N:ℝ) ^ 2 := by simp
  have hcard2 : (W.card : ℝ) ≤ 2 * (N:ℝ)^2 := by
    have h : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith
    linarith
  -- the trace, Poisson summation, and the split at `m = 0`
  have htrace : Matrix.trace (MWmat N W * (MWmat N W).conjTranspose)
      = (W.card : ℂ) * ((N:ℂ) * ∑' m : ℤ, hhat 0 ((m:ℝ) * (N:ℝ))) := by
    rw [trace_two_identity N W, poisson_hfun hN1 0]
  have hsplit := (summable_hhat_row N hN1 0 hhat_decay_deriv).tsum_eq_add_tsum_ite (0 : ℤ)
  have hmain : Matrix.trace (MWmat N W * (MWmat N W).conjTranspose) -
        (((N:ℝ) * (W.card:ℝ) * Azero : ℝ) : ℂ)
      = (W.card : ℂ) * (N:ℂ) *
          (∑' m : ℤ, (if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ)))) := by
    rw [htrace, hsplit]
    simp only [Int.cast_zero, zero_mul, hhat_zero_zero]
    push_cast
    ring
  have htail := tsum_hhat_tail_bound N hN1 Cd C0 hCd0 hdec0 hTle
  have hnorm : ‖(W.card : ℂ) * (N:ℂ) *
      (∑' m : ℤ, (if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ))))‖
      = (W.card:ℝ) * (N:ℝ) *
        ‖∑' m : ℤ, (if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ)))‖ := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hkey : 2 * Cd * C0 ≤ (N:ℝ)^47 := by
    have h1 : 2 * Cd * C0 ≤ ((Nat.ceil (2 * Cd * C0) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (2 * Cd * C0) + 2 : ℕ) : ℝ) ≤ (N:ℝ) := by
      have h3 : Nat.ceil (2 * Cd * C0) + 2 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast h3
    have h4 : ((Nat.ceil (2 * Cd * C0) : ℕ) : ℝ) ≤ (N:ℝ) := by
      have : ((Nat.ceil (2 * Cd * C0) : ℕ) : ℝ) ≤ ((Nat.ceil (2 * Cd * C0) + 2 : ℕ) : ℝ) := by
        push_cast; norm_num
      linarith
    exact le_trans (le_trans h1 h4) (le_self_pow₀ hN1R (by norm_num))
  have hden : 0 < (N:ℝ)^97 := by positivity
  have hfinal : 2 * Cd * C0 * (N:ℝ)^3 / (N:ℝ)^100 ≤ 1 / (N:ℝ)^50 := by
    have heq : 2 * Cd * C0 * (N:ℝ)^3 / (N:ℝ)^100 = (2 * Cd * C0) / (N:ℝ)^97 := by
      rw [show (100:ℕ) = 97 + 3 by norm_num, pow_add]
      field_simp
    rw [heq]
    have h1 : (2 * Cd * C0) / (N:ℝ)^97 ≤ (N:ℝ)^47 / (N:ℝ)^97 :=
      div_le_div_of_nonneg_right hkey hden.le
    have h2 : (N:ℝ)^47 / (N:ℝ)^97 = 1 / (N:ℝ)^50 := by
      rw [show (97:ℕ) = 47 + 50 by norm_num, pow_add]
      field_simp
    linarith [h1, h2.le, h2.ge]
  rw [hmain, hnorm, tinyN]
  calc (W.card:ℝ) * (N:ℝ) *
        ‖∑' m : ℤ, (if m = 0 then 0 else hhat 0 ((m:ℝ) * (N:ℝ)))‖
      ≤ (W.card:ℝ) * (N:ℝ) * (Cd * C0 / (N:ℝ)^100) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (2 * (N:ℝ)^2) * (N:ℝ) * (Cd * C0 / (N:ℝ)^100) := by
        have h1 : (W.card:ℝ) * (N:ℝ) ≤ (2 * (N:ℝ)^2) * (N:ℝ) :=
          mul_le_mul_of_nonneg_right hcard2 hNpos.le
        have h2 : 0 ≤ Cd * C0 / (N:ℝ)^100 := by positivity
        exact mul_le_mul_of_nonneg_right h1 h2
    _ = 2 * Cd * C0 * (N:ℝ)^3 / (N:ℝ)^100 := by ring
    _ ≤ 1 / (N:ℝ)^50 := hfinal

end Work.GM.Trace
