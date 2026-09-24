import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.hhat_decay
import Submission.Work.GM.Trace.hhat_norm_le_Azero
import Submission.Work.GM.S3.tail_defs
import Submission.Work.GM.S3.tail_pseries
import Submission.Work.GM.S3.phiMaj_sum
import Submission.Work.GM.S3.hhat_le_phiMaj
import Submission.Work.GM.S3.tsum_prod_three
import Submission.Work.GM.S3.Iterm_majorant
import Submission.Work.GM.S3.Iterm_summable
import Submission.Work.GM.S3.finite_part_reindex
import Submission.Work.GM.S3.psi_tail_arith
import Submission.Work.GM.S3.final_rpow_bound
import Submission.Commons.Analysis.Sampling.card_le_separated_finset

namespace Work.GM.S3

set_option maxHeartbeats 2000000

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (hhat hfun Iterm Spart nzCount Separated)
open Submission.LargeValues (M bumpW)

/-- The number of nonzero coordinates is `3` as soon as all three coordinates are nonzero. -/
theorem nzCount_eq_three {m : ℤ × ℤ × ℤ} (h1 : m.1 ≠ 0) (h2 : m.2.1 ≠ 0) (h3 : m.2.2 ≠ 0) :
    nzCount m = 3 := by
  simp [nzCount, h1, h2, h3]

/-- Conversely, if `nzCount m = 3` then all three coordinates of `m` are nonzero. -/
theorem nzCount_eq_three_iff {m : ℤ × ℤ × ℤ} :
    nzCount m = 3 ↔ (m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0) := by
  by_cases h1 : m.1 = 0 <;> by_cases h2 : m.2.1 = 0 <;> by_cases h3 : m.2.2 = 0 <;>
    simp [nzCount, h1, h2, h3]

/-- `Spart k N W` is the sum of `Iterm N W` over `ℤ³` against the indicator of `nzCount = k`. -/
theorem Spart_eq_tsum_indicator (k : ℕ) (N : ℕ) (W : Finset ℝ) :
    Spart k N W =
      ∑' m : ℤ × ℤ × ℤ, Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = k} (Iterm N W) m := by
  rw [Spart]
  exact _root_.tsum_subtype {m : ℤ × ℤ × ℤ | nzCount m = k} (Iterm N W)

/-- For `x : ℤ` with `x ∉ Finset.Icc (-K) K` and `0 ≤ K` one has `(K : ℝ) < |x|`. -/
theorem lt_abs_of_notMem_Icc {K : ℤ} (hK : 0 ≤ K) {x : ℤ} (hx : x ∉ Finset.Icc (-K) K) :
    (K : ℝ) < |(x : ℝ)| := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  rw [Finset.mem_Icc] at hx
  simp only [not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have h1 : (x : ℝ) < -(K : ℝ) := by exact_mod_cast hx
    have h2 : (x : ℝ) < 0 := by linarith
    rw [abs_of_neg h2]
    linarith
  · have h1 : (K : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have h2 : (0 : ℝ) < (x : ℝ) := by linarith
    rw [abs_of_pos h2]
    linarith


/-! ## Renamed copy of the `tsum_tail_Iterm` development

Same mathematics as `Submission/Work/GM/S3/tsum_tail_Iterm.lean`, with every declaration
renamed (`ncTailPart`, `nc_norm_Iterm_le`, `nc_tsum_tail_Iterm`, ...) so that this file can be
imported together with `Submission.Work.GM.S3.prop71_main` (which declares its own
`Work.GM.S3.norm_Iterm_le`) and `Work.GM.S3.norm_Iterm_le_Rtilde_of_good`. -/


open Finset
open scoped BigOperators

open Submission.GM (hhat Iterm)

/-- The tail part of `ψ` at threshold `K`: `ncTailPart K ψ a = if K < |a| then ψ a else 0`. -/
noncomputable def ncTailPart (K : ℝ) (ψ : ℤ → ℝ) (a : ℤ) : ℝ :=
  if K < |(a : ℝ)| then ψ a else 0

lemma ncTailPart_nonneg {K : ℝ} {ψ : ℤ → ℝ} (hψn : ∀ m : ℤ, 0 ≤ ψ m) (a : ℤ) :
    0 ≤ ncTailPart K ψ a := by
  rw [ncTailPart]; split_ifs with h
  · exact hψn a
  · exact le_refl 0

lemma ncTailPart_of_lt {K : ℝ} {ψ : ℤ → ℝ} {a : ℤ} (h : K < |(a : ℝ)|) :
    ncTailPart K ψ a = ψ a := by
  rw [ncTailPart]; exact if_pos h

/-- The norm of a triple sum is at most the sum of the norms. -/
lemma nc_norm_sum3_le {α : Type*} (s : Finset α) (F : α → α → α → ℂ) :
    ‖∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, F a b c‖ ≤ ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ‖F a b c‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a ha => ?_))
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun b hb => ?_))
  exact norm_sum_le _ _

/-- Pointwise bound for `‖Iterm N W m‖` under the hypothesis that one coordinate of `m` is in the
tail: the `ψ`-bound is applied to that coordinate and the `φ`-bound to the other two. -/
lemma nc_norm_Iterm_le (N : ℕ) (W : Finset ℝ) (φ ψ : ℤ → ℝ) (K : ℝ)
    (hφn : ∀ m : ℤ, 0 ≤ φ m) (hψn : ∀ m : ℤ, 0 ≤ ψ m)
    (hφ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ,
        ‖Submission.GM.hhat (t - s) ((m : ℝ) * N)‖ ≤ φ m)
    (hψ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ, K < |(m : ℝ)| →
        ‖Submission.GM.hhat (t - s) ((m : ℝ) * N)‖ ≤ ψ m)
    (m : ℤ × ℤ × ℤ)
    (hm : K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)|) :
    ‖Submission.GM.Iterm N W m‖ ≤ (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
      (ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
        + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
        + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2) := by
  classical
  have hstep1 : ‖Submission.GM.Iterm N W m‖ ≤ (N : ℝ) ^ 3 *
      (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
          ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
          ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖) := by
    rw [show Submission.GM.Iterm N W m = (N : ℂ) ^ 3 *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
            Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
            Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)) from rfl]
    have hN : ‖(N : ℂ) ^ 3‖ = (N : ℝ) ^ 3 := by
      rw [norm_pow, Complex.norm_natCast]
    refine le_trans (norm_mul_le _ _) ?_
    rw [hN]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (nc_norm_sum3_le W (fun t₁ t₂ t₃ =>
      Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N) *
        Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N) *
        Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N))) ?_
    exact Finset.sum_le_sum (fun t₁ h₁ => Finset.sum_le_sum (fun t₂ h₂ =>
      Finset.sum_le_sum (fun t₃ h₃ => (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))))
  have hinner : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
      ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
        ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
        ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ ≤
      ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
        + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
        + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 := by
    intro t₁ h₁ t₂ h₂ t₃ h₃
    rcases hm with h | h | h
    · have ha : ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ ≤ ψ m.1 :=
        hψ t₁ t₂ h₁ h₂ m.1 h
      have hb : ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ ≤ φ m.2.1 :=
        hφ t₂ t₃ h₂ h₃ m.2.1
      have hc : ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ ≤ φ m.2.2 :=
        hφ t₃ t₁ h₃ h₁ m.2.2
      have h2n : 0 ≤ φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2 :=
        mul_nonneg (mul_nonneg (hφn m.1) (ncTailPart_nonneg hψn m.2.1)) (hφn m.2.2)
      have h3n : 0 ≤ φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 :=
        mul_nonneg (mul_nonneg (hφn m.1) (hφn m.2.1)) (ncTailPart_nonneg hψn m.2.2)
      calc ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
          ≤ ψ m.1 * φ m.2.1 * φ m.2.2 := by
            refine mul_le_mul (mul_le_mul ha hb (norm_nonneg _)
              (le_trans (norm_nonneg _) ha)) hc (norm_nonneg _)
              (mul_nonneg (le_trans (norm_nonneg _) ha) (le_trans (norm_nonneg _) hb))
        _ = ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2 := by rw [ncTailPart_of_lt h]
        _ ≤ ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
              + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
              + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 := by linarith
    · have ha : ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ ≤ φ m.1 :=
        hφ t₁ t₂ h₁ h₂ m.1
      have hb : ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ ≤ ψ m.2.1 :=
        hψ t₂ t₃ h₂ h₃ m.2.1 h
      have hc : ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ ≤ φ m.2.2 :=
        hφ t₃ t₁ h₃ h₁ m.2.2
      have h1n : 0 ≤ ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2 :=
        mul_nonneg (mul_nonneg (ncTailPart_nonneg hψn m.1) (hφn m.2.1)) (hφn m.2.2)
      have h3n : 0 ≤ φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 :=
        mul_nonneg (mul_nonneg (hφn m.1) (hφn m.2.1)) (ncTailPart_nonneg hψn m.2.2)
      calc ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
          ≤ φ m.1 * ψ m.2.1 * φ m.2.2 := by
            refine mul_le_mul (mul_le_mul ha hb (norm_nonneg _)
              (le_trans (norm_nonneg _) ha)) hc (norm_nonneg _)
              (mul_nonneg (le_trans (norm_nonneg _) ha) (le_trans (norm_nonneg _) hb))
        _ = φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2 := by rw [ncTailPart_of_lt h]
        _ ≤ ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
              + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
              + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 := by linarith
    · have ha : ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ ≤ φ m.1 :=
        hφ t₁ t₂ h₁ h₂ m.1
      have hb : ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ ≤ φ m.2.1 :=
        hφ t₂ t₃ h₂ h₃ m.2.1
      have hc : ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖ ≤ ψ m.2.2 :=
        hψ t₃ t₁ h₃ h₁ m.2.2 h
      have h1n : 0 ≤ ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2 :=
        mul_nonneg (mul_nonneg (ncTailPart_nonneg hψn m.1) (hφn m.2.1)) (hφn m.2.2)
      have h2n : 0 ≤ φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2 :=
        mul_nonneg (mul_nonneg (hφn m.1) (ncTailPart_nonneg hψn m.2.1)) (hφn m.2.2)
      calc ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
              ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖
          ≤ φ m.1 * φ m.2.1 * ψ m.2.2 := by
            refine mul_le_mul (mul_le_mul ha hb (norm_nonneg _)
              (le_trans (norm_nonneg _) ha)) hc (norm_nonneg _)
              (mul_nonneg (le_trans (norm_nonneg _) ha) (le_trans (norm_nonneg _) hb))
        _ = φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 := by rw [ncTailPart_of_lt h]
        _ ≤ ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
              + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
              + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2 := by linarith
  have hsum : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
          ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
          ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖) ≤
      (W.card : ℝ) ^ 3 *
        (ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
          + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
          + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2) := by
    refine le_trans (Finset.sum_le_sum (fun t₁ h₁ => Finset.sum_le_sum (fun t₂ h₂ =>
      Finset.sum_le_sum (fun t₃ h₃ => hinner t₁ h₁ t₂ h₂ t₃ h₃)))) ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact le_of_eq (by ring)
  calc ‖Submission.GM.Iterm N W m‖ ≤ (N : ℝ) ^ 3 *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖Submission.GM.hhat (t₁ - t₂) ((m.1 : ℝ) * N)‖ *
            ‖Submission.GM.hhat (t₂ - t₃) ((m.2.1 : ℝ) * N)‖ *
            ‖Submission.GM.hhat (t₃ - t₁) ((m.2.2 : ℝ) * N)‖) := hstep1
    _ ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 *
        (ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
          + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
          + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
        (ncTailPart K ψ m.1 * φ m.2.1 * φ m.2.2
          + φ m.1 * ncTailPart K ψ m.2.1 * φ m.2.2
          + φ m.1 * φ m.2.1 * ncTailPart K ψ m.2.2) := by ring

/-- Summability of the product of three one-dimensional summable families on `ℤ³`. -/
lemma nc_summable_prod_triple {f₁ f₂ f₃ : ℤ → ℝ} (h₁ : Summable f₁) (h₂ : Summable f₂)
    (h₃ : Summable f₃) :
    Summable (fun m : ℤ × ℤ × ℤ => f₁ m.1 * f₂ m.2.1 * f₃ m.2.2) := by
  have h23 : Summable (fun q : ℤ × ℤ => f₂ q.1 * f₃ q.2) :=
    summable_mul_of_summable_norm h₂.norm h₃.norm
  exact (summable_mul_of_summable_norm h₁.norm h23.norm).congr (fun x => by ring)

/-- Sum of `‖Iterm N W m‖` over the "large" region `|m₁| > K ∨ |m₂| > K ∨ |m₃| > K` of `ℤ³`,
bounded by `3·N³·|W|³·(tail sum of ψ)·(sum of φ)²`.  Here `φ` is a global one-dimensional majorant
of `‖ĥ_(t-s)(mN)‖` (valid for every `m`) and `ψ` majorises it on the tail `|m| > K`.  Route:
`1_{tail} ≤ ∑_i 1_{|m_i|>K}` (so the pointwise `ψ`-bound is only applied to a coordinate with
`|m_i| > K`, and the `φ`-bound to the other two), then `tsum_le_tsum` and Fubini
(`Summable.tsum_prod`, `summable_mul_of_summable_norm`, `tsum_mul_left`/`tsum_mul_right`) to factor
the triple product into the product of the three one-dimensional sums. -/
theorem nc_tsum_tail_Iterm (N : ℕ) (W : Finset ℝ) (φ ψ : ℤ → ℝ) (K : ℝ)
    (hφn : ∀ m : ℤ, 0 ≤ φ m) (hψn : ∀ m : ℤ, 0 ≤ ψ m)
    (hφS : Summable φ)
    (hψS : Summable (fun m : ℤ => if K < |(m : ℝ)| then ψ m else 0))
    (hφ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ,
        ‖Submission.GM.hhat (t - s) ((m : ℝ) * N)‖ ≤ φ m)
    (hψ : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ, K < |(m : ℝ)| →
        ‖Submission.GM.hhat (t - s) ((m : ℝ) * N)‖ ≤ ψ m) :
    Summable (fun m : ℤ × ℤ × ℤ =>
        (if K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)| then
          ‖Submission.GM.Iterm N W m‖ else 0)) ∧
      tsum (fun m : ℤ × ℤ × ℤ =>
        (if K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)| then
          ‖Submission.GM.Iterm N W m‖ else 0))
      ≤ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3
          * tsum (fun a : ℤ => if K < |(a : ℝ)| then ψ a else 0)
          * tsum (fun b : ℤ => φ b) ^ 2 := by
  classical
  let Ψ : ℤ → ℝ := ncTailPart K ψ
  have hΨn : ∀ a : ℤ, 0 ≤ Ψ a := fun a => ncTailPart_nonneg hψn a
  have hΨS : Summable Ψ := hψS
  let Pfun : ℤ × ℤ × ℤ → ℝ := fun m => Ψ m.1 * φ m.2.1 * φ m.2.2
      + φ m.1 * Ψ m.2.1 * φ m.2.2 + φ m.1 * φ m.2.1 * Ψ m.2.2
  let B : ℤ × ℤ × ℤ → ℝ := fun m => (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Pfun m
  have hPnonneg : ∀ m, 0 ≤ Pfun m := by
    intro m
    have h1 : 0 ≤ Ψ m.1 * φ m.2.1 * φ m.2.2 :=
      mul_nonneg (mul_nonneg (hΨn m.1) (hφn m.2.1)) (hφn m.2.2)
    have h2 : 0 ≤ φ m.1 * Ψ m.2.1 * φ m.2.2 :=
      mul_nonneg (mul_nonneg (hφn m.1) (hΨn m.2.1)) (hφn m.2.2)
    have h3 : 0 ≤ φ m.1 * φ m.2.1 * Ψ m.2.2 :=
      mul_nonneg (mul_nonneg (hφn m.1) (hφn m.2.1)) (hΨn m.2.2)
    exact add_nonneg (add_nonneg h1 h2) h3
  have hBnonneg : ∀ m, 0 ≤ B m := fun m =>
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (hPnonneg m)
  have hFle : ∀ m : ℤ × ℤ × ℤ,
      (if K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)| then
        ‖Submission.GM.Iterm N W m‖ else 0) ≤ B m := by
    intro m
    by_cases hm : K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)|
    · rw [if_pos hm]
      exact nc_norm_Iterm_le N W φ ψ K hφn hψn hφ hψ m hm
    · rw [if_neg hm]
      exact hBnonneg m
  have hFnonneg : ∀ m : ℤ × ℤ × ℤ,
      0 ≤ (if K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)| then
        ‖Submission.GM.Iterm N W m‖ else 0) := by
    intro m
    split_ifs with h
    · exact norm_nonneg _
    · exact le_refl 0
  have hg1 : Summable (fun m : ℤ × ℤ × ℤ => Ψ m.1 * φ m.2.1 * φ m.2.2) :=
    nc_summable_prod_triple hΨS hφS hφS
  have hg2 : Summable (fun m : ℤ × ℤ × ℤ => φ m.1 * Ψ m.2.1 * φ m.2.2) :=
    nc_summable_prod_triple hφS hΨS hφS
  have hg3 : Summable (fun m : ℤ × ℤ × ℤ => φ m.1 * φ m.2.1 * Ψ m.2.2) :=
    nc_summable_prod_triple hφS hφS hΨS
  have hPsum : Summable Pfun := (hg1.add hg2).add hg3
  have hBsum : Summable B := hPsum.mul_left ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3)
  have ht1 : tsum (fun m : ℤ × ℤ × ℤ => Ψ m.1 * φ m.2.1 * φ m.2.2)
      = tsum Ψ * tsum φ * tsum φ := tsum_prod_three Ψ φ φ hΨS hφS hφS
  have ht2 : tsum (fun m : ℤ × ℤ × ℤ => φ m.1 * Ψ m.2.1 * φ m.2.2)
      = tsum φ * tsum Ψ * tsum φ := tsum_prod_three φ Ψ φ hφS hΨS hφS
  have ht3 : tsum (fun m : ℤ × ℤ × ℤ => φ m.1 * φ m.2.1 * Ψ m.2.2)
      = tsum φ * tsum φ * tsum Ψ := tsum_prod_three φ φ Ψ hφS hφS hΨS
  have hPtsum : tsum Pfun
      = tsum (fun m : ℤ × ℤ × ℤ => Ψ m.1 * φ m.2.1 * φ m.2.2)
        + tsum (fun m : ℤ × ℤ × ℤ => φ m.1 * Ψ m.2.1 * φ m.2.2)
        + tsum (fun m : ℤ × ℤ × ℤ => φ m.1 * φ m.2.1 * Ψ m.2.2) := by
    rw [(hg1.add hg2).tsum_add hg3, hg1.tsum_add hg2]
  have hPval : tsum Pfun = 3 * tsum Ψ * (tsum φ) ^ 2 := by
    rw [hPtsum, ht1, ht2, ht3]; ring
  have hBval : tsum B = 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * tsum Ψ * (tsum φ) ^ 2 := by
    rw [hPsum.tsum_mul_left ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3), hPval]; ring
  have hFsum : Summable (fun m : ℤ × ℤ × ℤ =>
      (if K < |(m.1 : ℝ)| ∨ K < |(m.2.1 : ℝ)| ∨ K < |(m.2.2 : ℝ)| then
        ‖Submission.GM.Iterm N W m‖ else 0)) := Summable.of_nonneg_of_le hFnonneg hFle hBsum
  refine ⟨hFsum, ?_⟩
  exact (Summable.tsum_le_tsum hFle hFsum hBsum).trans (le_of_eq hBval)


/-- GM (7.1) truncation, re-usable copy.  The body below is the *same statement* as
`Work.GM.S3.s3_tail` in `Submission/Work/GM/S3/s3_tail.lean` (which is already proved): the goal is
a second, independently usable copy of it.

WHY A SECOND COPY IS NEEDED.  `Submission/Work/GM/S3/prop72_paper.lean` must import both this
truncation and `Work.GM.S3.norm_Iterm_le_Rtilde_of_good` (from
`Submission/Work/GM/S3/norm_Iterm_le_Rtilde_of_good.lean`, which imports
`Submission.Work.GM.S3.prop71_main`).  But `tsum_tail_Iterm.lean` (a dependency of `s3_tail`) and
`prop71_main.lean` both declare `Work.GM.S3.norm_Iterm_le`, so the two cannot coexist:

  `import Submission.Work.GM.S3.tsum_tail_Iterm failed, environment already contains
   'Work.GM.S3.norm_Iterm_le' from Submission.Work.GM.S3.prop71_main`

So the truncation must be re-derived in a file that does not import `tsum_tail_Iterm`.
Concretely: put a *renamed* copy of `Submission/Work/GM/S3/tsum_tail_Iterm.lean` at the top of your
file (rename `norm_Iterm_le` and any other name clashing with `prop71_main`'s chain), then port the
proof of `s3_tail` from `Submission/Work/GM/S3/s3_tail.lean` (its imports are the `depends_on`
list; you may also import `Submission.Commons.Analysis.Sampling.card_le_separated_finset`
directly -- it lies under `Submission/Commons/`, not `Submission/Work/`, so it cannot be listed
here).  Finally CHECK that a file importing both `Submission.Work.GM.S3.<your file>` and
`Submission.Work.GM.S3.prop71_main` builds: that is the point of the exercise. -/
theorem s3_tail_noclash :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      Summable (fun m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 3} =>
          Submission.GM.Iterm N W m.1) ∧
      ‖Submission.GM.Spart 3 N W -
        (∑ m₁ ∈ Finset.Icc (-⌊(Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)⌋)
                ⌊(Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)⌋,
          ∑ m₂ ∈ Finset.Icc (-⌊(Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)⌋)
                ⌊(Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)⌋,
          ∑ m₃ ∈ Finset.Icc (-⌊(Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)⌋)
                ⌊(Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)⌋,
            (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then Submission.GM.Iterm N W (m₁, m₂, m₃) else 0))‖
        ≤ C * (N : ℝ) ^ (-20 : ℤ) := by
  intro ε δ hε hδ
  -- ## Step 0: the decay exponent `j` and the constants
  set j : ℕ := Nat.ceil (28 / δ) + 2 with hjdef
  obtain ⟨Cj, hCjpos, hdecj⟩ := hhat_decay j
  have hCjnn : 0 ≤ Cj := le_of_lt hCjpos
  have hj2 : 2 ≤ j := by rw [hjdef]; omega
  have hjge : (28 : ℝ) ≤ δ * ((j : ℝ) - 1) := by
    have hceil : (28 : ℝ) / δ ≤ (Nat.ceil (28 / δ) : ℝ) := Nat.le_ceil _
    have hval : (j : ℝ) = (Nat.ceil (28 / δ) : ℝ) + 2 := by rw [hjdef]; push_cast; ring
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have h1 : (28 : ℝ) / δ + 1 ≤ (j : ℝ) - 1 := by rw [hval]; linarith
    have h2 : δ * ((28 : ℝ) / δ + 1) ≤ δ * ((j : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hδ)
    have h3 : δ * ((28 : ℝ) / δ + 1) = 28 + δ := by field_simp
    rw [h3] at h2
    linarith [le_of_lt hδ]
  have hAznn : (0 : ℝ) ≤ Work.GM.Trace.Azero :=
    le_trans (norm_nonneg _) (Work.GM.Trace.hhat_norm_le_Azero 0 0)
  set Kc : ℝ := 24 * 2 ^ (2 * j + 1) * Cj * (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) ^ 2
    with hKcdef
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  refine ⟨1, one_pos, max 32 (Nat.ceil Kc + 1), ?_⟩
  intro N hN W hW hsep
  have hN32 : 32 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNrpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNKc : Kc ≤ (N : ℝ) := by
    have h1 : Nat.ceil Kc + 1 ≤ N := le_trans (le_max_right _ _) hN
    have h2 : Kc ≤ (Nat.ceil Kc : ℝ) := Nat.le_ceil Kc
    have h3 : ((Nat.ceil Kc : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_succ _) h1)
    linarith
  -- the window length `T = M N` and `L = T/N`
  set T : ℝ := M N with hTdef
  have hTval : T = (N : ℝ) ^ (6 / 5 : ℝ) := by rw [hTdef, Submission.LargeValues.M]
  have hT1 : 1 ≤ T := by rw [hTval]; exact Real.one_le_rpow hNr1 (by norm_num)
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  set L : ℝ := T / N with hLdef
  have hLval : L = (N : ℝ) ^ (1 / 5 : ℝ) := by
    rw [hLdef, hTval, show (6 : ℝ) / 5 = 1 + 1 / 5 by norm_num, Real.rpow_add hNrpos,
      Real.rpow_one, mul_div_cancel_left₀ _ (ne_of_gt hNrpos)]
  have hL1 : 1 ≤ L := by rw [hLval]; exact Real.one_le_rpow hNr1 (by norm_num)
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hLT : L ≤ T := by
    rw [hLdef, div_le_iff₀ hNrpos]
    nlinarith [hTpos, hNr1]
  -- `L * T^δ = T^(1+δ)/N ≥ 2`
  have hLTeq : L * T ^ δ = T ^ (1 + δ) / (N : ℝ) := by
    rw [hLdef, div_mul_eq_mul_div]
    rw [show T * T ^ δ = T ^ (1 + δ) by
      have hTT : T * T ^ δ = T ^ (1 : ℝ) * T ^ δ := by rw [Real.rpow_one]
      rw [hTT, ← Real.rpow_add hTpos]]
  have hLTδ : 2 ≤ L * T ^ δ := by
    have h1 : L * T ^ δ = (N : ℝ) ^ (1 / 5 + 6 / 5 * δ) := by
      rw [hLval, hTval, ← Real.rpow_mul hNrpos.le, ← Real.rpow_add hNrpos]
    rw [h1]
    have h2 : (32 : ℝ) ^ (1 / 5 : ℝ) = 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h3 : (32 : ℝ) ^ (1 / 5 : ℝ) ≤ (32 : ℝ) ^ (1 / 5 + 6 / 5 * δ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (32 : ℝ) ^ (1 / 5 + 6 / 5 * δ) ≤ (N : ℝ) ^ (1 / 5 + 6 / 5 * δ) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN32) (by linarith)
    linarith
  have hTeps1 : 1 ≤ T ^ ε := Real.one_le_rpow hT1 (le_of_lt hε)
  have hTepspos : 0 < T ^ ε := lt_of_lt_of_le one_pos hTeps1
  -- the cardinality bound `|W| ≤ T + 1 ≤ 2T`
  have hcardT : (W.card : ℝ) ≤ T + 1 := by
    have h := Commons.Analysis.Sampling.card_le_separated_finset (s := W) (δ := T ^ ε) hTepspos
      (fun x hx y hy hxy => hsep x hx y hy hxy) (a := 0) (b := T) (le_of_lt hTpos)
      (fun x hx => (hW x hx).1) (fun x hx => (hW x hx).2)
    have h2 : (T - 0) / T ^ ε ≤ T := by
      rw [sub_zero, div_le_iff₀ hTepspos]
      nlinarith [hTeps1, hTpos]
    linarith
  have hcard : (W.card : ℝ) ≤ 2 * T := by linarith
  -- `|t - s| ≤ T` for `t, s ∈ W`
  have hsub_le : ∀ t ∈ W, ∀ s ∈ W, |t - s| ≤ T := by
    intro t ht s hs
    have ht' := hW t ht
    have hs' := hW s hs
    rw [abs_le]
    exact ⟨by linarith [ht'.1, hs'.2], by linarith [ht'.2, hs'.1]⟩
  -- ## Step 1: the one-dimensional majorants `φ` (global) and `ψ` (tail)
  set φ : ℤ → ℝ := Work.GM.S3.phiMaj L Work.GM.Trace.Azero (Cj * 2 ^ j * L ^ 2) with hφdef
  set Dt : ℝ := Cj * (2 * L) ^ j with hDtdef
  set ψ : ℤ → ℝ := fun m => Dt / |(m : ℝ)| ^ j with hψdef
  have hDtpos : 0 < Dt := by rw [hDtdef]; positivity
  have hDtnn : 0 ≤ Dt := le_of_lt hDtpos
  have hψval : ∀ m : ℤ, ψ m = Dt / |(m : ℝ)| ^ j := by intro m; rw [hψdef]
  have hDteq : Dt = Cj * (2 * T) ^ j / (N : ℝ) ^ j := by
    have h2 : (2 : ℝ) * (T / (N : ℝ)) = 2 * T / (N : ℝ) := by ring
    rw [hDtdef, hLdef, h2, div_pow, mul_div_assoc]
  have hφnn : ∀ m : ℤ, 0 ≤ φ m := by
    intro m
    rw [hφdef]
    simp only [Work.GM.S3.phiMaj]
    split_ifs
    · exact hAznn
    · positivity
  have hψnn : ∀ m : ℤ, 0 ≤ ψ m := by
    intro m
    rw [hψdef]
    positivity
  have hφdata : Summable φ ∧
      tsum (fun m : ℤ => φ m)
        ≤ (3 * Work.GM.Trace.Azero + 4 * (Cj * 2 ^ j * L ^ 2) / L) * L := by
    have h := Work.GM.S3.phiMaj_sum L Work.GM.Trace.Azero (Cj * 2 ^ j * L ^ 2) hL1 hAznn
      (by positivity)
    rw [hφdef]
    exact h
  have hφS : Summable φ := hφdata.1
  have hφle : tsum (fun m : ℤ => φ m)
      ≤ (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j * L) * L := by
    refine hφdata.2.trans ?_
    have hLeq : 4 * (Cj * 2 ^ j * L ^ 2) / L = 4 * Cj * 2 ^ j * L := by
      field_simp
    rw [hLeq]
  have hφle2 : tsum (fun m : ℤ => φ m) ≤ (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L ^ 2 := by
    refine hφle.trans ?_
    have h3 : (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j * L)
        ≤ (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L := by
      nlinarith [hL1, hAznn, hCjnn]
    calc (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j * L) * L
        ≤ ((3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L) * L :=
          mul_le_mul_of_nonneg_right h3 (le_of_lt hLpos)
      _ = (3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L ^ 2 := by ring
  have hφtsum_nn : 0 ≤ tsum (fun m : ℤ => φ m) := tsum_nonneg (fun m => hφnn m)
  -- the pointwise majorant properties
  have hφ_pw : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ,
      ‖hhat (t - s) ((m : ℝ) * N)‖ ≤ φ m := by
    intro t s ht hs m
    rw [hφdef]
    exact Work.GM.S3.hhat_le_phiMaj j hj2 Cj hCjnn hdecj
      (fun t ξ => Work.GM.Trace.hhat_norm_le_Azero t ξ) hN1 hT1 (hsub_le t ht s hs) m
  have hψ_pw : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ, (0 : ℝ) < |(m : ℝ)| →
      ‖hhat (t - s) ((m : ℝ) * N)‖ ≤ ψ m := by
    intro t s ht hs m hm
    rw [hψval, hDteq]
    have hξ : ((m : ℝ) * N) ≠ 0 := by
      have hm0 : (m : ℝ) ≠ 0 := by
        intro h; rw [h] at hm; simp at hm
      exact mul_ne_zero hm0 (ne_of_gt hNrpos)
    have hdec := hdecj (t - s) ((m : ℝ) * N) hξ
    have h2 : |((m : ℝ) * N)| ^ j = |(m : ℝ)| ^ j * (N : ℝ) ^ j := by
      rw [abs_mul, mul_pow]; simp
    rw [h2] at hdec
    have h1 : (1 + |t - s|) ^ j ≤ (2 * T) ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      have := hsub_le t ht s hs
      linarith
    have hden : (0 : ℝ) < |(m : ℝ)| ^ j * (N : ℝ) ^ j := by positivity
    have hshape : Cj * (2 * T) ^ j / (N : ℝ) ^ j / |(m : ℝ)| ^ j
        = Cj * (2 * T) ^ j / (|(m : ℝ)| ^ j * (N : ℝ) ^ j) := by
      rw [div_div]
      congr 1
      ring
    rw [hshape]
    exact hdec.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 hCjnn) (le_of_lt hden))
  -- ## Step 2: `Iterm` is absolutely summable on `ℤ³`
  have hItermS : Summable (fun m : ℤ × ℤ × ℤ => ‖Iterm N W m‖) :=
    Work.GM.S3.Iterm_summable N W φ hφnn hφS hφ_pw
  have hItermS' : Summable (fun m : ℤ × ℤ × ℤ => Iterm N W m) := hItermS.of_norm
  have hgS : Summable (fun m : ℤ × ℤ × ℤ =>
      Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) m) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_ hItermS
    intro m
    by_cases hm : nzCount m = 3
    · rw [Set.indicator_of_mem (show m ∈ {m : ℤ × ℤ × ℤ | nzCount m = 3} from hm)]
    · rw [Set.indicator_of_notMem (show m ∉ {m : ℤ × ℤ × ℤ | nzCount m = 3} from hm)]
      simp
  -- ## Step 3: the finite part
  set Ki : ℤ := ⌊T ^ (1 + δ) / (N : ℝ)⌋ with hKidef
  set A : Finset (ℤ × ℤ × ℤ) :=
    ((Finset.Icc (-Ki) Ki ×ˢ (Finset.Icc (-Ki) Ki ×ˢ Finset.Icc (-Ki) Ki)).filter
      (fun m : ℤ × ℤ × ℤ => m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0)) with hAdef
  have hKinn : (0 : ℤ) ≤ Ki := by
    rw [hKidef]
    exact Int.floor_nonneg.mpr (by positivity)
  have hP : (∑ m₁ ∈ Finset.Icc (-⌊T ^ (1 + δ) / (N : ℝ)⌋) ⌊T ^ (1 + δ) / (N : ℝ)⌋,
        ∑ m₂ ∈ Finset.Icc (-⌊T ^ (1 + δ) / (N : ℝ)⌋) ⌊T ^ (1 + δ) / (N : ℝ)⌋,
        ∑ m₃ ∈ Finset.Icc (-⌊T ^ (1 + δ) / (N : ℝ)⌋) ⌊T ^ (1 + δ) / (N : ℝ)⌋,
          (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then Iterm N W (m₁, m₂, m₃) else 0))
      = ∑ m ∈ A, Iterm N W m := by
    rw [hAdef, hKidef]
    exact Work.GM.S3.finite_part_reindex N W ⌊T ^ (1 + δ) / (N : ℝ)⌋
  have hAeq : ∑ m ∈ A, Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) m
      = ∑ m ∈ A, Iterm N W m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hAdef] at hm
    simp only [Finset.mem_filter, Finset.mem_product] at hm
    exact Set.indicator_of_mem
      (show m ∈ {m : ℤ × ℤ × ℤ | nzCount m = 3} from
        nzCount_eq_three hm.2.1 hm.2.2.1 hm.2.2.2)
      (Iterm N W)
  have hdiff : Spart 3 N W - ∑ m ∈ A, Iterm N W m
      = ∑' x : {x : ℤ × ℤ × ℤ // x ∉ A},
          Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) x := by
    have h := hgS.sum_add_tsum_subtype_compl A
    rw [hAeq] at h
    rw [Spart_eq_tsum_indicator, sub_eq_iff_eq_add, add_comm]
    exact h.symm
  -- ## Step 4: the tail sum over `ℤ³`
  set ψtail : ℝ := tsum (fun a : ℤ => if (Ki : ℝ) < |(a : ℝ)| then ψ a else 0) with hψtaildef
  set F : ℤ × ℤ × ℤ → ℝ := fun m =>
      (if (Ki : ℝ) < |(m.1 : ℝ)| ∨ (Ki : ℝ) < |(m.2.1 : ℝ)| ∨ (Ki : ℝ) < |(m.2.2 : ℝ)|
        then ‖Iterm N W m‖ else 0) with hFdef
  set tt : ℝ := tsum F with httdef
  have hKi2 : L * T ^ δ / 2 ≤ (Ki : ℝ) := by
    rw [hKidef, ← hLTeq]
    have hfl := Int.lt_floor_add_one (L * T ^ δ)
    have hfl' : L * T ^ δ < ((⌊L * T ^ δ⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast hfl
    linarith
  have hKi_ge : 1 ≤ (Ki : ℝ) := by linarith [hKi2, hLTδ]
  have hKi_pos : 0 < (Ki : ℝ) := lt_of_lt_of_le one_pos hKi_ge
  have hψS : Summable (fun m : ℤ => if (Ki : ℝ) < |(m : ℝ)| then Dt / |(m : ℝ)| ^ j else 0) :=
    (Work.GM.S3.tail_pseries j hj2 Dt (Ki : ℝ) hDtnn hKi_ge).1
  have hψS' : Summable (fun m : ℤ => if (Ki : ℝ) < |(m : ℝ)| then ψ m else 0) := by
    rw [hψdef]
    exact hψS
  have hψp : ∀ (t s : ℝ), t ∈ W → s ∈ W → ∀ m : ℤ, (Ki : ℝ) < |(m : ℝ)| →
      ‖hhat (t - s) ((m : ℝ) * N)‖ ≤ ψ m := by
    intro t s ht hs m hm
    refine hψ_pw t s ht hs m ?_
    linarith [show (0 : ℝ) ≤ (Ki : ℝ) by positivity]
  have htailS : Summable F := by
    rw [hFdef]
    exact (Work.GM.S3.nc_tsum_tail_Iterm N W φ ψ (Ki : ℝ) hφnn hψnn hφS hψS' hφ_pw hψp).1
  have htailbound : tt ≤ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * ψtail
      * (tsum (fun b : ℤ => φ b)) ^ 2 := by
    have h := (Work.GM.S3.nc_tsum_tail_Iterm N W φ ψ (Ki : ℝ) hφnn hψnn hφS hψS' hφ_pw hψp).2
    rw [httdef, hFdef, hψtaildef]
    exact h
  -- ## Step 5: the complement of `A` is bounded by the tail sum
  have htail_of_notmem : ∀ m : ℤ × ℤ × ℤ, m ∉ A → nzCount m = 3 →
      ((Ki : ℝ) < |(m.1 : ℝ)| ∨ (Ki : ℝ) < |(m.2.1 : ℝ)| ∨ (Ki : ℝ) < |(m.2.2 : ℝ)|) := by
    intro m hmA h3
    rw [hAdef] at hmA
    simp only [Finset.mem_filter, Finset.mem_product, not_and_or] at hmA
    have h1 := (nzCount_eq_three_iff.mp h3).1
    have h2 := (nzCount_eq_three_iff.mp h3).2.1
    have h4 := (nzCount_eq_three_iff.mp h3).2.2
    rcases hmA with (h | h | h) | (h | h | h)
    · exact Or.inl (lt_abs_of_notMem_Icc hKinn h)
    · exact Or.inr (Or.inl (lt_abs_of_notMem_Icc hKinn h))
    · exact Or.inr (Or.inr (lt_abs_of_notMem_Icc hKinn h))
    · exact absurd h1 h
    · exact absurd h2 h
    · exact absurd h4 h
  have hpt : ∀ (m : ℤ × ℤ × ℤ) (_ : m ∉ A),
      ‖Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) m‖ ≤ F m := by
    intro m hm
    change ‖Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) m‖
      ≤ (if (Ki : ℝ) < |(m.1 : ℝ)| ∨ (Ki : ℝ) < |(m.2.1 : ℝ)| ∨ (Ki : ℝ) < |(m.2.2 : ℝ)|
          then ‖Iterm N W m‖ else 0)
    by_cases h3 : nzCount m = 3
    · rw [Set.indicator_of_mem (show m ∈ {m : ℤ × ℤ × ℤ | nzCount m = 3} from h3),
        if_pos (htail_of_notmem m hm h3)]
    · rw [Set.indicator_of_notMem (show m ∉ {m : ℤ × ℤ × ℤ | nzCount m = 3} from h3),
        norm_zero]
      split_ifs <;> positivity
  have hcompl : ‖∑' x : {x : ℤ × ℤ × ℤ // x ∉ A},
      Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) x‖ ≤ tt := by
    have hsub : Summable (fun x : {x : ℤ × ℤ × ℤ // x ∉ A} =>
        Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) x) := hgS.subtype _
    have h1 : ‖∑' x : {x : ℤ × ℤ × ℤ // x ∉ A},
        Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) x‖
        ≤ ∑' x : {x : ℤ × ℤ × ℤ // x ∉ A},
            ‖Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) x‖ :=
      norm_tsum_le_tsum_norm hsub.norm
    have h2 : ∑' x : {x : ℤ × ℤ × ℤ // x ∉ A},
        ‖Set.indicator {m : ℤ × ℤ × ℤ | nzCount m = 3} (Iterm N W) x‖
        ≤ ∑' x : {x : ℤ × ℤ × ℤ // x ∉ A}, F x.1 :=
      Summable.tsum_le_tsum (fun x => hpt x.1 x.2) hsub.norm (htailS.subtype _)
    have h3 := Summable.tsum_subtype_le F {x : ℤ × ℤ × ℤ | x ∉ A}
        (fun m => by positivity) htailS
    refine h1.trans (h2.trans ?_)
    rw [httdef]
    exact h3
  -- ## Step 6: the bound on the tail sum of `ψ`
  have hψtail_le : ψtail ≤ 2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))) := by
    rw [hψtaildef]
    refine (Work.GM.S3.tail_pseries j hj2 Dt (Ki : ℝ) hDtnn hKi_ge).2.trans ?_
    rw [hDtdef]
    exact Work.GM.S3.psi_tail_arith Cj L T (Ki : ℝ) δ j hj2 hCjnn hLpos hT1 hδ hKi2
  -- ## Step 7: the numeric conclusion
  have hfinal : ‖Spart 3 N W - ∑ m ∈ A, Iterm N W m‖ ≤ (N : ℝ) ^ (-20 : ℤ) := by
    have hA0 : ‖Spart 3 N W - ∑ m ∈ A, Iterm N W m‖ ≤ tt := by
      rw [hdiff]; exact hcompl
    have hstep : tt ≤ 3 * (N : ℝ) ^ 3 * (2 * T) ^ 3
        * (2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))))
        * ((3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L ^ 2) ^ 2 := by
      refine htailbound.trans ?_
      have h1 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 := pow_le_pow_left₀ (by positivity) hcard 3
      have h3 : (tsum (fun b : ℤ => φ b)) ^ 2
          ≤ ((3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L ^ 2) ^ 2 :=
        pow_le_pow_left₀ hφtsum_nn hφle2 2
      have hψpos : 0 ≤ 2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))) := by positivity
      calc 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * ψtail * (tsum (fun b : ℤ => φ b)) ^ 2
          ≤ 3 * (N : ℝ) ^ 3 * (2 * T) ^ 3 * ψtail * (tsum (fun b : ℤ => φ b)) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 3 * (N : ℝ) ^ 3 * (2 * T) ^ 3
              * (2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))))
              * (tsum (fun b : ℤ => φ b)) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact hψtail_le
        _ ≤ 3 * (N : ℝ) ^ 3 * (2 * T) ^ 3
              * (2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))))
              * ((3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    refine hA0.trans (hstep.trans ?_)
    have hid : 3 * (N : ℝ) ^ 3 * (2 * T) ^ 3
        * (2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))))
        * ((3 * Work.GM.Trace.Azero + 4 * Cj * 2 ^ j) * L ^ 2) ^ 2
        = Kc * (N : ℝ) ^ 3 * T ^ 3 * L ^ 5 * T ^ (-(δ * ((j : ℝ) - 1))) := by
      rw [hKcdef]
      ring
    exact Work.GM.S3.final_rpow_bound N Kc T L δ j _ hN1 hNKc hTval hLpos hLT hjge (le_of_eq hid)
  refine ⟨hItermS'.subtype _, ?_⟩
  rw [hP, one_mul]
  exact hfinal


end Work.GM.S3
