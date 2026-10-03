/-
# `Work.FIChain.RhoWin2TauGrouping4`

Grouping the double sum `Σ_{b ∈ S} τ(b) · Σ_{m ≤ x} τ(m)² |f (m b)|` by the value `c = m b`,
we show it is dominated by `Σ_{c ≤ x} τ(c)⁴ |f c|`.

For each `c ≤ x` the contributing pairs are `(b, m)` with `b ∈ S`, `b ∣ c`, `m = c / b`, and

  `Σ_{b ∈ S, b | c} τ(b)·τ(c/b)² ≤ #{b | c} · τ(c)³ ≤ τ(c) · τ(c)³ = τ(c)⁴`,

using only that the relevant `b ≤ c` are divisors of `c` (so at most `τ(c)` of them) and that
`b | c` implies `τ(b) ≤ τ(c)` and `τ(c/b) ≤ τ(c)`.  No squarefreeness of `b` is needed.

This is the `τ(b)`-weighted variant of `Work.FIChain.tau_grouping_abstract`.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Combinatorial core: for any finite set `S` of positive integers and any `c ≠ 0`,
`Σ_{b ∈ S, b | c} τ(b)·τ(c/b)² ≤ τ(c)⁴`. -/
lemma tau_sum_le_four (c : ℕ) (hc : c ≠ 0) (S : Finset ℕ) (hS : ∀ b ∈ S, 0 < b) :
    (∑ b ∈ S.filter (fun b => b ∣ c),
        ((b.divisors.card : ℝ)) * ((c / b).divisors.card : ℝ) ^ 2)
      ≤ ((c.divisors.card : ℝ)) ^ 4 := by
  have hle : ∀ b ∈ S.filter (fun b => b ∣ c),
      ((b.divisors.card : ℝ)) * ((c / b).divisors.card : ℝ) ^ 2
        ≤ ((c.divisors.card : ℝ)) ^ 3 := by
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbS, hbc⟩ := hb
    have hbdvd : b.divisors ⊆ c.divisors := Nat.divisors_subset_of_dvd hc hbc
    have hbcard : ((b.divisors.card : ℝ)) ≤ (c.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hbdvd
    have hdiv : c / b ∣ c :=
      ⟨b, by rw [Nat.mul_comm (c / b) b]; exact (Nat.mul_div_cancel' hbc).symm⟩
    have hsub : (c / b).divisors ⊆ c.divisors := Nat.divisors_subset_of_dvd hc hdiv
    have hcard : ((c / b).divisors.card : ℝ) ≤ (c.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h1 : (0 : ℝ) ≤ ((c / b).divisors.card : ℝ) := by positivity
    have h2 : ((c / b).divisors.card : ℝ) ^ 2 ≤ ((c.divisors.card : ℝ)) ^ 2 :=
      pow_le_pow_left₀ h1 hcard 2
    have h3 : ((b.divisors.card : ℝ)) * ((c / b).divisors.card : ℝ) ^ 2
        ≤ ((c.divisors.card : ℝ)) * ((c.divisors.card : ℝ)) ^ 2 :=
      mul_le_mul hbcard h2 (by positivity) (by positivity)
    calc ((b.divisors.card : ℝ)) * ((c / b).divisors.card : ℝ) ^ 2
        ≤ ((c.divisors.card : ℝ)) * ((c.divisors.card : ℝ)) ^ 2 := h3
      _ = ((c.divisors.card : ℝ)) ^ 3 := by ring
  have hsub : S.filter (fun b => b ∣ c) ⊆ c.divisors := by
    intro b hb
    rw [Finset.mem_filter] at hb
    exact Nat.mem_divisors.mpr ⟨hb.2, hc⟩
  have hcard : ((S.filter (fun b => b ∣ c)).card : ℝ) ≤ (c.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc (∑ b ∈ S.filter (fun b => b ∣ c),
          ((b.divisors.card : ℝ)) * ((c / b).divisors.card : ℝ) ^ 2)
      ≤ ∑ b ∈ S.filter (fun b => b ∣ c), ((c.divisors.card : ℝ)) ^ 3 := Finset.sum_le_sum hle
    _ = ((S.filter (fun b => b ∣ c)).card : ℝ) * ((c.divisors.card : ℝ)) ^ 3 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((c.divisors.card : ℝ)) * ((c.divisors.card : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((c.divisors.card : ℝ)) ^ 4 := by ring

theorem RhoWin2TauGrouping4 (S : Finset ℕ) (hS : ∀ b ∈ S, 0 < b) (f : ℕ → ℝ) (x : ℕ)
    (hf : ∀ c : ℕ, x < c → f c = 0) :
    (∑ b ∈ S, ((b.divisors.card : ℝ)) * ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
      ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 4 * |f c| := by
  have key0 : ∀ b ∈ S,
      (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
        = ∑ c ∈ (Finset.Icc 1 x).filter (fun c => b ∣ c),
            ((c / b).divisors.card : ℝ) ^ 2 * |f c| := by
    intro b hb
    have hb0 : 0 < b := hS b hb
    calc (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
        = ∑ m ∈ (Finset.Icc 1 x).filter (fun m => m * b ≤ x),
            ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)| := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          by_cases h : m * b ≤ x
          · simp [h]
          · simp only [h, if_false]
            rw [hf (m * b) (Nat.lt_of_not_le h), abs_zero, mul_zero]
      _ = ∑ c ∈ (Finset.Icc 1 x).filter (fun c => b ∣ c),
            ((c / b).divisors.card : ℝ) ^ 2 * |f c| := by
          refine Finset.sum_bij (fun m _ => m * b) ?_ ?_ ?_ ?_
          · rintro m hm
            rw [Finset.mem_filter] at hm ⊢
            obtain ⟨hmI, hmb⟩ := hm
            have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
            have hmx : m ≤ x := (Finset.mem_Icc.mp hmI).2
            exact ⟨Finset.mem_Icc.mpr
                ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hmb⟩,
              ⟨m, Nat.mul_comm m b⟩⟩
          · rintro m₁ _ m₂ _ h
            exact Nat.eq_of_mul_eq_mul_right hb0 h
          · rintro c hc
            rw [Finset.mem_filter] at hc
            obtain ⟨hcI, hbc⟩ := hc
            have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcI).1
            have hcx : c ≤ x := (Finset.mem_Icc.mp hcI).2
            have hbc' : b * (c / b) = c := Nat.mul_div_cancel' hbc
            have hne : c / b ≠ 0 := by
              intro hz
              rw [hz, mul_zero] at hbc'
              omega
            refine ⟨c / b, ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨Finset.mem_Icc.mpr
                  ⟨Nat.one_le_iff_ne_zero.mpr hne, (Nat.div_le_self c b).trans hcx⟩,
                by rw [mul_comm, hbc']; exact hcx⟩
            · rw [mul_comm]; exact hbc'
          · intro m _
            rw [Nat.mul_div_cancel m hb0]
  have key : ∀ b ∈ S,
      ((b.divisors.card : ℝ)) * (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
        = ∑ c ∈ (Finset.Icc 1 x).filter (fun c => b ∣ c),
            ((b.divisors.card : ℝ)) * (((c / b).divisors.card : ℝ) ^ 2) * |f c| := by
    intro b hb
    rw [key0 b hb, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  calc (∑ b ∈ S, ((b.divisors.card : ℝ)) *
          ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
      = ∑ b ∈ S, ∑ c ∈ (Finset.Icc 1 x).filter (fun c => b ∣ c),
          ((b.divisors.card : ℝ)) * (((c / b).divisors.card : ℝ) ^ 2) * |f c| :=
        Finset.sum_congr rfl key
    _ = ∑ c ∈ Finset.Icc 1 x, ∑ b ∈ S.filter (fun b => b ∣ c),
          ((b.divisors.card : ℝ)) * (((c / b).divisors.card : ℝ) ^ 2) * |f c| := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 4 * |f c| := by
        refine Finset.sum_le_sum (fun c hcc => ?_)
        have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcc).1
        have hc0 : c ≠ 0 := by omega
        have hbound := tau_sum_le_four c hc0 S hS
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

end

end Work.FIChain
