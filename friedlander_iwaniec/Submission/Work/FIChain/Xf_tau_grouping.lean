/-
# `Work.FIChain.Xf_tau_grouping`

Grouping the double sum `Σ_{b₁ | Π, b₁ ≤ D} Σ_{m ≤ x} τ(m)² |Xf (m b₁)|` by the value
`c = m b₁`, we show it is dominated by `Σ_{c ≤ x} τ(c)³ |Xf c|`.

The point is that for each `c ≤ x` the contributing pairs are `(b₁, m)` with `m = c / b₁`,
and

  `Σ_{b₁ | Π, b₁ | c} τ(c/b₁)² ≤ #{b₁ | c} · τ(c)² ≤ τ(c) · τ(c)² = τ(c)³`,

using only that the relevant `b₁ ≤ c` are divisors of `c` (so at most `τ(c)` of them) and that
`b₁ | c` implies `τ(c/b₁) ≤ τ(c)`.  No squarefreeness of `Π` is needed.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `Π`-restricted window sum `Xf x Pz c u` vanishes as soon as `c > x`
(then the window `cn ≤ x` contains no `n ≥ 1`). -/
lemma Xf_eq_zero_of_lt (x Pz c : ℕ) (u : ℝ) (h : x < c) : Xf x Pz c u = 0 := by
  rw [Xf]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnI, hcn, _⟩ := hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  have hc : c ≤ c * n := by
    calc c = c * 1 := (Nat.mul_one c).symm
      _ ≤ c * n := Nat.mul_le_mul_left c hn1
  omega

/-- Combinatorial core: for any finite set `S` of positive integers and any `c ≠ 0`,
`Σ_{b ∈ S, b | c} τ(c/b)² ≤ τ(c)³`. -/
lemma tau_sum_le (c : ℕ) (hc : c ≠ 0) (S : Finset ℕ) (hS : ∀ b ∈ S, 0 < b) :
    (∑ b ∈ S.filter (fun b => b ∣ c), ((c / b).divisors.card : ℝ) ^ 2)
      ≤ ((c.divisors.card : ℝ)) ^ 3 := by
  have hle : ∀ b ∈ S.filter (fun b => b ∣ c),
      ((c / b).divisors.card : ℝ) ^ 2 ≤ ((c.divisors.card : ℝ)) ^ 2 := by
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbS, hbc⟩ := hb
    have hb0 : 0 < b := hS b hbS
    have hdiv : c / b ∣ c :=
      ⟨b, by rw [Nat.mul_comm (c / b) b]; exact (Nat.mul_div_cancel' hbc).symm⟩
    have hsub : (c / b).divisors ⊆ c.divisors := Nat.divisors_subset_of_dvd hc hdiv
    have hcard : (c / b).divisors.card ≤ c.divisors.card := Finset.card_le_card hsub
    have hcardR : ((c / b).divisors.card : ℝ) ≤ (c.divisors.card : ℝ) := by
      exact_mod_cast hcard
    have h1 : (0 : ℝ) ≤ ((c / b).divisors.card : ℝ) := by positivity
    exact pow_le_pow_left₀ h1 hcardR 2
  have hsub : S.filter (fun b => b ∣ c) ⊆ c.divisors := by
    intro b hb
    rw [Finset.mem_filter] at hb
    exact Nat.mem_divisors.mpr ⟨hb.2, hc⟩
  have hcard : ((S.filter (fun b => b ∣ c)).card : ℝ) ≤ (c.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc (∑ b ∈ S.filter (fun b => b ∣ c), ((c / b).divisors.card : ℝ) ^ 2)
      ≤ ∑ b ∈ S.filter (fun b => b ∣ c), ((c.divisors.card : ℝ)) ^ 2 := Finset.sum_le_sum hle
    _ = ((S.filter (fun b => b ∣ c)).card : ℝ) * ((c.divisors.card : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((c.divisors.card : ℝ)) * ((c.divisors.card : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((c.divisors.card : ℝ)) ^ 3 := by ring

/-- Abstract grouping lemma: for a finite family of positive weights `b ∈ S` and any `f`
vanishing beyond `x`, `Σ_{b ∈ S} Σ_{m ≤ x} τ(m)² |f (m b)| ≤ Σ_{c ≤ x} τ(c)³ |f c|`. -/
lemma tau_grouping_abstract (S : Finset ℕ) (hS : ∀ b ∈ S, 0 < b) (f : ℕ → ℝ) (x : ℕ)
    (hf : ∀ c, x < c → f c = 0) :
    (∑ b ∈ S, ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
      ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |f c| := by
  have key : ∀ b ∈ S,
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
  calc (∑ b ∈ S, ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |f (m * b)|)
      = ∑ b ∈ S, ∑ c ∈ (Finset.Icc 1 x).filter (fun c => b ∣ c),
          ((c / b).divisors.card : ℝ) ^ 2 * |f c| := Finset.sum_congr rfl key
    _ = ∑ c ∈ Finset.Icc 1 x, ∑ b ∈ S.filter (fun b => b ∣ c),
          ((c / b).divisors.card : ℝ) ^ 2 * |f c| := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |f c| := by
        refine Finset.sum_le_sum (fun c hcc => ?_)
        have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcc).1
        have hc0 : c ≠ 0 := by omega
        have hbound := tau_sum_le c hc0 S hS
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

theorem Xf_tau_grouping (x Pz : ℕ) (D u : ℝ) :
    (∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => (b₁ : ℝ) ≤ D),
        ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 * |Work.FIChain.Xf x Pz (m * b₁) u|)
      ≤ ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 3 * |Work.FIChain.Xf x Pz c u| := by
  refine tau_grouping_abstract _ ?_ (fun c => Xf x Pz c u) x ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact Nat.pos_of_mem_divisors hb.1
  · intro c hc
    exact Xf_eq_zero_of_lt x Pz c u hc

end

end Work.FIChain
