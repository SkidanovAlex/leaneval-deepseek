import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.s3RemPlus_cutfree_defs
import Submission.Work.FIChain.remainder_all_at_07
import Submission.Work.FIChain.cfRsum_le
import Submission.Work.FIChain.cfPairs_le

namespace Work.FIChain

open Finset

/-- `Σ_{ℓ ∣ ζ} τ(ℓ)² ≤ τ(ζ)^5`: the `K = 2, K + 1 = 3 ≤ 5` case of
`Submission.ASP.sum_divisors_card_pow_le`, transported to `ℝ`. -/
lemma sum_divisors_card_sq_le_pt (ζ : ℕ) :
    (∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2) ≤ ((ζ.divisors.card : ℝ)) ^ 5 := by
  have h := Submission.ASP.sum_divisors_card_pow_le 2 ζ
  have h35 : ((ζ.divisors.card : ℝ)) ^ 3 ≤ ((ζ.divisors.card : ℝ)) ^ 5 := by
    rcases Nat.eq_zero_or_pos ζ.divisors.card with h0 | hpos
    · rw [h0]; norm_num
    · exact pow_le_pow_right₀
        (by exact_mod_cast (show 1 ≤ ζ.divisors.card by omega)) (by norm_num)
  calc (∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2)
      = (((∑ ℓ ∈ ζ.divisors, (ℓ.divisors.card) ^ 2) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl (fun ℓ _ => (Nat.cast_pow _ _).symm)
    _ ≤ ((ζ.divisors.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
    _ = ((ζ.divisors.card : ℝ)) ^ 3 := by rw [Nat.cast_pow]
    _ ≤ ((ζ.divisors.card : ℝ)) ^ 5 := h35

/-- **The `(R′)`-weighted fibre bound for the `λ⁺` remainder** (the pointwise-in-`(v,t)` step of the
companion's (8.4)).

For every `x ≥ X₀`, every modulus cutoff `N ≤ ⌈x^{7/10}⌉` and every pair of scales
`m₁, m₂ ≤ x`, and every weight `w` with `0 ≤ w ℓ ≤ τ(ℓ)²`:

    Σ_{ℓ ≤ x} Σ_{d ≤ x, ℓ·d ≤ N} w(ℓ)·(|r̃(ℓd, m₁)| + |r̃(ℓd, m₂)|)
        ≤ 2·Ã(x)·(log x)^{-3}.

Grouping the `(ℓ,d)`-pairs by `ζ = ℓ·d`: `Σ_{ℓ | ζ} τ(ℓ)² ≤ τ(ζ)^5`
(`Submission.ASP.sum_divisors_card_pow_le`), so the left side is at most
`Σ_{ζ ≤ N} τ(ζ)^5 (|r̃(ζ,m₁)| + |r̃(ζ,m₂)|)`, and each of the two sums is
`≤ Ã(x)(log x)^{-3}` by `(R′)` (`Work.FIChain.cfRsum_le`, from
`Work.FIChain.remainder_all_at_07`).  `Work.FIChain.cfR ζ m = rtildeFull FIr FIg FIgtil FIa ζ m`.
`Work.FIChain.cfPairs_le` (proved) already gives the `(ℓ,d) → ζ` step. -/
theorem s3Rem_fibre_pt_le :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ N m₁ m₂ : ℕ,
      N ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ → m₁ ≤ x → m₂ ≤ x →
      ∀ w : ℕ → ℝ, (∀ ℓ : ℕ, 0 ≤ w ℓ) →
        (∀ ℓ : ℕ, w ℓ ≤ ((ℓ.divisors.card : ℝ)) ^ 2) →
      (∑ ℓ ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x,
          (if ℓ * d ≤ N then w ℓ *
            (|Work.FIChain.cfR (ℓ * d) m₁| + |Work.FIChain.cfR (ℓ * d) m₂|) else 0))
        ≤ 2 * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℤ)) := by
  obtain ⟨Xr, hr⟩ := cfRsum_le
  refine ⟨max Xr 1, fun x hx N m₁ m₂ hN hm1 hm2 w hw0 hw2 => ?_⟩
  have hxr : Xr ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  -- The cutoff `N` is below `x` as well.
  have hNx : N ≤ x := by
    refine le_trans hN (Nat.ceil_le.mpr ?_)
    calc (x : ℝ) ^ ((7 : ℝ) / 10) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  -- ## Step 1: group the `(ℓ,d)`-pairs by `ζ = ℓ·d`.
  have hgroup : (∑ ℓ ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x,
        (if ℓ * d ≤ N then w ℓ * (|cfR (ℓ * d) m₁| + |cfR (ℓ * d) m₂|) else 0))
      ≤ ∑ ζ ∈ Finset.Icc 1 N, (∑ ℓ ∈ ζ.divisors, w ℓ) *
          (|cfR ζ m₁| + |cfR ζ m₂|) := by
    have h := cfPairs_le x x N w (fun ζ => |cfR ζ m₁| + |cfR ζ m₂|) hw0
      (fun n => by positivity) hNx hNx
    rw [Finset.sum_product] at h
    exact h
  refine le_trans hgroup ?_
  -- ## Step 2: bound `Σ_{ℓ ∣ ζ} w ℓ ≤ Σ_{ℓ ∣ ζ} τ(ℓ)² ≤ τ(ζ)^5`.
  have hfib : ∑ ζ ∈ Finset.Icc 1 N, (∑ ℓ ∈ ζ.divisors, w ℓ) *
        (|cfR ζ m₁| + |cfR ζ m₂|)
      ≤ ∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 *
          (|cfR ζ m₁| + |cfR ζ m₂|) := by
    refine Finset.sum_le_sum (fun ζ _ => mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc (∑ ℓ ∈ ζ.divisors, w ℓ)
        ≤ ∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2 :=
          Finset.sum_le_sum (fun ℓ _ => hw2 ℓ)
      _ ≤ ((ζ.divisors.card : ℝ)) ^ 5 := sum_divisors_card_sq_le_pt ζ
  refine le_trans hfib ?_
  -- ## Step 3: split into the `m₁`- and `m₂`-sums and apply `(R′)` to each.
  have hsplit : ∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 *
        (|cfR ζ m₁| + |cfR ζ m₂|)
      = (∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m₁|)
        + (∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m₂|) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ζ _ => mul_add _ _ _)
  rw [hsplit]
  have h1 := hr x hxr N m₁ hN hm1
  have h2 := hr x hxr N m₂ hN hm2
  have hexp : (Real.log (x : ℝ)) ^ (-(3 : ℤ)) = (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_intCast (Real.log (x : ℝ)) (-3)]
    norm_num
  rw [hexp]
  calc (∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m₁|)
        + (∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m₂|)
      ≤ AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ))
          + AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := add_le_add h1 h2
    _ = 2 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by ring

end Work.FIChain
