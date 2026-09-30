import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset
open scoped BigOperators

/-- Splitting `∑_{n=1}^{N} g n` at the point `h+1` and again at `h+N-L+1`, written with
half-open intervals (`Finset.Ico`), the middle piece being the one that reindexes to a window
`g(n+h)`. -/
private lemma split3 (g : ℕ → ℂ) (h L N : ℕ) (hh : h ≤ L) (hLN : L ≤ N) :
    ∑ n ∈ Icc 1 N, g n
      = (∑ n ∈ Ico 1 (h+1), g n) + (∑ n ∈ Ico (h+1) (h+N-L+1), g n)
        + (∑ n ∈ Ico (h+N-L+1) (N+1), g n) := by
  rw [← Ico_succ_right_eq_Icc 1 N]
  change ∑ n ∈ Ico 1 (N+1), g n = _
  have h1 : 1 ≤ h + 1 := by omega
  have h2 : h + 1 ≤ h + N - L + 1 := by omega
  have h3 : h + N - L + 1 ≤ N + 1 := by omega
  rw [← sum_Ico_consecutive g h1 (show h + 1 ≤ N + 1 by omega),
    ← sum_Ico_consecutive g h2 h3]
  ring

/-- The middle piece of `split3` is the shifted window `∑_{n=1}^{N-L} g (n+h)`. -/
private lemma mid (g : ℕ → ℂ) (h L N : ℕ) (_hh : h ≤ L) (hLN : L ≤ N) :
    (∑ n ∈ Ico (h+1) (h+N-L+1), g n) = ∑ n ∈ Icc 1 (N-L), g (n+h) := by
  have e1 : Ico (h+1) (h+N-L+1) = Ico (1+h) (N-L+1+h) := by
    congr 1 <;> omega
  rw [e1, ← sum_Ico_add g 1 (N-L+1) h]
  have hI : Ico 1 (N-L+1) = Icc 1 (N-L) := Ico_succ_right_eq_Icc 1 (N-L)
  rw [hI]
  apply sum_congr rfl
  intro x hx
  rw [add_comm]

/-- **Averaging a sequence over a shift.**  For `1 ≤ L ≤ N`, `g : ℕ → ℂ` with `‖g n‖ ≤ 1` for all
`n`,
`‖Σ_{n=1}^{N} g n‖ ≤ L⁻¹ Σ_{n=1}^{N-L} ‖Σ_{h=1}^{L} g(n+h)‖ + 2L`.

Suggested route: `L · Σ_{n ≤ N} g n = Σ_{h=1}^{L} Σ_{m=1}^{N} g m`, and for each `h ∈ [1,L]` split
`Σ_{m=1}^{N} g m = Σ_{m=h+1}^{N} g m + Σ_{m=1}^{h} g m`, where the first sum reindexes to
`Σ_{n=1}^{N-h} g (n+h)`.  Comparing with `Σ_{n=1}^{N-L} Σ_{h=1}^{L} g(n+h) = Σ_{h=1}^{L} Σ_{n=1}^{N-L} g(n+h)`
costs at most `Σ_{h=1}^{L}(L-h) = L(L-1)/2` (the `Finset.sum_sdiff` of
`Icc 1 (N-L) ⊆ Icc 1 (N-h)` has at most `L-h` elements), and the leftover
`Σ_{h=1}^{L} Σ_{m=1}^{h} g m` is bounded by `Σ_{h=1}^{L} h = L(L+1)/2` because `‖g m‖ ≤ 1`.  Hence
`L‖Σ g‖ ≤ Σ_{n}‖Σ_h g(n+h)‖ + 2L²`, and divide by `L > 0`. -/
theorem averaging_bound {L N : ℕ} (hL : 1 ≤ L) (hLN : L ≤ N) (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 N, g n‖
      ≤ ((L:ℝ))⁻¹ * (∑ n ∈ Finset.Icc 1 (N - L), ‖∑ h ∈ Finset.Icc 1 L, g (n + h)‖)
        + 2 * (L:ℝ) := by
  -- For each `h ∈ [1,L]`, the full sum splits into three pieces: the part below `h+1`, the
  -- shifted window, and the tail from `h+N-L+1` on.
  have hperH : ∀ h ∈ Icc 1 L,
      (∑ n ∈ Icc 1 N, g n)
        = (∑ n ∈ Ico 1 (h+1), g n) + (∑ n ∈ Icc 1 (N-L), g (n+h))
          + (∑ n ∈ Ico (h+N-L+1) (N+1), g n) := by
    intro h hh
    have hhL : h ≤ L := (mem_Icc.mp hh).2
    rw [split3 g h L N hhL hLN, mid g h L N hhL hLN]
  -- The average of the full sum over `h ∈ [1,L]` is `L` times the full sum.
  have hconst : (L:ℂ) * (∑ n ∈ Icc 1 N, g n) = ∑ h ∈ Icc 1 L, (∑ n ∈ Icc 1 N, g n) := by
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  have hdecomp : ∑ h ∈ Icc 1 L, (∑ n ∈ Icc 1 N, g n)
      = (∑ h ∈ Icc 1 L, ∑ n ∈ Ico 1 (h+1), g n)
        + (∑ h ∈ Icc 1 L, ∑ n ∈ Icc 1 (N-L), g (n+h))
        + (∑ h ∈ Icc 1 L, ∑ n ∈ Ico (h+N-L+1) (N+1), g n) := by
    rw [sum_congr rfl hperH, sum_add_distrib, sum_add_distrib]
  -- Swapping the two sums in the middle term produces the desired right-hand side.
  have hBswap : (∑ h ∈ Icc 1 L, ∑ n ∈ Icc 1 (N-L), g (n+h))
      = ∑ n ∈ Icc 1 (N-L), ∑ h ∈ Icc 1 L, g (n+h) := Finset.sum_comm
  -- The two error terms each have at most `L` unit-bounded summands per `h`, hence norm `≤ L²`.
  have hA : ‖∑ h ∈ Icc 1 L, ∑ n ∈ Ico 1 (h+1), g n‖ ≤ (L:ℝ) * L := by
    calc ‖∑ h ∈ Icc 1 L, ∑ n ∈ Ico 1 (h+1), g n‖
        ≤ ∑ h ∈ Icc 1 L, ‖∑ n ∈ Ico 1 (h+1), g n‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Icc 1 L, (∑ n ∈ Ico 1 (h+1), (1:ℝ)) := by
            apply sum_le_sum; intro h hh
            exact le_trans (norm_sum_le _ _) (by apply sum_le_sum; intro n hn; exact hg n)
      _ ≤ ∑ h ∈ Icc 1 L, (L:ℝ) := by
            apply sum_le_sum; intro h hh
            have hhL : h ≤ L := (mem_Icc.mp hh).2
            have hc : (∑ n ∈ Ico 1 (h+1), (1:ℝ)) = ((Ico 1 (h+1)).card : ℝ) := by simp
            rw [hc, Nat.card_Ico]
            have : (h + 1 - 1 : ℕ) ≤ L := by omega
            exact_mod_cast this
      _ = (L:ℝ) * L := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
            simp
  have hC : ‖∑ h ∈ Icc 1 L, ∑ n ∈ Ico (h+N-L+1) (N+1), g n‖ ≤ (L:ℝ) * L := by
    calc ‖∑ h ∈ Icc 1 L, ∑ n ∈ Ico (h+N-L+1) (N+1), g n‖
        ≤ ∑ h ∈ Icc 1 L, ‖∑ n ∈ Ico (h+N-L+1) (N+1), g n‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Icc 1 L, (∑ n ∈ Ico (h+N-L+1) (N+1), (1:ℝ)) := by
            apply sum_le_sum; intro h hh
            exact le_trans (norm_sum_le _ _) (by apply sum_le_sum; intro n hn; exact hg n)
      _ ≤ ∑ h ∈ Icc 1 L, (L:ℝ) := by
            apply sum_le_sum; intro h hh
            have hhL : h ≤ L := (mem_Icc.mp hh).2
            have hc : (∑ n ∈ Ico (h+N-L+1) (N+1), (1:ℝ))
                = ((Ico (h+N-L+1) (N+1)).card : ℝ) := by simp
            rw [hc, Nat.card_Ico]
            have : (N + 1) - (h + N - L + 1) ≤ L := by omega
            exact_mod_cast this
      _ = (L:ℝ) * L := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
            simp
  have hB : ‖∑ h ∈ Icc 1 L, ∑ n ∈ Icc 1 (N-L), g (n+h)‖
      ≤ ∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖ := by
    rw [hBswap]; exact norm_sum_le _ _
  have htri : ∀ a b c : ℂ, ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    intro a b c
    have h1 := norm_add_le (a+b) c
    have h2 := norm_add_le a b
    linarith
  -- Hence `L ‖Σ g‖ ≤ Σ_n ‖Σ_h g(n+h)‖ + 2L²`.
  have hmain : (L:ℝ) * ‖∑ n ∈ Icc 1 N, g n‖
      ≤ (∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + 2 * ((L:ℝ)*L) := by
    have hnormeq : (L:ℝ) * ‖∑ n ∈ Icc 1 N, g n‖ = ‖(L:ℂ) * (∑ n ∈ Icc 1 N, g n)‖ := by
      rw [norm_mul, norm_natCast]
    rw [hnormeq, hconst, hdecomp]
    calc ‖(∑ h ∈ Icc 1 L, ∑ n ∈ Ico 1 (h+1), g n)
            + (∑ h ∈ Icc 1 L, ∑ n ∈ Icc 1 (N-L), g (n+h))
            + (∑ h ∈ Icc 1 L, ∑ n ∈ Ico (h+N-L+1) (N+1), g n)‖
        ≤ ‖∑ h ∈ Icc 1 L, ∑ n ∈ Ico 1 (h+1), g n‖
            + ‖∑ h ∈ Icc 1 L, ∑ n ∈ Icc 1 (N-L), g (n+h)‖
            + ‖∑ h ∈ Icc 1 L, ∑ n ∈ Ico (h+N-L+1) (N+1), g n‖ := htri _ _ _
      _ ≤ (L:ℝ) * L + (∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + (L:ℝ) * L :=
          add_le_add (add_le_add hA hB) hC
      _ = (∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + 2 * ((L:ℝ)*L) := by ring
  -- Divide by `L > 0`.
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  have hLR : (L:ℝ) ≠ 0 := ne_of_gt hLpos
  have hstep : ‖∑ n ∈ Icc 1 N, g n‖
      ≤ (L:ℝ)⁻¹ * ((∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + 2 * ((L:ℝ)*L)) := by
    calc ‖∑ n ∈ Icc 1 N, g n‖ = (L:ℝ)⁻¹ * ((L:ℝ) * ‖∑ n ∈ Icc 1 N, g n‖) := by
            rw [← mul_assoc, inv_mul_cancel₀ hLR, one_mul]
      _ ≤ (L:ℝ)⁻¹ * ((∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + 2 * ((L:ℝ)*L)) :=
            mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hLpos.le)
  calc ‖∑ n ∈ Icc 1 N, g n‖
      ≤ (L:ℝ)⁻¹ * ((∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + 2 * ((L:ℝ)*L)) := hstep
    _ = (L:ℝ)⁻¹ * (∑ n ∈ Icc 1 (N-L), ‖∑ h ∈ Icc 1 L, g (n+h)‖) + 2 * (L:ℝ) := by
          field_simp

end Work.BMF
