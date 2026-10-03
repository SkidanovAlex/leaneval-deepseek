import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs

/-!
# Spreading *back*: a lower bound on a filtered average transfers to the full set

The §5 chain cannot live on `LStateAbs` (whose non-vanishing conjunct is *false* on the full
parameter box — the coefficient `pFlat D d c m Λ` vanishes at the all-zero parameter for `m ≥ 1`):
the round must **spread** the state from the full box `A` to its "good" subset
`A^good = {a ∈ A : ∀ i, p i a ≠ 0}` (see `Prop36SW/lstateSpread.lean`), peel there, and then spread
**back** to the full box.

The spread back is the elementary observation that for a nonnegative function `Φ` on `A` the average
over `A` dominates (half of) the average over a subset `A'` of relative density `≥ 1/2`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

/-- **Spreading back.**  If `A' ⊆ A` has relative density at least `1/2` and `Φ ≥ 0` on `A`, then
the average of `Φ` over `A` is at least half its average over `A'`. -/
theorem filter_average_ge_half {P : Type} [DecidableEq P] (A A' : Finset P) (Φ : P → ℝ)
    (hA' : A' ⊆ A) (h0 : ∀ a ∈ A, 0 ≤ Φ a)
    (h2 : (A.card : ℝ) ≤ 2 * (A'.card : ℝ)) :
    ((A'.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a) / 2 ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, Φ a := by
  rcases Finset.eq_empty_or_nonempty A' with hA'e | hA'ne
  · have hAcard : A.card = 0 := by
      have h : (A.card : ℝ) ≤ 0 := by rw [hA'e] at h2; simpa using h2
      exact Nat.cast_eq_zero.mp (le_antisymm h (Nat.cast_nonneg _))
    rw [hA'e, Finset.card_eq_zero.mp hAcard]
    simp
  · have hA'card : (0 : ℝ) < (A'.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hA'ne
    have hAcard : (0 : ℝ) < (A.card : ℝ) :=
      lt_of_lt_of_le hA'card (by
        have : (A'.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA'
        linarith)
    have hsum_le : ∑ a ∈ A', Φ a ≤ ∑ a ∈ A, Φ a :=
      Finset.sum_le_sum_of_subset_of_nonneg hA' (fun x hx _ => h0 x hx)
    have hsum_nn : 0 ≤ ∑ a ∈ A', Φ a := Finset.sum_nonneg (fun a ha => h0 a (hA' ha))
    have hhalf : (1 : ℝ) / 2 ≤ (A.card : ℝ)⁻¹ * (A'.card : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ hAcard]
      linarith [h2]
    have hfac : (A.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a
        = ((A.card : ℝ)⁻¹ * (A'.card : ℝ)) * ((A'.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a) := by
      field_simp
    have hXnn : (0 : ℝ) ≤ (A'.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a :=
      mul_nonneg (le_of_lt (inv_pos.mpr hA'card)) hsum_nn
    have hh := mul_le_mul_of_nonneg_right hhalf hXnn
    calc ((A'.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a) / 2
        = (1 / 2) * ((A'.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a) := by ring
      _ ≤ ((A.card : ℝ)⁻¹ * (A'.card : ℝ)) * ((A'.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a) := hh
      _ = (A.card : ℝ)⁻¹ * ∑ a ∈ A', Φ a := hfac.symm
      _ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, Φ a :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)

end

end Work.Peluse.Prop36SW
