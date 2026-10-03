import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs

/-!
# `linFamAvg` at a smaller radius

`linFamAvg D l c N M H f b β` is the *average* of the nonnegative fibres `linFib` over the parameter
box `parBox l H`.  For `H' ≤ H` the box `parBox l H'` is a subset of `parBox l H`, so the average at
the larger radius dominates the rescaled average at the smaller one:

  `(|parBox l H'| / |parBox l H|) * linFamAvg … H' ≤ linFamAvg … H`.

This is the comparison that lets the PET chain be run at its *maximal admissible* window
`petWindow` (rather than at the datum's `δ'`), and hence what closes the window bookkeeping of the
assembly: the chain produces a lower bound at the radius `⌊petWindow · M⌋` and the transfer to the
conclusion's radius `⌊δ' · M⌋ ≥ ⌊petWindow · M⌋` (when `δ' ≥ petWindow`) costs only the factor
`(|parBox l H_c| / |parBox l H_δ|)`, which is bounded below by a constant depending on `P` alone.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The parameter box is monotone in the radius. -/
lemma parBox_mono_radius (D : IdxDatum) (l : ℕ) {H H' : ℕ} (h : H' ≤ H) :
    D.parBox l H' ⊆ D.parBox l H := by
  intro a ha
  rw [IdxDatum.mem_parBox] at ha ⊢
  intro j s
  obtain ⟨h1, h2⟩ := ha j s
  have hle : ((H' : ℤ)) ≤ ((H : ℤ)) := by exact_mod_cast h
  exact ⟨by omega, by omega⟩

/-- The parameter box is never empty. -/
lemma parBox_nonempty (D : IdxDatum) (l H : ℕ) : (D.parBox l H).Nonempty :=
  ⟨0, by rw [IdxDatum.mem_parBox]; intro j s; simp⟩

/-- **`linFamAvg` at a smaller radius.** -/
theorem linFamAvg_radius_le {l : ℕ} (D : IdxDatum) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ)
    {H H' : ℕ} (h : H' ≤ H) :
    (((D.parBox l H').card : ℕ) : ℝ) / (((D.parBox l H).card : ℕ) : ℝ)
        * linFamAvg D l c N M H' f b β
      ≤ linFamAvg D l c N M H f b β := by
  have hsub : D.parBox l H' ⊆ D.parBox l H := parBox_mono_radius D l h
  have hSne : (((D.parBox l H).card : ℕ) : ℝ) ≠ 0 := by
    have := Finset.card_pos.mpr (parBox_nonempty D l H)
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hS'ne : (((D.parBox l H').card : ℕ) : ℝ) ≠ 0 := by
    have := Finset.card_pos.mpr (parBox_nonempty D l H')
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  rw [linFamAvg_eq, linFamAvg_eq]
  have key : (((D.parBox l H').card : ℕ) : ℝ) / (((D.parBox l H).card : ℕ) : ℝ)
      * ((((D.parBox l H').card : ℕ) : ℝ)⁻¹
          * ∑ a ∈ D.parBox l H', linFib D l c N M f b β a)
      = (((D.parBox l H).card : ℕ) : ℝ)⁻¹
          * ∑ a ∈ D.parBox l H', linFib D l c N M f b β a := by
    field_simp
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => ?_)
  simp only [linFib]
  exact norm_nonneg _

end

end Work.Peluse.UControl
