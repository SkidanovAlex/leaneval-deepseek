import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- On a set of diameter at most `1`, the Hölder seminorm of order `α` is
monotone in the exponent: if `α ≤ β` and `‖x - y‖ ≤ 1` for all `x, y ∈ Ω`, then
`‖x - y‖ ^ β ≤ ‖x - y‖ ^ α`, so each divided difference with exponent `β` is
dominated by the corresponding one with exponent `α`. -/
private lemma holderSeminorm_mono_alpha {i : ℕ} {α β : ℝ} (hαβ : α ≤ β) {f : X → ℂ}
    {Ω : Set X} (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ 1) :
    holderSeminorm i α f Ω ≤ holderSeminorm i β f Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_holderSeminorm i β f Ω hx hy hxy)
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hr1 : ‖x - y‖ ≤ 1 := hΩ x hx y hy
  have hpow : ‖x - y‖ ^ β ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow_of_exponent_ge hr hr1 hαβ
  have hpos : 0 < ‖x - y‖ ^ β := Real.rpow_pos_of_pos hr β
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hpow

/-- The `C^{k,α}` norm of `Submission/Work/CR/Flat/Holder.lean` is monotone in the
exponent `α` on a set of diameter at most `1`.

This is the correct hypothesis: on a set where `‖x - y‖ ≤ 1` one has
`‖x - y‖ ^ β ≤ ‖x - y‖ ^ α` for `α ≤ β`, so that the divided differences — and
hence the norm — increase with `α`. -/
theorem holderNorm_mono_alpha {k : ℕ} {α β : ℝ} (hαβ : α ≤ β) {f : X → ℂ} {Ω : Set X}
    (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ 1) :
    holderNorm k α f Ω ≤ holderNorm k β f Ω := by
  unfold holderNorm
  exact Finset.sum_le_sum fun i _ =>
    add_le_add le_rfl (holderSeminorm_mono_alpha hαβ hΩ)

end Work.CR.Flat.Holder
