import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.ghatFar_eq_sum_Wfar

/-!
# Splitting the far weight `Wfar` into its window and tail parts

`Wfar(x) = M₃ Σ_ℓ [|ℓ-x| > 2/M₃] ψ̂₁(M₃(ℓ-x))`.  The set of integers contributing is the
*disjoint* union of the **window** range `2/M₃ < |ℓ-x| ≤ B/M₃` and the **tail** range
`B/M₃ < |ℓ-x|` (with `2/M₃ < |ℓ-x|`), which is exactly `Wwin + Wtail`.

This gives the additive splitting of `ghatFar` used by the region-II far analysis: the `m₁`-sum
of `Bsum · Wfar` splits into the `m₁`-sum of `Bsum · Wwin` plus the `m₁`-sum of `Bsum · Wtail`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- **The far weight splits into window and tail.**  For every `y`,
`Wfar K M₃ y = Wwin K M₃ B y + Wtail K M₃ B y`.  (No hypothesis on `B` is needed: the two
`ℓ`-ranges are complementary inside `{|ℓ-y| > 2/M₃}` and disjoint.) -/
lemma Wfar_eq_Wwin_add_Wtail (K M₃ B y : ℝ) (hK : 0 < K) (hM₃ : 0 < M₃) :
    Wfar K M₃ y = Wwin K M₃ B y + Wtail K M₃ B y := by
  have hfar : Summable (fun ℓ : ℤ =>
      if |(ℓ : ℝ) - y| > 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) :=
    summable_psi1hat_shift_far K M₃ y hK hM₃
  have hwin : Summable (fun ℓ : ℤ =>
      if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
    refine Summable.of_norm_bounded hfar.norm (fun ℓ => ?_)
    by_cases h : 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃
    · rw [if_pos h, if_pos h.1]
    · rw [if_neg h]; simp
  have htail : Summable (fun ℓ : ℤ =>
      if B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y| then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
    refine Summable.of_norm_bounded hfar.norm (fun ℓ => ?_)
    by_cases h : B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y|
    · rw [if_pos h, if_pos h.2]
    · rw [if_neg h]; simp
  have hsum : (∑' ℓ : ℤ,
        if |(ℓ : ℝ) - y| > 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
      = (∑' ℓ : ℤ,
          if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
            psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)
        + (∑' ℓ : ℤ,
          if B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y| then
            psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0) := by
    rw [← Summable.tsum_add hwin htail]
    refine tsum_congr (fun ℓ => ?_)
    by_cases h1 : 2 / M₃ < |(ℓ : ℝ) - y|
    · by_cases h2 : |(ℓ : ℝ) - y| ≤ B / M₃
      · rw [if_pos h1, if_pos ⟨h1, h2⟩, if_neg (fun hc => not_lt.mpr h2 hc.1), add_zero]
      · rw [if_pos h1, if_neg (fun hc => h2 hc.2), if_pos ⟨not_le.mp h2, h1⟩, zero_add]
    · rw [if_neg (fun hc => h1 hc), if_neg (fun hc => h1 hc.1),
        if_neg (fun hc => h1 hc.2), add_zero]
  unfold Wfar Wwin Wtail
  rw [hsum]
  ring

/-- **The far part of `ghat` splits into its window and tail parts.** -/
theorem ghatFar_split_win_tail {K M₁ M₂ M₃ B : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (ξ : ℝ) :
    ghatFar K M₁ M₂ M₃ f ξ =
      (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wwin K M₃ B (ξ / (m₁ : ℝ)))
      + (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))) := by
  rw [ghatFar_eq_sum_Wfar hK hM₁ hM₂ hM₃ hf hcs ξ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m₁ _ => ?_)
  rw [Wfar_eq_Wwin_add_Wtail K M₃ B (ξ / (m₁ : ℝ)) hK hM₃]
  ring

end

end Work.GM.Affine
