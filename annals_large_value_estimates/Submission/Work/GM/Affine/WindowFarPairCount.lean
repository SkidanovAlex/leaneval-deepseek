import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.window_part_defs
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.windowTrunc_L2_bound

/-!
# Counting the window pairs (GM §9)

`Pwin T M₁ M₃ B ξ` is the set of pairs `(m₁, ℓ)` with `m₁ ∈ R1 M₁` (so `M₁ < |m₁| ≤ 2M₁`) and
`|ℓ - ξ/m₁| ≤ B/M₃`.  On the far window region `T^η M₁/M₃ < |ξ| ≤ T^6` with `2B ≤ T^η`, every such
pair satisfies

`|m₁ ℓ - ξ| = |m₁| · |ℓ - ξ/m₁| ≤ 2M₁ · B/M₃ =: r` and `r ≤ T^η M₁/M₃ < |ξ|`,

so the *resonance count* `card_mul_pairs_le` applies at once with `r = 2BM₁/M₃`, `X = T^6`:

`#(Pwin) ≤ C_ε (T^6 + 2BM₁/M₃ + 2)^ε (2 · 2BM₁/M₃ + 1)`.

This is step 2 of the plan of `NOTES_windowTrunc_L2_bound.md`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The region condition `ξ ∈ [-T^6,T^6] \ [-T^η M₁/M₃, T^η M₁/M₃]` says `|ξ| ≤ T^6` and
`T^η M₁/M₃ < |ξ|`. -/
lemma abs_le_and_lt_of_mem_farWindow {T η M₁ M₃ ξ : ℝ}
    (hξ : ξ ∈ (Set.Icc (-(T ^ 6)) (T ^ 6))
        \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) :
    |ξ| ≤ T ^ 6 ∧ T ^ η * M₁ / M₃ < |ξ| := by
  obtain ⟨hξIcc, hξnot⟩ := by simpa only [Set.mem_sdiff] using hξ
  have h1 : |ξ| ≤ T ^ 6 := by
    rw [Set.mem_Icc] at hξIcc
    rw [abs_le]
    exact ⟨by linarith [hξIcc.1], hξIcc.2⟩
  have h2 : T ^ η * M₁ / M₃ < |ξ| := by
    have h := hξnot
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · linarith [neg_le_abs ξ]
    · linarith [le_abs_self ξ]
  exact ⟨h1, h2⟩

/-- Membership in `Pwin` gives membership of the first coordinate in `R1 M₁` and the window
condition on `ℓ - ξ/m₁`. -/
lemma mem_R1_and_window_of_mem_Pwin {T M₁ M₃ B ξ : ℝ} {p : ℤ × ℤ}
    (hp : p ∈ Pwin T M₁ M₃ B ξ) :
    p.1 ∈ R1 M₁ ∧
      2 / M₃ < |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
        |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ≤ B / M₃ := by
  rw [Pwin, Finset.mem_filter] at hp
  obtain ⟨hp', hcond⟩ := hp
  obtain ⟨hp1, -⟩ := Finset.mem_product.mp hp'
  exact ⟨hp1, hcond.1, hcond.2⟩

/-- **Counting the window pairs** (GM §9, region II, step 2 of the plan of
`NOTES_windowTrunc_L2_bound.md`).

For every `ε > 0` there is `Cc > 0` such that on the far window region
`T^η M₁/M₃ < |ξ| ≤ T^6`, with `2B ≤ T^η`, the window pairs satisfy
`#(Pwin T M₁ M₃ B ξ) ≤ Cc (T^6 + 2BM₁/M₃ + 2)^ε (2·2BM₁/M₃ + 1)`.

Proof: every pair of `Pwin` has `M₁ < |m₁| ≤ 2M₁`, hence
`|m₁ℓ - ξ| = |m₁|·|ℓ - ξ/m₁| ≤ 2BM₁/M₃ =: r`, and `r ≤ T^η M₁/M₃ < |ξ|`; the resonance count
`card_mul_pairs_le` (which counts pairs by the divisor count of the products `m₁ℓ`) gives the
claim. -/
theorem WindowFarPairCount {ε : ℝ} (hε : 0 < ε) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (T η B M₁ M₃ : ℝ), 1 ≤ T → 0 < η → 2 ≤ B → 2 * B ≤ T ^ η →
      0 < M₁ → 1 ≤ M₃ →
      ∀ ξ : ℝ, ξ ∈ (Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) →
      ((Pwin T M₁ M₃ B ξ).card : ℝ)
        ≤ Cc * (T ^ 6 + 2 * B * M₁ / M₃ + 2) ^ ε * (2 * (2 * B * M₁ / M₃) + 1) := by
  obtain ⟨C, hCpos, hC⟩ := card_mul_pairs_le hε
  refine ⟨C, hCpos, ?_⟩
  intro T η B M₁ M₃ hT hη hB h2B hM₁ hM₃ ξ hξ
  obtain ⟨hξabs, hξgt⟩ := abs_le_and_lt_of_mem_farWindow hξ
  have hX : (1 : ℝ) ≤ T ^ 6 := one_le_pow₀ hT
  have hM₃pos : 0 < M₃ := by linarith
  -- the product distance bound `r = 2BM₁/M₃` is below `|ξ|`
  have hr_le : 2 * B * M₁ / M₃ ≤ T ^ η * M₁ / M₃ := by
    have h : 2 * B * M₁ ≤ T ^ η * M₁ := by nlinarith
    exact div_le_div_of_nonneg_right h hM₃pos.le
  refine hC M₁ (2 * B * M₁ / M₃) (T ^ 6) hM₁ (by positivity) hX ξ (lt_of_le_of_lt hr_le hξgt)
    hξabs (Pwin T M₁ M₃ B ξ) ?_ ?_
  · intro p hp
    exact R1_le_abs (mem_R1_and_window_of_mem_Pwin hp).1
  · intro p hp
    obtain ⟨hm₁R, -, hhi⟩ := mem_R1_and_window_of_mem_Pwin hp
    have hm₁lt : M₁ < |(p.1 : ℝ)| := (Finset.mem_filter.mp hm₁R).2
    have hne : (p.1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hm₁lt
      linarith
    have hkey : ((p.1 : ℝ) * (p.2 : ℝ)) - ξ
        = (p.1 : ℝ) * ((p.2 : ℝ) - ξ / (p.1 : ℝ)) := by
      rw [mul_sub, mul_div_cancel₀ ξ hne]
    rw [hkey, abs_mul]
    calc |(p.1 : ℝ)| * |(p.2 : ℝ) - ξ / (p.1 : ℝ)|
        ≤ (2 * M₁) * (B / M₃) :=
          mul_le_mul (abs_le_two_mul_of_mem_R1 hm₁R) hhi (abs_nonneg _) (by positivity)
      _ = 2 * B * M₁ / M₃ := by ring

end

end Work.GM.Affine
