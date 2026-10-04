import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.l1_le_sqrt_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℓ¹` summability from the weighted `ℓ²` summability `CSq`

If the weighted `ℓ²` sum `Σ_k ⟨k⟩^{2s} ‖c k‖²` converges (`CSq s c < ∞`) and the weight
`⟨k⟩² = wt k` satisfies `card ι < 2 s` — so that the *dual* weight `Σ_k ⟨k⟩^{-2s}` converges —
then the coefficient family is summable in `ℓ¹`: `Σ_k ‖c k‖ < ∞`.

This is the summability (as opposed to the mere *estimate* of `l1_le_sqrt_CSq`) behind
`ℓ¹(ℤ^ι) ⊇` the weighted `ℓ²` space, and it is the form needed to apply `Summable.tsum_*`
lemmas downstream.

The proof is the pointwise AM–GM split

  `‖c k‖ = √(⟨k⟩^{2s}‖c k‖²) · √(⟨k⟩^{-2s}) ≤ (⟨k⟩^{2s}‖c k‖² + ⟨k⟩^{-2s}) / 2`,

whose two summands are summable by hypothesis and by the lattice `p`-series
`Work.Diff.STE.summable_wt_zpow`.
-/

noncomputable section

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise AM–GM: `‖z‖ ≤ (⟨k⟩^{2s}‖z‖² + ⟨k⟩^{-2s})/2`, the geometric mean
`√(⟨k⟩^{2s}‖z‖²)·√(⟨k⟩^{-2s})` being dominated by the arithmetic mean. -/
private lemma norm_le_half_wt_add_inv_wt (s : ℕ) (k : ι → ℤ) (z : ℂ) :
    ‖z‖ ≤ 2⁻¹ * ((wt k) ^ s * ‖z‖ ^ 2 + ((wt k) ^ s)⁻¹) := by
  have hw : (0 : ℝ) < (wt k) ^ s := pow_pos (wt_pos k) s
  have hA : 0 ≤ (wt k) ^ s * ‖z‖ ^ 2 := mul_nonneg hw.le (sq_nonneg _)
  have hB : 0 ≤ ((wt k) ^ s)⁻¹ := inv_nonneg.mpr hw.le
  have hmul : (wt k) ^ s * ‖z‖ ^ 2 * ((wt k) ^ s)⁻¹ = ‖z‖ ^ 2 := by
    calc (wt k) ^ s * ‖z‖ ^ 2 * ((wt k) ^ s)⁻¹
        = ‖z‖ ^ 2 * ((wt k) ^ s * ((wt k) ^ s)⁻¹) := by ring
      _ = ‖z‖ ^ 2 * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hw)]
      _ = ‖z‖ ^ 2 := mul_one _
  have hsq : Real.sqrt ((wt k) ^ s * ‖z‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹) = ‖z‖ := by
    rw [← Real.sqrt_mul hA, hmul, Real.sqrt_sq (norm_nonneg z)]
  have hgm :=
    two_mul_le_add_sq (Real.sqrt ((wt k) ^ s * ‖z‖ ^ 2)) (Real.sqrt (((wt k) ^ s)⁻¹))
  rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at hgm
  have h2 : 2 * ‖z‖ ≤ (wt k) ^ s * ‖z‖ ^ 2 + ((wt k) ^ s)⁻¹ := by
    calc 2 * ‖z‖
        = 2 * (Real.sqrt ((wt k) ^ s * ‖z‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹)) := by
          rw [hsq]
      _ = 2 * Real.sqrt ((wt k) ^ s * ‖z‖ ^ 2) * Real.sqrt (((wt k) ^ s)⁻¹) := by ring
      _ ≤ (wt k) ^ s * ‖z‖ ^ 2 + ((wt k) ^ s)⁻¹ := hgm
  linarith

/-- The dual weight `k ↦ ⟨k⟩^{-2s}` is summable as soon as `card ι < 2 s`. -/
private lemma summable_wt_inv_wt (s : ℕ) (hs : Fintype.card ι < 2 * s) :
    Summable (fun k : ι → ℤ => ((wt k) ^ s)⁻¹) :=
  (summable_wt_zpow (ι := ι) s hs).congr fun k => by
    simp [zpow_neg]

/-- **`ℓ¹` summability from the weighted `ℓ²` summability.** -/
theorem summable_norm_of_CSq {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (hs : Fintype.card ι < 2 * s) (c : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2)) :
    Summable (fun k : ι → ℤ => ‖c k‖) := by
  have hB : Summable (fun k : ι → ℤ => ((wt k) ^ s)⁻¹) := summable_wt_inv_wt s hs
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg (c k))
    (fun k => norm_le_half_wt_add_inv_wt s k (c k)) ?_
  exact (hc.add hB).mul_left (2⁻¹ : ℝ)

end Work.Diff.STE
