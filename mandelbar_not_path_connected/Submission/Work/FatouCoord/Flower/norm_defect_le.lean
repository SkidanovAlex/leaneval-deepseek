import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Flower.LambdaBounds
import Submission.Work.FatouCoord.Flower.defect_zero_bound
import Submission.Work.FatouCoord.Flower.defect_lipschitz_large

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The defect of the corrected ansatz is `O((1 + log ‖y‖ + ‖ζ‖)/‖y‖²)` on `{Re y < -1}`

This is the form of the defect estimate needed by the flower construction: the chart points that
occur there have large modulus but are only known to satisfy `Re y < -1` (they are *not*
confined to a far left half-plane `{Re y < -R}` as in `Repelling.defect_bound`), and the
correction `ζ` is allowed to be as large as a multiple of `√‖y‖`.

The proof combines the two halves of the estimate:

* `Flower.defect_zero_bound` bounds the value at `ζ = 0`,
  `‖defect f a y 0‖ ≤ K₁ (1 + log ‖y‖)/‖y‖²`;
* `Flower.defect_lipschitz_large` bounds the `ζ`-dependence on the disc of radius `C √‖y‖`,
  `‖defect f a y ζ - defect f a y ζ'‖ ≤ K₂ ‖ζ - ζ'‖/‖y‖²`.

The two estimates add, and `1 + log ‖y‖ ≥ 1` together with `‖ζ‖ ≥ 0` absorbs the two constants
into a single one.
-/

namespace Work.FatouCoord.Flower

theorem norm_defect_le {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (C : ℝ) : ∃ K N : ℝ, 0 < K ∧ 0 < N ∧ ∀ y ζ : ℂ, y.re < -1 → N ≤ ‖y‖ → ‖ζ‖ ≤ C * Real.sqrt ‖y‖ → ‖Work.FatouCoord.Petal.defect f a y ζ‖ ≤ K * (1 + Real.log ‖y‖ + ‖ζ‖) / ‖y‖ ^ 2 := by
  obtain ⟨K₁, N₁, hK₁pos, hN₁pos, h₁⟩ := Work.FatouCoord.Flower.defect_zero_bound hb
  obtain ⟨K₂, N₂, hK₂pos, hN₂pos, h₂⟩ :=
    Work.FatouCoord.Flower.defect_lipschitz_large hb (C := max C 0) (le_max_right C 0)
  refine ⟨K₁ + K₂ + 1, max (max N₁ N₂) 1 + 1, by linarith, ?_, ?_⟩
  · have : (1:ℝ) ≤ max (max N₁ N₂) 1 := le_max_right _ 1
    linarith
  · intro y ζ hy hNy hζ
    have hNy₁ : N₁ ≤ ‖y‖ := by
      have : N₁ ≤ max (max N₁ N₂) 1 := le_trans (le_max_left N₁ N₂) (le_max_left _ 1)
      linarith
    have hNy₂ : N₂ ≤ ‖y‖ := by
      have : N₂ ≤ max (max N₁ N₂) 1 := le_trans (le_max_right N₁ N₂) (le_max_left _ 1)
      linarith
    have hy1 : (1:ℝ) ≤ ‖y‖ := by
      have : (1:ℝ) ≤ max (max N₁ N₂) 1 := le_max_right _ 1
      linarith
    have hζ' : ‖ζ‖ ≤ (max C 0) * Real.sqrt ‖y‖ :=
      le_trans hζ (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
    have h0mem : ‖(0:ℂ)‖ ≤ (max C 0) * Real.sqrt ‖y‖ := by
      simp only [norm_zero]
      positivity
    have hd1 := h₁ y hy hNy₁
    have hd2 := h₂ y ζ 0 hy hNy₂ hζ' h0mem
    have htri : ‖Work.FatouCoord.Petal.defect f a y ζ‖ ≤
        ‖Work.FatouCoord.Petal.defect f a y 0‖
          + ‖Work.FatouCoord.Petal.defect f a y ζ - Work.FatouCoord.Petal.defect f a y 0‖ := by
      have h := norm_add_le (Work.FatouCoord.Petal.defect f a y 0)
        (Work.FatouCoord.Petal.defect f a y ζ - Work.FatouCoord.Petal.defect f a y 0)
      have h2 : Work.FatouCoord.Petal.defect f a y 0
          + (Work.FatouCoord.Petal.defect f a y ζ - Work.FatouCoord.Petal.defect f a y 0)
          = Work.FatouCoord.Petal.defect f a y ζ := by ring
      rwa [h2] at h
    have hlog0 : 0 ≤ Real.log ‖y‖ := Real.log_nonneg hy1
    have hznn : 0 ≤ ‖ζ‖ := norm_nonneg ζ
    have htnn : 0 < ‖y‖ ^ 2 := by positivity
    calc ‖Work.FatouCoord.Petal.defect f a y ζ‖
        ≤ ‖Work.FatouCoord.Petal.defect f a y 0‖
            + ‖Work.FatouCoord.Petal.defect f a y ζ - Work.FatouCoord.Petal.defect f a y 0‖ := htri
      _ ≤ K₁ * (1 + Real.log ‖y‖) / ‖y‖ ^ 2 + K₂ * ‖ζ - 0‖ / ‖y‖ ^ 2 := add_le_add hd1 hd2
      _ ≤ (K₁ + K₂ + 1) * (1 + Real.log ‖y‖ + ‖ζ‖) / ‖y‖ ^ 2 := by
          rw [sub_zero, ← add_div]
          apply div_le_div_of_nonneg_right _ htnn.le
          nlinarith [hK₁pos, hK₂pos, hlog0, hznn]

end Work.FatouCoord.Flower
