import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open Work.MRMT

/-- If `‖N‖ ≤ R · ‖D‖` and `0 ≤ R`, then `‖N/D‖ ≤ R`.  Division by zero gives the junk
value `0`, which is harmless. -/
private theorem norm_div_le_of_le_mul {N D : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ‖N‖ ≤ R * ‖D‖) : ‖N / D‖ ≤ R := by
  rw [norm_div]
  by_cases hD : ‖D‖ = 0
  · rw [hD, div_zero]; exact hR
  · have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr (norm_ne_zero_iff.mp hD)
    calc ‖N‖ / ‖D‖ ≤ (R * ‖D‖) / ‖D‖ := div_le_div_of_nonneg_right h hDpos.le
      _ = R := by rw [mul_div_cancel_right₀ _ hDpos.ne']

theorem pullRev_le {μ f : ℂ → ℂ} {z : ℂ} {κ V : ℝ} (hκ : 0 ≤ κ) (hκV : κ * V < 1)
    (hV : ‖μ (f z)‖ ≤ V) (hr : ‖Work.MRMT.dz f z‖ ≤ κ * ‖Work.MRMT.dzbar f z‖) :
    ‖Work.MRMT.Found.pullRev μ f z‖ ≤ (V + κ) / (1 - κ * V) := by
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) hV
  have hden : 0 < 1 - κ * V := by linarith
  have hR0 : 0 ≤ (V + κ) / (1 - κ * V) := div_nonneg (by linarith) hden.le
  -- Bound on the numerator.
  have hN : ‖star (dz f z) + star (μ (f z)) * dzbar f z‖ ≤ (V + κ) * ‖dzbar f z‖ := by
    calc ‖star (dz f z) + star (μ (f z)) * dzbar f z‖
        ≤ ‖star (dz f z)‖ + ‖star (μ (f z)) * dzbar f z‖ := norm_add_le _ _
      _ = ‖dz f z‖ + ‖μ (f z)‖ * ‖dzbar f z‖ := by rw [norm_star, norm_mul, norm_star]
      _ ≤ κ * ‖dzbar f z‖ + V * ‖dzbar f z‖ :=
          add_le_add hr (mul_le_mul hV le_rfl (norm_nonneg _) hV0)
      _ = (V + κ) * ‖dzbar f z‖ := by ring
  -- Lower bound on the denominator.
  have hD : (1 - κ * V) * ‖dzbar f z‖
      ≤ ‖star (dzbar f z) + star (μ (f z)) * dz f z‖ := by
    have h1 : ‖μ (f z)‖ * ‖dz f z‖ ≤ V * (κ * ‖dzbar f z‖) :=
      mul_le_mul hV hr (norm_nonneg _) hV0
    have h2 : ‖dzbar f z‖ - ‖μ (f z)‖ * ‖dz f z‖
        ≤ ‖star (dzbar f z) + star (μ (f z)) * dz f z‖ := by
      have hle := norm_add_le (star (dzbar f z) + star (μ (f z)) * dz f z)
        (-(star (μ (f z)) * dz f z))
      simp only [add_neg_cancel_right, norm_neg, norm_star, norm_mul] at hle
      linarith
    have h3 : (1 - κ * V) * ‖dzbar f z‖ = ‖dzbar f z‖ - V * (κ * ‖dzbar f z‖) := by ring
    rw [h3]
    linarith
  -- Combine into `‖num‖ ≤ R · ‖den‖`.
  have hkey : ‖star (dz f z) + star (μ (f z)) * dzbar f z‖
      ≤ ((V + κ) / (1 - κ * V))
        * ‖star (dzbar f z) + star (μ (f z)) * dz f z‖ := by
    have h2 : ((V + κ) / (1 - κ * V)) * ((1 - κ * V) * ‖dzbar f z‖)
        = (V + κ) * ‖dzbar f z‖ := by
      rw [← mul_assoc, div_mul_cancel₀ (V + κ) hden.ne']
    calc ‖star (dz f z) + star (μ (f z)) * dzbar f z‖
        ≤ (V + κ) * ‖dzbar f z‖ := hN
      _ = ((V + κ) / (1 - κ * V)) * ((1 - κ * V) * ‖dzbar f z‖) := h2.symm
      _ ≤ ((V + κ) / (1 - κ * V))
            * ‖star (dzbar f z) + star (μ (f z)) * dz f z‖ :=
          mul_le_mul_of_nonneg_left hD hR0
  rw [Work.MRMT.Found.pullRev]
  exact norm_div_le_of_le_mul hR0 hkey

end Work.FBif
