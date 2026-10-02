/-
Copyright: Work.MRMT (mandelbar) subproject.

# Auxiliary algebra for the conjugated composite `star ∘ F ∘ f`

For a homeomorphism `F` satisfying the Beltrami equation `∂̄F = μF · ∂F` and a `C¹` map `f`,
the composite `star ∘ F ∘ f` has complex dilatation

`pullRev μF f z = (star (∂f z) + star (μF (f z)) · ∂̄f z) / (star (∂̄f z) + star (μF (f z)) · ∂f z)`,

as computed in `Work.MRMT.Found.dz_star_comp` / `Work.MRMT.Found.dzbar_star_comp`.  This file
gives the numerator `conjNum` and denominator `conjDen` of that expression, the algebraic
identity for the *defect* `∂̄(star ∘ F ∘ f) - μF · ∂(star ∘ F ∘ f)` in terms of
`conjNum - μF · conjDen`, and the elementary estimates used in `conj_contDiff`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.dz_star_comp
import Submission.Work.MRMT.Found.dzbar_star_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## The numerator and denominator of `pullRev` -/

/-- Numerator of the complex dilatation of `star ∘ F ∘ f`. -/
def conjNum (μF f : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (dz f z) + star (μF (f z)) * dzbar f z

/-- Denominator of the complex dilatation of `star ∘ F ∘ f`. -/
def conjDen (μF f : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (dzbar f z) + star (μF (f z)) * dz f z

/-- `pullRev` is the quotient of `conjNum` by `conjDen`. -/
theorem pullRev_eq_div (μF f : ℂ → ℂ) (z : ℂ) :
    pullRev μF f z = conjNum μF f z / conjDen μF f z := rfl

/-! ## The denominator does not vanish in the orientation-reversing case -/

/-- If `f` is orientation-reversing at `z` (`‖∂f z‖ < ‖∂̄f z‖`) and `‖μF (f z)‖ ≤ k < 1`,
then the denominator `conjDen μF f z` does not vanish. -/
theorem conjDen_ne_zero {f μF : ℂ → ℂ} {k : ℝ} {z : ℂ}
    (hμ : ‖μF (f z)‖ ≤ k) (hk : k < 1) (hrev : ‖dz f z‖ < ‖dzbar f z‖) :
    conjDen μF f z ≠ 0 := by
  intro h
  have h1 : star (dzbar f z) = -(star (μF (f z)) * dz f z) := by
    rw [conjDen] at h
    linear_combination h
  have h2 : ‖dzbar f z‖ = ‖μF (f z)‖ * ‖dz f z‖ := by
    have hh := congrArg norm h1
    simp only [norm_neg, norm_mul, norm_star] at hh
    simpa using hh
  rcases eq_or_lt_of_le (norm_nonneg (dz f z)) with h3 | h3
  · rw [← h3, mul_zero] at h2
    rw [h2, ← h3] at hrev
    exact absurd hrev (lt_irrefl 0)
  · have h4 : ‖dzbar f z‖ ≤ k * ‖dz f z‖ := by
      rw [h2]; exact mul_le_mul_of_nonneg_right hμ h3.le
    have h5 : k * ‖dz f z‖ < ‖dz f z‖ := by nlinarith
    linarith [hrev, h4, h5]

/-! ## Elementary bounds -/

/-- `‖conjNum μF f z‖ ≤ (1 + k) M` when `‖μF (f z)‖ ≤ k` and both Wirtinger derivatives of
`f` at `z` are bounded by `M`. -/
theorem norm_conjNum_le {f μF : ℂ → ℂ} {k M : ℝ} {z : ℂ} (hk : 0 ≤ k)
    (hμ : ‖μF (f z)‖ ≤ k) (ha : ‖dz f z‖ ≤ M) (hb : ‖dzbar f z‖ ≤ M) :
    ‖conjNum μF f z‖ ≤ (1 + k) * M := by
  rw [conjNum]
  calc ‖star (dz f z) + star (μF (f z)) * dzbar f z‖
      ≤ ‖star (dz f z)‖ + ‖star (μF (f z)) * dzbar f z‖ := norm_add_le _ _
    _ = ‖dz f z‖ + ‖μF (f z)‖ * ‖dzbar f z‖ := by rw [norm_star, norm_mul, norm_star]
    _ ≤ M + k * M := add_le_add ha (mul_le_mul hμ hb (norm_nonneg _) hk)
    _ = (1 + k) * M := by ring

/-- `‖conjDen μF f z‖ ≤ (1 + k) M` when `‖μF (f z)‖ ≤ k` and both Wirtinger derivatives of
`f` at `z` are bounded by `M`. -/
theorem norm_conjDen_le {f μF : ℂ → ℂ} {k M : ℝ} {z : ℂ} (hk : 0 ≤ k)
    (hμ : ‖μF (f z)‖ ≤ k) (ha : ‖dz f z‖ ≤ M) (hb : ‖dzbar f z‖ ≤ M) :
    ‖conjDen μF f z‖ ≤ (1 + k) * M := by
  rw [conjDen]
  calc ‖star (dzbar f z) + star (μF (f z)) * dz f z‖
      ≤ ‖star (dzbar f z)‖ + ‖star (μF (f z)) * dz f z‖ := norm_add_le _ _
    _ = ‖dzbar f z‖ + ‖μF (f z)‖ * ‖dz f z‖ := by rw [norm_star, norm_mul, norm_star]
    _ ≤ M + k * M := add_le_add hb (mul_le_mul hμ ha (norm_nonneg _) hk)
    _ = (1 + k) * M := by ring

/-! ## The defect of the composite -/

/-- The Wirtinger defect of `star ∘ F ∘ f` at `z`, expressed through `conjNum`, `conjDen`:
`∂̄(star ∘ F ∘ f) z - μF z · ∂(star ∘ F ∘ f) z = star (∂F (f z)) · (conjNum - μF z · conjDen)`. -/
theorem dzbar_sub_mul_dz_eq {F f μF : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F (f z)) (hf : DifferentiableAt ℝ f z)
    (hrel : dzbar F (f z) = μF (f z) * dz F (f z)) :
    dzbar (star ∘ F ∘ f) z - μF z * dz (star ∘ F ∘ f) z
      = star (dz F (f z)) * (conjNum μF f z - μF z * conjDen μF f z) := by
  rw [dzbar_star_comp hF hf hrel, dz_star_comp hF hf hrel]
  unfold conjNum conjDen
  ring

end Work.MRMT.Found
