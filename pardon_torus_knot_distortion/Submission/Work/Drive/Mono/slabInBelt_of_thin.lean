import Mathlib
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Final.LTypes

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

noncomputable section

/-- The unit vector `shiftVσ σ 1` (the coordinate vector in the direction `σ 2`) evaluates a test
vector at its `σ 2`-coordinate. -/
theorem slabInBelt_inner_shiftVσ_one (σ : Equiv.Perm (Fin 3)) (x : R3) :
    inner ℝ (Work.BoxShrink.shiftVσ σ 1) x = x (σ 2) := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single (σ 2)]
  · simp [Work.BoxShrink.shiftVσ_apply]
  · intro b _ hb
    simp [Work.BoxShrink.shiftVσ_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ (σ 2)) h

/-- **The thin tilted slab of `PBox s c σ` lies in the flat belt.**  If every point of the closed
box is within `R` of the centre and the slab `{|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h}` is so thin that
`h + |u| + ‖v - shiftVσ σ 1‖ * R < boxSide 2 * s`, then the slab can only meet the closed box in
the flat belt `{|·_{σ 2} - c_{σ 2}| < boxSide 2 * s}`.

The proof compares the `v`-height with the `σ 2`-coordinate using the unit vector
`e = shiftVσ σ 1`: `⟪v, z-c⟫` is within `h` of `u`, while `⟪e-v, z-c⟫` is at most
`‖e-v‖ * R = ‖v-e‖ * R` by Cauchy–Schwarz. -/
theorem slabInBelt_of_thin {s u h R : ℝ} {c v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} (hR : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3, z ∈ closure (Submission.PBox s c σ) → ‖z - c‖ ≤ R) (hthin : h + |u| + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < Submission.boxSide 2 * s) : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3, z ∈ closure (Submission.PBox s c σ) → |inner ℝ v z - (inner ℝ v c + u)| ≤ h → |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s := by
  intro z hz hzh
  have hzR : ‖z - c‖ ≤ R := hR z hz
  have hinner : z (σ 2) - c (σ 2) = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c) := by
    rw [slabInBelt_inner_shiftVσ_one]
    rfl
  have hdecomp : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
      = inner ℝ v (z - c) + inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c) := by
    have hve : (Work.BoxShrink.shiftVσ σ 1 : R3) = v + (Work.BoxShrink.shiftVσ σ 1 - v) := by
      abel
    conv_lhs => rw [hve]
    rw [inner_add_left]
  have hA : |inner ℝ v (z - c) - u| ≤ h := by
    have h1 : inner ℝ v (z - c) - u = inner ℝ v z - (inner ℝ v c + u) := by
      rw [inner_sub_right]; ring
    rw [h1]; exact hzh
  have hB : |inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c)| ≤
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R := by
    calc |inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c)|
        ≤ ‖Work.BoxShrink.shiftVσ σ 1 - v‖ * ‖z - c‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖Work.BoxShrink.shiftVσ σ 1 - v‖ * R := mul_le_mul_of_nonneg_left hzR (norm_nonneg _)
      _ = ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R := by rw [norm_sub_rev]
  calc |z (σ 2) - c (σ 2)|
      = |inner ℝ v (z - c) + inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c)| := by
        rw [hinner, hdecomp]
    _ = |(inner ℝ v (z - c) - u)
          + (u + inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c))| := by
        congr 1; ring
    _ ≤ h + (|u| + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R) := by
        have hBu : |u + inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c)|
            ≤ |u| + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R :=
          le_trans (abs_add_le u _) (add_le_add le_rfl hB)
        linarith [hA, hBu, abs_add_le (inner ℝ v (z - c) - u)
          (u + inner ℝ (Work.BoxShrink.shiftVσ σ 1 - v) (z - c))]
    _ < Submission.boxSide 2 * s := by linarith

end

end Work.Drive.Mono
