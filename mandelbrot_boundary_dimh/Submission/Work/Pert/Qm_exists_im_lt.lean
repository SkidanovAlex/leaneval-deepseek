import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Qm_slice

/-!
# PERT · `Work.Pert.Qm_exists_im_lt`

The lower gate `Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))` is **unbounded below**: for every
real `T` it contains a point of imaginary part `< -T`.

Geometrically: the slice of `Qm Ξ α` at height `t` is the open interval
`(Ξ - (1/α).re - |t + (1/α).im| , |t| - Ξ)` (`Work.Pert.Qm_mem_iff'`); as `t → -∞` both
endpoints tend to `+∞` like `|t|`, so the slice eventually swallows any fixed abscissa.

Explicitly, with `A = (1/α).re`, `B = (1/α).im`,
`L = |2Ξ - A| + |B| + |T| + 1` and the point `z = (Ξ - A) - L·i` one has `z.im = -L < -T`, and
the two cone conditions become `|B - L| > 0` (which follows from `L ≥ |B| + 1`) and
`2Ξ - A < L` (which follows from `L ≥ |2Ξ - A| + 1`).
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

theorem Qm_exists_im_lt {Ξ : ℝ} {α : ℂ} (T : ℝ) :
    ∃ z ∈ Work.Pert.Qm Ξ α, z.im < -T := by
  set A : ℝ := (1 / α).re with hA
  set B : ℝ := (1 / α).im with hB
  set L : ℝ := |2 * Ξ - A| + |B| + |T| + 1 with hL
  have hBA : (0 : ℝ) ≤ |2 * Ξ - A| := abs_nonneg _
  have hB0 : (0 : ℝ) ≤ |B| := abs_nonneg _
  have hT0 : (0 : ℝ) ≤ |T| := abs_nonneg _
  have hLge1 : |2 * Ξ - A| + 1 ≤ L := by rw [hL]; linarith
  have hLlB : |B| + 1 ≤ L := by rw [hL]; linarith
  have hLlT : |T| + 1 ≤ L := by rw [hL]; linarith
  have hLpos : (0 : ℝ) < L := by linarith
  refine ⟨(((Ξ - A : ℝ) : ℂ) + ((-L : ℝ) : ℂ) * Complex.I), ?_, ?_⟩
  · rw [Qm_mem_iff']
    rw [← hA, ← hB]
    refine ⟨?_, ?_⟩
    · have hneg : (-L) + B < 0 := by
        have h1 : B ≤ |B| := le_abs_self B
        linarith
      have hpos : (0 : ℝ) < |(-L) + B| := abs_pos.mpr (ne_of_lt hneg)
      linarith
    · rw [abs_neg, abs_of_pos hLpos]
      have h2 : 2 * Ξ - A ≤ |2 * Ξ - A| := le_abs_self _
      linarith
  · have him : (((Ξ - A : ℝ) : ℂ) + ((-L : ℝ) : ℂ) * Complex.I).im = -L := by simp
    rw [him]
    have h2 : T ≤ |T| := le_abs_self T
    linarith

end

end Work.Pert
