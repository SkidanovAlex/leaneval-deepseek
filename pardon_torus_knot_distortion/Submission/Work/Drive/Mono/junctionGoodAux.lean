import Mathlib
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.NoGrazeDefs
import Submission.Work.Drive.Mono.tiltData_small_of_dir_near

/-!
# Auxiliary lemmas for `Work.Drive.Mono.exists_junctionGood_tiltData`

Two elementary bookkeeping lemmas used by the junction-genericity data construction:
`SlabCutsBox` from the width inequality of the tilt-data construction, and the radius bound on the
*closure* of the box (needed because the window of the tilted data must contain the `ℓ`-range of
`closure (PBox)`, the levels added to the exceptional set being `ℓ`-values of points of the
closure).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

noncomputable section

/-- **`SlabCutsBox` from the width inequality of the tilt-data construction.**  If `h > 0` and
`h + |u| < boxWidth s σ v` then the slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` really cuts the box: the box
pokes out of it strictly on both sides. -/
theorem slabCutsBox_of_width {s u h : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    (hs : 0 < s) (hh : 0 < h) (hW : h + |u| < Work.Drive.Mono.boxWidth s σ v) :
    Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v := by
  have hWpos : 0 < Work.Drive.Mono.boxWidth s σ v := by linarith [abs_nonneg u]
  refine ⟨Work.Drive.Mono.exists_cut_above s hs c σ v (h := h) (u := u) hWpos ?_,
    Work.Drive.Mono.exists_cut_below s hs c σ v (h := h) (u := u) hWpos ?_⟩
  · linarith [le_abs_self u]
  · linarith [neg_abs_le u]

/-- **The radius bound on the closure of the box.**  Every point of `closure (PBox s c σ)` is within
`5/2 * s` of the centre `c`. -/
theorem norm_sub_le_of_mem_closure_PBox {s : ℝ} (hs : 0 ≤ s) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {y : R3} (hy : y ∈ closure (Submission.PBox s c σ)) :
    ‖y - c‖ ≤ 5 / 2 * s := by
  have hsub : closure (Submission.PBox s c σ) ⊆ Metric.closedBall c (5 / 2 * s) :=
    closure_minimal (fun z hz => by
      have h := Submission.PBox_subset_ball s hs c σ hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at h)) Metric.isClosed_closedBall
  have h := hsub hy
  rwa [Metric.mem_closedBall, dist_eq_norm] at h

end

end Work.Drive.Mono
