import Mathlib
import Submission.Work.Drive.Mono.SlabCaps

namespace Work.Drive.Mono

/-
# Points of the box above a level, arbitrarily close to a point of the closed box

If the open box `PBox s c σ` contains a point `y` above the level `lam` (`lam < ℓ y`) and `z` lies
in the *closed* box `closure (PBox s c σ)` at level at least `lam` (`lam ≤ ℓ z`), then every
neighbourhood of `z` contains a point `u` of the open box with `lam < ℓ u`.

The proof is convexity: the box is convex, `z` is in its closure and `y` is in its interior
(it is open), so the punctured segment `z + t • (y - z)`, `t ∈ (0,1]`, lies in the box
(`Convex.add_smul_sub_mem_interior'`).  The level along this segment is
`(1 - t) * ℓ z + t * ℓ y`, which exceeds `lam` strictly as soon as `t > 0`, and the point tends to
`z` as `t → 0⁺`.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem exists_mem_PBox_gt_level_near {s lam : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {z : R3}
    (habove : ∃ y : R3, y ∈ Submission.PBox s c σ ∧ lam < ℓ y)
    (hz : z ∈ closure (Submission.PBox s c σ)) (hzlam : lam ≤ ℓ z) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ Submission.PBox s c σ, dist u z < ε ∧ lam < ℓ u := by
  obtain ⟨y, hy, hly⟩ := habove
  -- a small positive parameter, small enough that the segment `z + t • (y - z)` stays within `ε`
  set t : ℝ := min (1 / 2) (ε / (2 * (‖y - z‖ + 1))) with ht_def
  have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht_le_one : t ≤ 1 := by
    have := min_le_left (1 / 2 : ℝ) (ε / (2 * (‖y - z‖ + 1)))
    linarith
  refine ⟨z + t • (y - z), ?_, ?_, ?_⟩
  · -- the point lies in the open box, by convexity: closure point + interior point
    have hcv : Convex ℝ (Submission.PBox s c σ) :=
      Work.Topology.SphereSlicing.convex_PBox s c σ
    have hopen : interior (Submission.PBox s c σ) = Submission.PBox s c σ :=
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq
    have h := hcv.add_smul_sub_mem_interior' hz (by rw [hopen]; exact hy) ⟨ht_pos, ht_le_one⟩
    rwa [hopen] at h
  · -- the point is within `ε` of `z`
    rw [dist_eq_norm]
    have hsub : z + t • (y - z) - z = t • (y - z) := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
    have hle : t ≤ ε / (2 * (‖y - z‖ + 1)) := min_le_right _ _
    have hnn : 0 ≤ ‖y - z‖ := norm_nonneg _
    have h2 : (ε / (2 * (‖y - z‖ + 1))) * ‖y - z‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖y - z‖ + 1))]
      nlinarith [hε, hnn]
    calc t * ‖y - z‖ ≤ (ε / (2 * (‖y - z‖ + 1))) * ‖y - z‖ :=
          mul_le_mul_of_nonneg_right hle hnn
      _ < ε := h2
  · -- the level along the segment is strictly above `lam`
    have hlin : ℓ (z + t • (y - z)) = ℓ z + t * (ℓ y - ℓ z) := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hlin]
    have h1 : 0 ≤ (1 - t) * (ℓ z - lam) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 < t * (ℓ y - lam) := mul_pos ht_pos (by linarith)
    have h3 : ℓ z + t * (ℓ y - ℓ z) - lam
        = (1 - t) * (ℓ z - lam) + t * (ℓ y - lam) := by ring
    linarith

end Work.Drive.Mono
