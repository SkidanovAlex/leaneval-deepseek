import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Topology.SphereSlicing

/-- The box norm is continuous. -/
theorem frontier_PBox_boxNorm_continuous (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous fun y : R3 => Submission.boxNorm c σ y := by
  unfold Submission.boxNorm
  fun_prop

/-- The box norm is positively homogeneous along rays through the centre. -/
theorem frontier_PBox_boxNorm_homogeneous (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) (y : R3) :
    Submission.boxNorm c σ (c + t • (y - c)) = |t| * Submission.boxNorm c σ y := by
  have h0 : |(c + t • (y - c)) (σ 0) - c (σ 0)| / Submission.boxSide 0
      = |t| * (|y (σ 0) - c (σ 0)| / Submission.boxSide 0) := by
    have h : (c + t • (y - c)) (σ 0) - c (σ 0) = t * (y (σ 0) - c (σ 0)) := by simp
    rw [h, abs_mul, mul_div_assoc]
  have h1 : |(c + t • (y - c)) (σ 1) - c (σ 1)| / Submission.boxSide 1
      = |t| * (|y (σ 1) - c (σ 1)| / Submission.boxSide 1) := by
    have h : (c + t • (y - c)) (σ 1) - c (σ 1) = t * (y (σ 1) - c (σ 1)) := by simp
    rw [h, abs_mul, mul_div_assoc]
  have h2 : |(c + t • (y - c)) (σ 2) - c (σ 2)| / Submission.boxSide 2
      = |t| * (|y (σ 2) - c (σ 2)| / Submission.boxSide 2) := by
    have h : (c + t • (y - c)) (σ 2) - c (σ 2) = t * (y (σ 2) - c (σ 2)) := by simp
    rw [h, abs_mul, mul_div_assoc]
  rw [Submission.boxNorm, h0, h1, h2, ← mul_max_of_nonneg, ← mul_max_of_nonneg]
  · rfl
  · exact abs_nonneg t
  · exact abs_nonneg t

/-- The box norm vanishes at the centre. -/
theorem frontier_PBox_boxNorm_centre (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Submission.boxNorm c σ c = 0 := by
  simp [Submission.boxNorm]

theorem frontier_PBox {r : ℝ} (hr : 0 < r) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) :
    frontier (Submission.PBox r c σ) = Work.Topology.SphereSlicing.BoxSphere r c σ := by
  have hcont : Continuous fun y : R3 => Submission.boxNorm c σ y :=
    frontier_PBox_boxNorm_continuous c σ
  have hhom : ∀ (t : ℝ) (y : R3), Submission.boxNorm c σ (c + t • (y - c))
      = |t| * Submission.boxNorm c σ y := frontier_PBox_boxNorm_homogeneous c σ
  have hP : Submission.PBox r c σ = {y : R3 | Submission.boxNorm c σ y < r} := by
    ext y; exact Submission.mem_PBox_iff r c σ y
  rw [hP]
  unfold BoxSphere
  have hopen : IsOpen {y : R3 | Submission.boxNorm c σ y < r} :=
    isOpen_lt hcont continuous_const
  rw [hopen.frontier_eq]
  have hcl : closure {y : R3 | Submission.boxNorm c σ y < r}
      = {y : R3 | Submission.boxNorm c σ y ≤ r} := by
    apply le_antisymm
    · refine closure_minimal ?_ (isClosed_le hcont continuous_const)
      intro y hy
      exact le_of_lt (by simpa using hy)
    · intro y hy
      have hy' : Submission.boxNorm c σ y ≤ r := by simpa using hy
      rcases lt_or_eq_of_le hy' with hlt | heq
      · exact subset_closure (by simpa using hlt)
      · rw [Metric.mem_closure_iff]
        intro ε hε
        set δ : ℝ := min (ε / (2 * (‖y - c‖ + 1))) (1 / 2) with hδdef
        have hden : 0 < 2 * (‖y - c‖ + 1) := by positivity
        have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
        have hδle : δ ≤ ε / (2 * (‖y - c‖ + 1)) := min_le_left _ _
        have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
        have hδlt1 : δ < 1 := by linarith
        refine ⟨c + (1 - δ) • (y - c), ?_, ?_⟩
        · show Submission.boxNorm c σ (c + (1 - δ) • (y - c)) < r
          rw [hhom (1 - δ) y, abs_of_pos (by linarith : (0:ℝ) < 1 - δ), heq]
          nlinarith [hr, hδpos]
        · rw [dist_eq_norm]
          have hsub : y - (c + (1 - δ) • (y - c)) = δ • (y - c) := by module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
          have hnc : (0:ℝ) ≤ ‖y - c‖ := norm_nonneg _
          have hlt : δ * ‖y - c‖ < δ * (‖y - c‖ + 1) := by
            nlinarith [hδpos, hnc]
          have hle : δ * (‖y - c‖ + 1) ≤ ε / 2 := by
            have h1 : δ * (‖y - c‖ + 1) ≤ (ε / (2 * (‖y - c‖ + 1))) * (‖y - c‖ + 1) :=
              mul_le_mul_of_nonneg_right hδle (by positivity)
            have h2 : (ε / (2 * (‖y - c‖ + 1))) * (‖y - c‖ + 1) = ε / 2 := by
              field_simp
            linarith [h1, h2.le, h2.ge]
          linarith
  rw [hcl]
  ext y
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.mp h2)
  · intro h
    exact ⟨le_of_eq h, by rw [h]; exact lt_irrefl r⟩

end Work.Topology.SphereSlicing
