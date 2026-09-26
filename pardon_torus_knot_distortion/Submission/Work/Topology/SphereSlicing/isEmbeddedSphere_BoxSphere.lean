import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous
import Submission.Work.Topology.SphereSlicing.boxNorm_homogeneous

namespace Work.Topology.SphereSlicing

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-!
# The box sphere is an embedded sphere

The box sphere `BoxSphere s c σ = {y | boxNorm c σ y = s}` (`s > 0`) is the boundary of Pardon's
box `PBox s c σ`, a polyhedral `S²`.  Here we exhibit the radial parametrisation

`boxSpherePoint s c σ w = c + (s / boxNorm c σ (c + w)) • w`

of the unit sphere onto it: the ray from the centre `c` in the direction of the unit vector `w`
meets the boundary `{boxNorm = s}` at parameter `s / boxNorm c σ (c + w)`, by positive
homogeneity of the box norm about the centre.  This map is continuous, injective (the direction
is recovered from `(φ w - c) / ‖φ w - c‖`) and surjective, which is exactly
`Work.InnermostDisk.IsEmbeddedSphere (BoxSphere s c σ)`.
-/

/-- The box norm about the centre: `boxNorm c σ (c + z) = maxᵢ |z (σ i)| / boxSide i`. -/
theorem boxNorm_centre_add (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) :
    Submission.boxNorm c σ (c + z)
      = max (max (|z (σ 0)| / Submission.boxSide 0) (|z (σ 1)| / Submission.boxSide 1))
          (|z (σ 2)| / Submission.boxSide 2) := by
  have h : ∀ i : Fin 3, |(c + z) (σ i) - c (σ i)| / Submission.boxSide i
      = |z (σ i)| / Submission.boxSide i := by
    intro i
    rw [show (c + z) (σ i) - c (σ i) = z (σ i) by simp]
  rw [Submission.boxNorm, h 0, h 1, h 2]

/-- Each of the three terms of the box norm about `c` is bounded by it. -/
theorem le_boxNorm_centre_add (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) :
    ∀ j : Fin 3, |z (σ j)| / Submission.boxSide j ≤ Submission.boxNorm c σ (c + z) := by
  intro j
  rw [boxNorm_centre_add]
  fin_cases j
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- The box norm about `c`: scaling from `c` multiplies it by `|t|`. -/
theorem boxNorm_centre_smul (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) (z : R3) :
    Submission.boxNorm c σ (c + t • z) = |t| * Submission.boxNorm c σ (c + z) := by
  have h := boxNorm_homogeneous c σ t (c + z)
  simpa using h

/-- The box norm about `c` is positive away from `c`. -/
theorem boxNorm_centre_add_pos {c : R3} {σ : Equiv.Perm (Fin 3)} {z : R3} (hz : z ≠ 0) :
    0 < Submission.boxNorm c σ (c + z) := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by ext i; exact h i)
  have hpos : 0 < |z i| / Submission.boxSide (σ.symm i) :=
    div_pos (abs_pos.mpr hi) (Submission.boxSide_pos _)
  have hle := le_boxNorm_centre_add c σ z (σ.symm i)
  have hEq : |z i| / Submission.boxSide (σ.symm i)
      = |z (σ (σ.symm i))| / Submission.boxSide (σ.symm i) := by simp
  rw [hEq] at hpos
  exact lt_of_lt_of_le hpos hle

/-- The box norm about `c` is positive on the direction of a unit vector. -/
theorem boxNorm_centre_add_pos_sphere (c : R3) (σ : Equiv.Perm (Fin 3))
    (w : Metric.sphere (0 : R3) 1) : 0 < Submission.boxNorm c σ (c + (w : R3)) := by
  refine boxNorm_centre_add_pos ?_
  intro hw
  have h1 : ‖(w : R3)‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
  rw [hw] at h1
  simp at h1

/-- The box norm vanishes at the centre. -/
theorem boxNorm_centre_self (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Submission.boxNorm c σ c = 0 := by
  simp [Submission.boxNorm]

/-- **The radial parametrisation of the box sphere**: the point where the ray from the centre
`c` in the direction of the unit vector `w` meets the boundary `{boxNorm = s}`. -/
def boxSpherePoint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (w : Metric.sphere (0 : R3) 1) : R3 :=
  c + (s / Submission.boxNorm c σ (c + (w : R3))) • (w : R3)

theorem boxSpherePoint_apply (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (w : Metric.sphere (0 : R3) 1) :
    boxSpherePoint s c σ w
      = c + (s / Submission.boxNorm c σ (c + (w : R3))) • (w : R3) := rfl

theorem continuous_boxSpherePoint (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (boxSpherePoint s c σ) := by
  rw [show boxSpherePoint s c σ = fun w : Metric.sphere (0 : R3) 1 =>
      c + (s / Submission.boxNorm c σ (c + (w : R3))) • (w : R3) from rfl]
  have h1 : Continuous fun w : Metric.sphere (0 : R3) 1 =>
      Submission.boxNorm c σ (c + (w : R3)) :=
    (boxNorm_continuous c σ).comp (continuous_const.add continuous_subtype_val)
  have h2 : Continuous fun w : Metric.sphere (0 : R3) 1 =>
      s / Submission.boxNorm c σ (c + (w : R3)) :=
    continuous_const.div h1 fun w => ne_of_gt (boxNorm_centre_add_pos_sphere c σ w)
  exact continuous_const.add (h2.smul continuous_subtype_val)

/-- The radial parametrisation lands on the box sphere. -/
theorem boxSpherePoint_mem {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (w : Metric.sphere (0 : R3) 1) : boxSpherePoint s c σ w ∈ BoxSphere s c σ := by
  have hpos := boxNorm_centre_add_pos_sphere c σ w
  show Submission.boxNorm c σ (c + (s / Submission.boxNorm c σ (c + (w : R3))) • (w : R3))
      = s
  rw [boxNorm_centre_smul, abs_of_pos (div_pos hs hpos), div_mul_cancel₀ s (ne_of_gt hpos)]

/-- The radial parametrisation is injective: the direction is recovered from `φ w - c`. -/
theorem boxSpherePoint_injective {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (boxSpherePoint s c σ) := by
  have key : ∀ u : Metric.sphere (0 : R3) 1,
      (u : R3) = (‖boxSpherePoint s c σ u - c‖)⁻¹ • (boxSpherePoint s c σ u - c) := by
    intro u
    have hpos := boxNorm_centre_add_pos_sphere c σ u
    have ht : 0 < s / Submission.boxNorm c σ (c + (u : R3)) := div_pos hs hpos
    have hsub : boxSpherePoint s c σ u - c
        = (s / Submission.boxNorm c σ (c + (u : R3))) • (u : R3) := by
      show c + (s / Submission.boxNorm c σ (c + (u : R3))) • (u : R3) - c = _
      abel
    have hnorm : ‖boxSpherePoint s c σ u - c‖
        = s / Submission.boxNorm c σ (c + (u : R3)) := by
      rw [hsub, norm_smul, Real.norm_of_nonneg ht.le,
        mem_sphere_zero_iff_norm.mp u.2, mul_one]
    rw [hnorm, hsub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  intro w w' h
  exact Subtype.ext (by rw [key w, key w', h])

/-- The radial parametrisation is surjective onto the box sphere. -/
theorem boxSpherePoint_surjective {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ y ∈ BoxSphere s c σ, ∃ w : Metric.sphere (0 : R3) 1, boxSpherePoint s c σ w = y := by
  intro y hy
  have hy' : Submission.boxNorm c σ y = s := hy
  have hvne : y - c ≠ 0 := by
    intro h
    have hyc : y = c := sub_eq_zero.mp h
    rw [hyc, boxNorm_centre_self c σ] at hy'
    exact (ne_of_gt hs) hy'.symm
  have hr : 0 < ‖y - c‖ := norm_pos_iff.mpr hvne
  refine ⟨⟨(‖y - c‖)⁻¹ • (y - c), ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      inv_mul_cancel₀ (ne_of_gt hr)]
  · show c + (s / Submission.boxNorm c σ (c + (‖y - c‖)⁻¹ • (y - c))) •
        ((‖y - c‖)⁻¹ • (y - c)) = y
    have hhom : Submission.boxNorm c σ (c + (‖y - c‖)⁻¹ • (y - c))
        = (‖y - c‖)⁻¹ * s := by
      rw [boxNorm_centre_smul, abs_of_pos (inv_pos.mpr hr)]
      rw [show c + (y - c) = y by abel, hy']
    rw [hhom]
    have hdiv : s / ((‖y - c‖)⁻¹ * s) = ‖y - c‖ := by
      rw [div_eq_iff (mul_ne_zero (inv_ne_zero (ne_of_gt hr)) (ne_of_gt hs))]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul]
    rw [hdiv, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    abel

theorem isEmbeddedSphere_BoxSphere {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.InnermostDisk.IsEmbeddedSphere (Work.Topology.SphereSlicing.BoxSphere s c σ) := by
  refine ⟨⟨boxSpherePoint s c σ, continuous_boxSpherePoint s c σ⟩,
    boxSpherePoint_injective hs c σ, ?_⟩
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact boxSpherePoint_mem hs c σ w
  · intro hy
    exact boxSpherePoint_surjective hs c σ y hy

end

end Work.Topology.SphereSlicing
