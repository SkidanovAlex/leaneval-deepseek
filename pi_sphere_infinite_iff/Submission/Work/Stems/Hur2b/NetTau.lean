import Mathlib
import Submission.Work.Stems.Hur2b.NetExitGeom

/-!
# The radial parameter `tau`

`tau y` is `0` on `∂D` and `1` on `∂I²`, so it can be used to contract the walk to the base vertex
`(0,0,0)` along the collar.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

theorem exitDist_eq_sNorm_of_Mmin {ζ : Fin 2 → ℝ} (h : Mmin ζ = 1) :
    exitDist ζ = sNorm ζ := by
  have h1 : rayOff ζ = ζ := by
    funext i
    simp only [rayOff, exitScale, h, one_div, inv_one, one_mul]
  rw [exitDist, h1]

/-- `tau` vanishes on `∂D`. -/
theorem tau_eq_zero {y : IC 2} (hy : y ∈ NetBdy) : tau y = 0 := by
  have h := exitDist_eq_sNorm_of_Mmin (Mmin_eq_one_of_mem_NetBdy hy)
  have h2 : tau y = clamp 0 := by
    rw [tau, h, sub_self, mul_zero]
  have h3 : ((clamp 0 : unitInterval) : ℝ) = 0 := by
    rw [clamp_coe_max]; norm_num
  rw [h2, h3]

theorem tauU_eq_zero {y : IC 2} (hy : y ∈ NetBdy) : tauU y = 0 := by
  apply Subtype.ext
  rw [tauU, tau_eq_zero hy, clamp_coe_max]
  norm_num

/-- The `ℓ∞`-norm of the offset is at least `7/16` on the boundary of the square. -/
theorem sNorm_offOf_ge (y : IC 2) (hy : y ∈ Cube.boundary (Fin 2)) : 7/16 ≤ sNorm (offOf y) := by
  obtain ⟨i, hi⟩ := hy
  have hcoe : ∀ u : unitInterval, u = 0 → (u : ℝ) = 0 := by
    intro u hu; rw [hu]; norm_num
  have hcoe1 : ∀ u : unitInterval, u = 1 → (u : ℝ) = 1 := by
    intro u hu; rw [hu]; norm_num
  rcases (show i = 0 ∨ i = 1 from by fin_cases i <;> simp) with hi0 | hi0
  · rw [hi0] at hi
    rw [sNorm]
    rcases hi with h | h
    · have h2 : |offOf y 0| = 7/16 := by rw [offOf_eq, hcoe _ h]; norm_num
      exact le_trans (le_of_eq h2.symm) (le_max_left _ _)
    · have h2 : |offOf y 0| = 9/16 := by rw [offOf_eq, hcoe1 _ h]; norm_num
      exact le_trans (by norm_num : (7/16:ℝ) ≤ 9/16)
        (le_trans (le_of_eq h2.symm) (le_max_left _ _))
  · rw [hi0] at hi
    rw [sNorm]
    rcases hi with h | h
    · have h2 : |offOf y 1| = 7/16 := by rw [offOf_eq, hcoe _ h]; norm_num
      exact le_trans (le_of_eq h2.symm) (le_max_right _ _)
    · have h2 : |offOf y 1| = 9/16 := by rw [offOf_eq, hcoe1 _ h]; norm_num
      exact le_trans (by norm_num : (7/16:ℝ) ≤ 9/16)
        (le_trans (le_of_eq h2.symm) (le_max_right _ _))

/-- `tau` is `1` on the boundary of the square. -/
theorem tau_eq_one {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) : tau y = 1 := by
  have h1 : 7/16 ≤ sNorm (offOf y) := sNorm_offOf_ge y hy
  have h2 : exitDist (offOf y) ≤ 5/16 := exitDist_le _
  have h3 : (1:ℝ) ≤ 8 * (sNorm (offOf y) - exitDist (offOf y)) := by linarith
  have h4 : tau y = clamp (8 * (sNorm (offOf y) - exitDist (offOf y))) := rfl
  have h5 : ((clamp (8 * (sNorm (offOf y) - exitDist (offOf y))) : unitInterval) : ℝ) = 1 := by
    rw [clamp_coe_max, min_eq_left h3, max_eq_right (by norm_num)]
  rw [h4, h5]

theorem tauU_eq_one {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) : tauU y = 1 := by
  apply Subtype.ext
  rw [tauU, tau_eq_one hy, clamp_coe_max]
  norm_num

/-! ## Continuity -/

theorem nu_eq_maxmin (l u c z : ℝ) :
    nu l u c z = max z 0 / (u - c) + min z 0 / (l - c) := by
  rw [nu]
  rcases le_or_gt 0 z with h | h
  · rw [if_pos h, max_eq_left h, min_eq_right h, zero_div, add_zero]
  · rw [if_neg (not_le.mpr h), max_eq_right h.le, min_eq_left h.le, zero_div, zero_add]

theorem continuous_nu (l u c : ℝ) : Continuous fun z : ℝ => nu l u c z := by
  have h : (fun z : ℝ => nu l u c z) =
      fun z => max z 0 / (u - c) + min z 0 / (l - c) := by
    funext z; exact nu_eq_maxmin l u c z
  rw [h]
  fun_prop

theorem continuous_Mmin : Continuous Mmin := by
  have h : Mmin = fun z : Fin 2 → ℝ =>
      min (max (nuB0 (z 0)) (nuB1 (z 1))) (max (nuC0 (z 0)) (nuC1 (z 1))) := rfl
  rw [h]
  refine Continuous.min (Continuous.max ?_ ?_) (Continuous.max ?_ ?_)
  · exact (continuous_nu _ _ _).comp (continuous_apply 0)
  · exact (continuous_nu _ _ _).comp (continuous_apply 1)
  · exact (continuous_nu _ _ _).comp (continuous_apply 0)
  · exact (continuous_nu _ _ _).comp (continuous_apply 1)

theorem continuousOn_exitScale : ContinuousOn exitScale {z : Fin 2 → ℝ | z ≠ 0} := by
  have h : exitScale = fun z : Fin 2 → ℝ => 1 / Mmin z := rfl
  rw [h]
  refine ContinuousOn.div continuousOn_const continuous_Mmin.continuousOn ?_
  intro z hz
  exact ne_of_gt (Mmin_pos hz)

theorem continuousOn_exitDist_offOf :
    ContinuousOn (fun y : IC 2 => exitDist (offOf y)) {y : IC 2 | offOf y ≠ 0} := by
  have hz : ContinuousOn (fun y : IC 2 => offOf y) {y : IC 2 | offOf y ≠ 0} :=
    (continuous_pi (fun i => continuous_offOf i)).continuousOn
  have h1 : ContinuousOn (fun y : IC 2 => exitScale (offOf y)) {y : IC 2 | offOf y ≠ 0} :=
    continuousOn_exitScale.comp hz (fun y hy => hy)
  have h2 : ContinuousOn (fun y : IC 2 => rayOff (offOf y)) {y : IC 2 | offOf y ≠ 0} := by
    have h3 : ContinuousOn (fun y : IC 2 => fun i => exitScale (offOf y) * offOf y i)
        {y : IC 2 | offOf y ≠ 0} := by
      refine continuousOn_pi.mpr fun i => ?_
      exact h1.mul (continuous_offOf i).continuousOn
    convert h3 using 2
    funext i
    rfl
  have hsn : Continuous sNorm :=
    show Continuous fun z : Fin 2 → ℝ => max |z 0| |z 1| from
      (continuous_apply 0).abs.max (continuous_apply 1).abs
  have h4 : (fun y : IC 2 => exitDist (offOf y)) = fun y => sNorm (rayOff (offOf y)) := rfl
  rw [h4]
  exact hsn.continuousOn.comp h2 (fun y _ => Set.mem_univ _)

/-- `tau` is continuous wherever the offset does not vanish (in particular on the collar). -/
theorem continuousOn_tau : ContinuousOn tau {y : IC 2 | offOf y ≠ 0} := by
  have hfun : tau = fun y : IC 2 =>
      ((clamp (8 * (sNorm (offOf y) - exitDist (offOf y))) : unitInterval) : ℝ) := by
    funext y; rfl
  rw [hfun]
  have h1 : Continuous fun y : IC 2 => sNorm (offOf y) :=
    show Continuous fun y : IC 2 => max |offOf y 0| |offOf y 1| from
      (continuous_offOf 0).abs.max (continuous_offOf 1).abs
  exact continuous_subtype_val.comp_continuousOn (continuous_clamp.comp_continuousOn
    (continuousOn_const.mul (h1.continuousOn.sub continuousOn_exitDist_offOf)))

end

end Work.Stems.Hur2b
