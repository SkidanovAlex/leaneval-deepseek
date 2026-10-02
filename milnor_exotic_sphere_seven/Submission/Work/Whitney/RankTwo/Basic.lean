import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.RankTwo.Eval
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.MVcapSquares

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney.RankTwo
open Work.Thom
open Work.Cohomology

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-! ## The coordinate hyperplanes -/

theorem ofLp_zero_iff (v : EuclideanSpace ℝ (Fin 1)) : v.ofLp 0 = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h' : WithLp.ofLp v = WithLp.ofLp (0 : EuclideanSpace ℝ (Fin 1)) := by
      funext i
      fin_cases i
      exact h
    exact WithLp.ofLp_injective 2 h'
  · rintro rfl; rfl

theorem coordA_ne_zero_iff (x : X Y) : coordA Y x ≠ 0 ↔ x ∈ tcmA Y 1 1 := by
  rw [coordA_eq]
  exact not_congr (ofLp_zero_iff (x.2.1))

theorem coordB_ne_zero_iff (x : X Y) : coordB Y x ≠ 0 ↔ x ∈ tcmC Y 1 1 := by
  rw [coordB_eq]
  exact not_congr (ofLp_zero_iff (x.2.2))

/-! ## Coordinates of the arcs -/

theorem arcC_apply (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    arcC Y y k q
      = (y, (tcmSumLin 1 1).symm (u2 (ang k * q 0 + ang (k + 1) * q 1))) := by
  simp only [arcC, ContinuousMap.prod_eval, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    ContinuousMap.mul_apply, ContinuousMap.add_apply, coord_apply, fibConeCM_apply, fibConeP]
  have h := fibCone_ray 1 (ang k * q 0 + ang (k + 1) * q 1)
  simpa using h

theorem coordA_fibCone_symm (y : Y) (θ : ℝ) :
    coordA Y (y, (tcmSumLin 1 1).symm (u2 θ)) = Real.cos θ := by
  rw [coordA_eq]
  show (((tcmSumLin 1 1).symm (u2 θ)).1).ofLp 0 = Real.cos θ
  rw [tcmSumLin_symm_fst, u2_apply_zero]
  show (Real.cos θ • one1).ofLp 0 = Real.cos θ
  rw [WithLp.ofLp_smul, one1, Work.Cohomology.s0N, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul, mul_one]

theorem coordB_fibCone_symm (y : Y) (θ : ℝ) :
    coordB Y (y, (tcmSumLin 1 1).symm (u2 θ)) = Real.sin θ := by
  rw [coordB_eq]
  show (((tcmSumLin 1 1).symm (u2 θ)).2).ofLp 0 = Real.sin θ
  rw [tcmSumLin_symm_snd, u2_apply_one]
  show (Real.sin θ • one1).ofLp 0 = Real.sin θ
  rw [WithLp.ofLp_smul, one1, Work.Cohomology.s0N, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul, mul_one]

theorem coordA_arcC (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    coordA Y (arcC Y y k q) = Real.cos (ang k * q 0 + ang (k + 1) * q 1) := by
  rw [arcC_apply]
  exact coordA_fibCone_symm Y y _

theorem coordB_arcC (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    coordB Y (arcC Y y k q) = Real.sin (ang k * q 0 + ang (k + 1) * q 1) := by
  rw [arcC_apply]
  exact coordB_fibCone_symm Y y _

/-- The angle of the arc at parameter `q`, written in terms of `q 1` only. -/
theorem arcC_angle (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    ang k * q 0 + ang (k + 1) * q 1 = ang k + q 1 * (Real.pi / 3) := by
  have hsum : q 0 + q 1 = 1 := by
    have h := q.2.2
    rw [Fin.sum_univ_two] at h
    exact h
  have h : ang (k + 1) = ang k + Real.pi / 3 := by
    simp only [ang]; push_cast; ring
  rw [h]
  linear_combination (ang k) * hsum

/-- The angle of the arc lies in `[k π / 3, (k+1) π / 3]`. -/
theorem arcC_angle_bounds (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    (k : ℝ) * Real.pi / 3 ≤ ang k * q 0 + ang (k + 1) * q 1 ∧
      ang k * q 0 + ang (k + 1) * q 1 ≤ ((k : ℝ) + 1) * Real.pi / 3 := by
  have h1 : 0 ≤ q 1 := q.2.1 1
  have h2 : q 1 ≤ 1 := by
    have hsum : q 0 + q 1 = 1 := by
      have h := q.2.2
      rw [Fin.sum_univ_two] at h
      exact h
    have h0 : 0 ≤ q 0 := q.2.1 0
    linarith
  have key : ang k * q 0 + ang (k + 1) * q 1
      = (k : ℝ) * Real.pi / 3 + q 1 * (Real.pi / 3) := by
    rw [arcC_angle]
    simp only [ang]
    try ring_nf
  rw [key]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor <;> nlinarith

/-! ## Each arc avoids one of the two coordinate hyperplanes -/

theorem arcMem_zero (y : Y) (q : stdSimplex ℝ (Fin 2)) : coordA Y (arcC Y y 0 q) ≠ 0 := by
  obtain ⟨h1, h2⟩ := arcC_angle_bounds 0 q
  norm_num at h1 h2
  rw [coordA_arcC]
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem arcMem_one (y : Y) (q : stdSimplex ℝ (Fin 2)) : coordB Y (arcC Y y 1 q) ≠ 0 := by
  obtain ⟨h1, h2⟩ := arcC_angle_bounds 1 q
  norm_num at h1 h2
  rw [coordB_arcC]
  apply ne_of_gt
  apply Real.sin_pos_of_mem_Ioo
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem arcMem_two (y : Y) (q : stdSimplex ℝ (Fin 2)) : coordA Y (arcC Y y 2 q) ≠ 0 := by
  obtain ⟨h1, h2⟩ := arcC_angle_bounds 2 q
  norm_num at h1 h2
  rw [coordA_arcC]
  apply ne_of_lt
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem arcMem_three (y : Y) (q : stdSimplex ℝ (Fin 2)) : coordA Y (arcC Y y 3 q) ≠ 0 := by
  obtain ⟨h1, h2⟩ := arcC_angle_bounds 3 q
  norm_num at h1 h2
  rw [coordA_arcC]
  apply ne_of_lt
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem arcMem_four (y : Y) (q : stdSimplex ℝ (Fin 2)) : coordB Y (arcC Y y 4 q) ≠ 0 := by
  obtain ⟨h1, h2⟩ := arcC_angle_bounds 4 q
  norm_num at h1 h2
  have hsin : Real.sin (ang 4 * q 0 + ang (4 + 1) * q 1)
      = Real.sin (ang 4 * q 0 + ang 5 * q 1 - 2 * Real.pi) := by
    rw [show ang (4 + 1) = ang 5 from rfl]
    exact (Real.sin_sub_two_pi _).symm
  rw [coordB_arcC, hsin]
  apply ne_of_lt
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem arcMem_five (y : Y) (q : stdSimplex ℝ (Fin 2)) : coordA Y (arcC Y y 5 q) ≠ 0 := by
  obtain ⟨h1, h2⟩ := arcC_angle_bounds 5 q
  norm_num at h1 h2
  have hcos : Real.cos (ang 5 * q 0 + ang (5 + 1) * q 1)
      = Real.cos (ang 5 * q 0 + ang 6 * q 1 - 2 * Real.pi) := by
    rw [show ang (5 + 1) = ang 6 from rfl]
    exact (Real.cos_sub_two_pi _).symm
  rw [coordA_arcC, hcos]
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-! ## The arcs lie in `A` or in `C` -/

theorem arcSimp_image_subset_A (y : Y) {k : ℕ}
    (hk : k ∈ ({0, 2, 3, 5} : Finset ℕ)) :
    Set.range (fun q : stdSimplex ℝ (Fin (1 + 1)) => (sEquiv Y 1) (arcSimp Y y k) q)
      ⊆ tcmA Y 1 1 := by
  rintro x ⟨q, rfl⟩
  rw [sEquiv_arcSimp, ← coordA_ne_zero_iff]
  rcases (show k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 5 by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    tauto) with rfl | rfl | rfl | rfl
  · exact arcMem_zero Y y q
  · exact arcMem_two Y y q
  · exact arcMem_three Y y q
  · exact arcMem_five Y y q

theorem arcSimp_image_subset_C (y : Y) {k : ℕ}
    (hk : k ∈ ({1, 4} : Finset ℕ)) :
    Set.range (fun q : stdSimplex ℝ (Fin (1 + 1)) => (sEquiv Y 1) (arcSimp Y y k) q)
      ⊆ tcmC Y 1 1 := by
  rintro x ⟨q, rfl⟩
  rw [sEquiv_arcSimp, ← coordB_ne_zero_iff]
  rcases (show k = 1 ∨ k = 4 by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    tauto) with rfl | rfl
  · exact arcMem_one Y y q
  · exact arcMem_four Y y q

end
end Work.Whitney.RankTwo
