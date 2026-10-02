import Mathlib
import Submission.Work.Whitney.RankTwo.Geom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The faces of the hexagon sectors

The face computations `δ 0 S_k = arc k`, `δ 1 S_k = rad (k+1)`, `δ 2 S_k = rad k` and the
consequence `d Z = c` for the chain `Z = Σ_k S_k` and the cycle `c = Σ_k arc k`.
-/

namespace Work.Whitney.RankTwo

open Work.Thom
open CategoryTheory AlgebraicTopology
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-! ## Coordinates of the face maps on `Δ¹` -/

theorem map_succAbove_zero_apply_zero (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (0 : Fin 3).succAbove q) 0 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp

theorem map_succAbove_zero_apply_one (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (0 : Fin 3).succAbove q) 1 = q 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : (Finset.univ.filter (fun x : Fin 2 => (0 : Fin 3).succAbove x = 1)) = {0} := by decide
  rw [h]; simp

theorem map_succAbove_zero_apply_two (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (0 : Fin 3).succAbove q) 2 = q 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : (Finset.univ.filter (fun x : Fin 2 => (0 : Fin 3).succAbove x = 2)) = {1} := by decide
  rw [h]; simp

theorem map_succAbove_one_apply_one (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (1 : Fin 3).succAbove q) 1 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp

theorem map_succAbove_one_apply_two (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (1 : Fin 3).succAbove q) 2 = q 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : (Finset.univ.filter (fun x : Fin 2 => (1 : Fin 3).succAbove x = 2)) = {1} := by decide
  rw [h]; simp

theorem map_succAbove_two_apply_one (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (2 : Fin 3).succAbove q) 1 = q 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : (Finset.univ.filter (fun x : Fin 2 => (2 : Fin 3).succAbove x = 1)) = {1} := by decide
  rw [h]; simp

theorem map_succAbove_two_apply_two (q : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (2 : Fin 3).succAbove q) 2 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp

/-- For `q ∈ Δ¹` the coordinates `q 0` and `q 1` sum to `1`. -/
theorem sum_two (q : stdSimplex ℝ (Fin 2)) : q 0 + q 1 = 1 := by
  rw [← Fin.sum_univ_two]; exact stdSimplex.sum_eq_one q

/-! ## The three faces of a sector -/

theorem secC_face_zero (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    secC Y y k (stdSimplex.map (0 : Fin 3).succAbove q) = arcC Y y k q := by
  have h1 := map_succAbove_zero_apply_one q
  have h2 := map_succAbove_zero_apply_two q
  simp only [secC, arcC, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    coord_apply, fibConeCM_apply, h1, h2, sum_two q]

theorem secC_face_one (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    secC Y y k (stdSimplex.map (1 : Fin 3).succAbove q) = radC Y y (k + 1) q := by
  have h1 := map_succAbove_one_apply_one q
  have h2 := map_succAbove_one_apply_two q
  simp only [secC, radC, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    coord_apply, fibConeCM_apply, h1, h2]
  refine Prod.ext rfl ?_
  congr 1
  refine Prod.ext ?_ ?_ <;> ring

theorem secC_face_two (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    secC Y y k (stdSimplex.map (2 : Fin 3).succAbove q) = radC Y y k q := by
  have h1 := map_succAbove_two_apply_one q
  have h2 := map_succAbove_two_apply_two q
  simp only [secC, radC, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    coord_apply, fibConeCM_apply, h1, h2]
  refine Prod.ext rfl ?_
  congr 1
  refine Prod.ext ?_ ?_ <;> ring

/-! ## The same, on the singular simplicial set -/

theorem ssX_δ_zero_secSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 0 (secSimp Y y k) = arcSimp Y y k := by
  apply ssX_ext
  intro z
  rw [ssX_δ_apply, sEquiv_secSimp, sEquiv_arcSimp, secC_face_zero]

theorem ssX_δ_one_secSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 1 (secSimp Y y k) = radSimp Y y (k + 1) := by
  apply ssX_ext
  intro z
  rw [ssX_δ_apply, sEquiv_secSimp, sEquiv_radSimp, secC_face_one]

theorem ssX_δ_two_secSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 2 (secSimp Y y k) = radSimp Y y k := by
  apply ssX_ext
  intro z
  rw [ssX_δ_apply, sEquiv_secSimp, sEquiv_radSimp, secC_face_two]

end

end Work.Whitney.RankTwo
