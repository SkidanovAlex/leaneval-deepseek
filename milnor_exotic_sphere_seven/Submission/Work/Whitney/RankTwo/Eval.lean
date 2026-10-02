import Mathlib
import Submission.Work.Whitney.RankTwo.Cochains
import Submission.Work.Whitney.RankTwo.posOf_const_of_continuous_ne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The cup-side evaluation on the hexagon sectors

The vertices of the sectors, the faces of the arcs and radial segments as `0`-simplices, and the
evaluation `Σ_k (α ⌣ β)(S_k) = 1` of the Alexander–Whitney product of the two sign cochains.
-/

namespace Work.Whitney.RankTwo

open Work.Thom
open Work.Cohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

set_option linter.unusedSectionVars false

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-! ## The vertices of the sectors -/

theorem coordA_vtx (y : Y) (k : ℕ) : coordA Y (vtx Y y k) = Real.cos (ang k) := by
  simp only [coordA, vtx, fibCone, ContinuousLinearEquiv.apply_symm_apply, u2]
  rw [one_smul, div_one, WithLp.ofLp_toLp, Matrix.cons_val_zero]

theorem coordB_vtx (y : Y) (k : ℕ) : coordB Y (vtx Y y k) = Real.sin (ang k) := by
  simp only [coordB, vtx, fibCone, ContinuousLinearEquiv.apply_symm_apply, u2]
  rw [one_smul, div_one, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The `k`-th vertex as a point of the fibre. -/
theorem fibCone_vtx (y : Y) (k : ℕ) : (vtx Y y k).2 = (tcmSumLin 1 1).symm (u2 (ang k)) := by
  simp [vtx, fibCone]

/-- The base point of `X` (the origin of the fibre over `y`). -/
def origin (y : Y) : X Y := (y, 0)

theorem coordA_origin (y : Y) : coordA Y (origin Y y) = 0 := by
  simp [coordA, origin]

theorem coordB_origin (y : Y) : coordB Y (origin Y y) = 0 := by
  simp [coordB, origin]

/-! ## The `0`-simplex at a point -/

/-- The `0`-simplex of `X` at a point. -/
noncomputable def ptSimp (x : X Y) : (ssX Y) _⦋0⦌ :=
  (sEquiv Y 0).symm (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x)

@[simp] theorem sEquiv_ptSimp (x : X Y) :
    sEquiv Y 0 (ptSimp Y x) = ContinuousMap.const (stdSimplex ℝ (Fin 1)) x :=
  (sEquiv Y 0).apply_symm_apply _

theorem ptSimp_default (x : X Y) : (sEquiv Y 0 (ptSimp Y x)) default = x := rfl

@[simp] theorem genEval_alpha0_ptSimp (x : X Y) :
    genEval ℤ (ssX Y) (alpha0 Y) (ptSimp Y x) = posOf (coordA Y x) := by
  rw [genEval_alpha0, ptSimp_default]

@[simp] theorem genEval_beta0_ptSimp (x : X Y) :
    genEval ℤ (ssX Y) (beta0 Y) (ptSimp Y x) = posOf (coordB Y x) := by
  rw [genEval_beta0, ptSimp_default]

/-! ## The faces of arcs and radial segments as `0`-simplices -/

theorem map_succAbove0_zero (z : stdSimplex ℝ (Fin 1)) :
    (stdSimplex.map (0 : Fin 2).succAbove z) 0 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp

theorem map_succAbove0_one (z : stdSimplex ℝ (Fin 1)) :
    (stdSimplex.map (0 : Fin 2).succAbove z) 1 = 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : (Finset.univ.filter (fun x : Fin 1 => (0 : Fin 2).succAbove x = 1)) = Finset.univ :=
    rfl
  rw [h, Fin.sum_univ_one]
  have := stdSimplex.sum_eq_one z
  rwa [Fin.sum_univ_one] at this

theorem map_succAbove1_zero (z : stdSimplex ℝ (Fin 1)) :
    (stdSimplex.map (1 : Fin 2).succAbove z) 0 = 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have h : (Finset.univ.filter (fun x : Fin 1 => (1 : Fin 2).succAbove x = 0)) = Finset.univ :=
    rfl
  rw [h, Fin.sum_univ_one]
  have := stdSimplex.sum_eq_one z
  rwa [Fin.sum_univ_one] at this

theorem map_succAbove1_one (z : stdSimplex ℝ (Fin 1)) :
    (stdSimplex.map (1 : Fin 2).succAbove z) 1 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp

theorem arcC_vertex (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) (h0 : q 0 = 0) (h1 : q 1 = 1) :
    arcC Y y k q = vtx Y y (k + 1) := by
  simp only [arcC, vtx, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    coord_apply, fibConeCM_apply, fibConeP, h0, h1]
  norm_num

theorem arcC_start (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) (h0 : q 0 = 1) (h1 : q 1 = 0) :
    arcC Y y k q = vtx Y y k := by
  simp only [arcC, vtx, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    coord_apply, fibConeCM_apply, fibConeP, h0, h1]
  norm_num

theorem radC_end (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) (h1 : q 1 = 1) :
    radC Y y k q = vtx Y y k := by
  simp only [radC, vtx, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, coord_apply, fibConeCM_apply, fibConeP, h1]
  norm_num

theorem radC_start (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) (h1 : q 1 = 0) :
    radC Y y k q = origin Y y := by
  simp only [radC, origin, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, coord_apply, fibConeCM_apply, fibConeP, h1, fibCone]
  norm_num

theorem ssX_δ_zero_arcSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 0 (arcSimp Y y k) = ptSimp Y (vtx Y y (k + 1)) := by
  apply (sEquiv Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [ssX_δ_apply, sEquiv_arcSimp, sEquiv_ptSimp]
  exact arcC_vertex Y y k _ (map_succAbove0_zero z) (map_succAbove0_one z)

theorem ssX_δ_one_arcSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 1 (arcSimp Y y k) = ptSimp Y (vtx Y y k) := by
  apply (sEquiv Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [ssX_δ_apply, sEquiv_arcSimp, sEquiv_ptSimp]
  exact arcC_start Y y k _ (map_succAbove1_zero z) (map_succAbove1_one z)

theorem ssX_δ_zero_radSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 0 (radSimp Y y k) = ptSimp Y (vtx Y y k) := by
  apply (sEquiv Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [ssX_δ_apply, sEquiv_radSimp, sEquiv_ptSimp]
  exact radC_end Y y k _ (map_succAbove0_one z)

theorem ssX_δ_one_radSimp (y : Y) (k : ℕ) :
    (ssX Y).δ 1 (radSimp Y y k) = ptSimp Y (origin Y y) := by
  apply (sEquiv Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [ssX_δ_apply, sEquiv_radSimp, sEquiv_ptSimp]
  exact radC_start Y y k _ (map_succAbove1_one z)

/-! ## The front and back faces of a sector -/

theorem frontIncl_one_two : frontIncl 1 2 (by norm_num) = SimplexCategory.δ (2 : Fin 3) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  fin_cases j <;> rfl

theorem backIncl_one_one : backIncl 1 1 = SimplexCategory.δ (0 : Fin 3) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  fin_cases j <;> rfl

theorem frontFace_secSimp (y : Y) (k : ℕ) :
    frontFace (ssX Y) 1 2 (by norm_num) (secSimp Y y k) = radSimp Y y k := by
  rw [frontFace, frontIncl_one_two]
  exact ssX_δ_two_secSimp Y y k

theorem backFace_secSimp (y : Y) (k : ℕ) :
    backFace (ssX Y) 1 1 (secSimp Y y k) = arcSimp Y y k := by
  rw [backFace, backIncl_one_one]
  exact ssX_δ_zero_secSimp Y y k

/-! ## The differentials of the sign cochains on arcs and radial segments -/

theorem alpha0_chain (σ : (ssX Y) _⦋1⦌) :
    (alpha0 Y) ((((ssX Y).chainComplex zR).d 1 0).hom
        (((ssX Y).ιChainComplex (R := zR) σ).hom 1))
      = (alpha0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 0 σ)).hom 1)
        - (alpha0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 1 σ)).hom 1) := by
  show (alpha0 Y) ((((ssX Y).chainComplex zR).d (0+1) 0).hom
        (((ssX Y).ιChainComplex (R := zR) σ).hom 1))
      = (alpha0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 0 σ)).hom 1)
        - (alpha0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 1 σ)).hom 1)
  have h := congrArg (fun (g : zR ⟶ ((ssX Y).chainComplex zR).X 0) => g.hom (1 : zR))
    (SSet.ιChainComplex_d (ssX Y) zR σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  rw [Fin.sum_univ_two]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply]
  norm_num
  rw [sub_eq_add_neg]

theorem beta0_chain (σ : (ssX Y) _⦋1⦌) :
    (beta0 Y) ((((ssX Y).chainComplex zR).d 1 0).hom
        (((ssX Y).ιChainComplex (R := zR) σ).hom 1))
      = (beta0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 0 σ)).hom 1)
        - (beta0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 1 σ)).hom 1) := by
  show (beta0 Y) ((((ssX Y).chainComplex zR).d (0+1) 0).hom
        (((ssX Y).ιChainComplex (R := zR) σ).hom 1))
      = (beta0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 0 σ)).hom 1)
        - (beta0 Y) (((ssX Y).ιChainComplex (R := zR) ((ssX Y).δ 1 σ)).hom 1)
  have h := congrArg (fun (g : zR ⟶ ((ssX Y).chainComplex zR).X 0) => g.hom (1 : zR))
    (SSet.ιChainComplex_d (ssX Y) zR σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  rw [Fin.sum_univ_two]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply]
  norm_num
  rw [sub_eq_add_neg]

theorem alpha0_ι_ptSimp (x : X Y) :
    (alpha0 Y) (((ssX Y).ιChainComplex (R := zR) (ptSimp Y x)).hom 1) = posOf (coordA Y x) :=
  genEval_alpha0_ptSimp Y x

theorem beta0_ι_ptSimp (x : X Y) :
    (beta0 Y) (((ssX Y).ιChainComplex (R := zR) (ptSimp Y x)).hom 1) = posOf (coordB Y x) :=
  genEval_beta0_ptSimp Y x

theorem genEval_alpha_radSimp (y : Y) (k : ℕ) :
    genEval ℤ (ssX Y) (alpha Y) (radSimp Y y k) = posOf (coordA Y (vtx Y y k)) := by
  rw [alpha, cochainDiff_apply]
  change (alpha0 Y) ((((ssX Y).chainComplex zR).d 1 0).hom
      (((ssX Y).ιChainComplex (R := zR) (radSimp Y y k)).hom 1)) = _
  rw [alpha0_chain]
  rw [show ((ssX Y).δ 0 (radSimp Y y k)) = ptSimp Y (vtx Y y k) from ssX_δ_zero_radSimp Y y k]
  rw [show ((ssX Y).δ 1 (radSimp Y y k)) = ptSimp Y (origin Y y) from ssX_δ_one_radSimp Y y k]
  rw [alpha0_ι_ptSimp, alpha0_ι_ptSimp, coordA_origin, coordA_vtx]
  rw [posOf_zero, sub_zero]

theorem genEval_beta_arcSimp (y : Y) (k : ℕ) :
    genEval ℤ (ssX Y) (beta Y) (arcSimp Y y k)
      = posOf (coordB Y (vtx Y y (k + 1))) - posOf (coordB Y (vtx Y y k)) := by
  rw [beta, cochainDiff_apply]
  change (beta0 Y) ((((ssX Y).chainComplex zR).d 1 0).hom
      (((ssX Y).ιChainComplex (R := zR) (arcSimp Y y k)).hom 1)) = _
  rw [beta0_chain]
  rw [show ((ssX Y).δ 0 (arcSimp Y y k)) = ptSimp Y (vtx Y y (k+1)) from
    ssX_δ_zero_arcSimp Y y k]
  rw [show ((ssX Y).δ 1 (arcSimp Y y k)) = ptSimp Y (vtx Y y k) from ssX_δ_one_arcSimp Y y k]
  rw [beta0_ι_ptSimp, beta0_ι_ptSimp, coordB_vtx, coordB_vtx]

theorem genEval_cup_secSimp (y : Y) (k : ℕ) :
    genEval ℤ (ssX Y) (cup ℤ (ssX Y) (alpha Y) (beta Y)) (secSimp Y y k)
      = posOf (coordA Y (vtx Y y k))
        * (posOf (coordB Y (vtx Y y (k + 1))) - posOf (coordB Y (vtx Y y k))) := by
  rw [cup_apply, frontFace_secSimp, backFace_secSimp, genEval_alpha_radSimp,
    genEval_beta_arcSimp]

/-! ## The trigonometric values at the six angles -/

theorem cos_ang_zero : Real.cos (ang 0) = 1 := by rw [ang_zero, Real.cos_zero]
theorem sin_ang_zero : Real.sin (ang 0) = 0 := by rw [ang_zero, Real.sin_zero]
theorem cos_ang_one : Real.cos (ang 1) = 1 / 2 := by
  rw [ang_one, Real.cos_pi_div_three]
theorem sin_ang_one : Real.sin (ang 1) = Real.sqrt 3 / 2 := by
  rw [ang_one, Real.sin_pi_div_three]
theorem cos_ang_two : Real.cos (ang 2) = -(1 / 2) := by
  rw [ang_two, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
theorem sin_ang_two : Real.sin (ang 2) = Real.sqrt 3 / 2 := by
  rw [ang_two, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three]
theorem cos_ang_three : Real.cos (ang 3) = -1 := by rw [ang_three, Real.cos_pi]
theorem sin_ang_three : Real.sin (ang 3) = 0 := by rw [ang_three, Real.sin_pi]
theorem cos_ang_four : Real.cos (ang 4) = -(1 / 2) := by
  rw [ang_four, show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi from by ring, Real.cos_add_pi,
    Real.cos_pi_div_three]
theorem sin_ang_four : Real.sin (ang 4) = -(Real.sqrt 3 / 2) := by
  rw [ang_four, show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi from by ring, Real.sin_add_pi,
    Real.sin_pi_div_three]
theorem cos_ang_five : Real.cos (ang 5) = 1 / 2 := by
  rw [ang_five, show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 from by ring,
    Real.cos_two_pi_sub, Real.cos_pi_div_three]
theorem sin_ang_five : Real.sin (ang 5) = -(Real.sqrt 3 / 2) := by
  rw [ang_five, show 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 from by ring,
    Real.sin_two_pi_sub, Real.sin_pi_div_three]
theorem cos_ang_six : Real.cos (ang 6) = 1 := by rw [ang_six, Real.cos_two_pi]
theorem sin_ang_six : Real.sin (ang 6) = 0 := by rw [ang_six, Real.sin_two_pi]

theorem sqrt3_pos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

theorem posOf_cos_ang_zero : posOf (Real.cos (ang 0)) = 1 := by
  rw [cos_ang_zero]; exact posOf_pos (by norm_num)
theorem posOf_sin_ang_zero : posOf (Real.sin (ang 0)) = 0 := by
  rw [sin_ang_zero]; exact posOf_nonpos (by norm_num)
theorem posOf_cos_ang_one : posOf (Real.cos (ang 1)) = 1 := by
  rw [cos_ang_one]; exact posOf_pos (by norm_num)
theorem posOf_sin_ang_one : posOf (Real.sin (ang 1)) = 1 := by
  rw [sin_ang_one]; exact posOf_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
theorem posOf_cos_ang_two : posOf (Real.cos (ang 2)) = 0 := by
  rw [cos_ang_two]; exact posOf_nonpos (by norm_num)
theorem posOf_sin_ang_two : posOf (Real.sin (ang 2)) = 1 := by
  rw [sin_ang_two]; exact posOf_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
theorem posOf_cos_ang_three : posOf (Real.cos (ang 3)) = 0 := by
  rw [cos_ang_three]; exact posOf_nonpos (by norm_num)
theorem posOf_sin_ang_three : posOf (Real.sin (ang 3)) = 0 := by
  rw [sin_ang_three]; exact posOf_nonpos (by norm_num)
theorem posOf_cos_ang_four : posOf (Real.cos (ang 4)) = 0 := by
  rw [cos_ang_four]; exact posOf_nonpos (by norm_num)
theorem posOf_sin_ang_four : posOf (Real.sin (ang 4)) = 0 := by
  rw [sin_ang_four]
  exact posOf_nonpos (by
    have h : (0:ℝ) ≤ Real.sqrt 3 / 2 := div_nonneg (Real.sqrt_nonneg 3) (by norm_num)
    linarith)

theorem posOf_cos_ang_five : posOf (Real.cos (ang 5)) = 1 := by
  rw [cos_ang_five]; exact posOf_pos (by norm_num)

theorem posOf_sin_ang_five : posOf (Real.sin (ang 5)) = 0 := by
  rw [sin_ang_five]
  exact posOf_nonpos (by
    have h : (0:ℝ) ≤ Real.sqrt 3 / 2 := div_nonneg (Real.sqrt_nonneg 3) (by norm_num)
    linarith)

theorem posOf_cos_ang_six : posOf (Real.cos (ang 6)) = 1 := by
  rw [cos_ang_six]; exact posOf_pos (by norm_num)
theorem posOf_sin_ang_six : posOf (Real.sin (ang 6)) = 0 := by
  rw [sin_ang_six]; exact posOf_nonpos (by norm_num)

/-! ## The sum of the six sector evaluations -/

/-- **The total evaluation of the Alexander–Whitney product on the cone is `1`.** -/
theorem cupSum :
    (∑ k ∈ Finset.range 6, (posOf (Real.cos (ang k))
        * (posOf (Real.sin (ang (k + 1))) - posOf (Real.sin (ang k))))) = 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [posOf_cos_ang_zero, posOf_cos_ang_one, posOf_cos_ang_two, posOf_cos_ang_three,
    posOf_cos_ang_four, posOf_cos_ang_five, posOf_cos_ang_six, posOf_sin_ang_zero,
    posOf_sin_ang_one, posOf_sin_ang_two, posOf_sin_ang_three, posOf_sin_ang_four,
    posOf_sin_ang_five, posOf_sin_ang_six]

end

end Work.Whitney.RankTwo
