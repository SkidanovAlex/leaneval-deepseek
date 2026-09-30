import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.kleinOfHyp_hypOfKlein
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.HypModel.mobius_mul
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-! ### The tangent inclusion `E4 ↪ V5` -/

/-- The inclusion of `E4` into the ambient Lorentz space `V5` as the first four coordinates
(last coordinate `0`). -/
def inl (v : E4) : V5 := ![v 0, v 1, v 2, v 3, 0]

@[simp] theorem inl_apply_zero (v : E4) : inl v 0 = v 0 := rfl
@[simp] theorem inl_apply_one (v : E4) : inl v 1 = v 1 := rfl
@[simp] theorem inl_apply_two (v : E4) : inl v 2 = v 2 := rfl
@[simp] theorem inl_apply_three (v : E4) : inl v 3 = v 3 := rfl
@[simp] theorem inl_apply_four (v : E4) : inl v 4 = 0 := rfl

/-- `inl` as a continuous linear map. -/
def inlCLM : E4 →L[ℝ] V5 :=
  LinearMap.toContinuousLinearMap
    { toFun := inl
      map_add' := by intro v w; ext i; fin_cases i <;> simp [inl]
      map_smul' := by intro c v; ext i; fin_cases i <;> simp [inl] }

@[simp] theorem inlCLM_apply (v : E4) : inlCLM v = inl v := rfl

/-- `ray z = ray 0 + inl z`. -/
theorem ray_eq_const_add_inl (z : E4) : ray z = ray 0 + inl z := by
  ext i; fin_cases i <;> simp [ray, inl]

/-- `lorentz (ray y) (inl w) = ⟪y,w⟫`. -/
theorem lorentz_ray_inl (y w : E4) : lorentz (ray y) (inl w) = ⟪y, w⟫_ℝ := by
  rw [lorentz_eq_dotProduct_proj4, inner_eq_dotProduct]
  simp [proj4, ray, inl, dotProduct, Fin.sum_univ_four]

/-- `lorentz (inl v) (ray y) = ⟪v,y⟫`. -/
theorem lorentz_inl_ray (v y : E4) : lorentz (inl v) (ray y) = ⟪v, y⟫_ℝ := by
  rw [lorentz_comm, lorentz_ray_inl, real_inner_comm]

/-- `lorentz (inl v) (inl w) = ⟪v,w⟫`. -/
theorem lorentz_inl_inl (v w : E4) : lorentz (inl v) (inl w) = ⟪v, w⟫_ℝ := by
  rw [lorentz_eq_dotProduct_proj4, inner_eq_dotProduct]
  simp [proj4, inl, dotProduct, Fin.sum_univ_four]

/-! ### The explicit derivative of the Klein lift -/

/-- The normalising factor `s(y) = (√(1-‖y‖²))⁻¹` of the Klein lift. -/
def kleinS (y : E4) : ℝ := (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹

/-- The explicit derivative of the Klein lift `hypOfKlein`:
`v ↦ s(y)³⟪y,v⟫ • ray y + s(y) • (v,0)`, `s(y) = (√(1-‖y‖²))⁻¹`. -/
def dHypOfKlein (y : E4) : E4 →L[ℝ] V5 :=
  (kleinS y) ^ 3 • (innerSL ℝ y).smulRight (ray y) + (kleinS y) • inlCLM

theorem dHypOfKlein_apply (y v : E4) :
    dHypOfKlein y v = (kleinS y ^ 3 * ⟪y, v⟫_ℝ) • ray y + (kleinS y) • inl v := by
  simp only [dHypOfKlein, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, inlCLM_apply, innerSL_apply_apply, smul_smul]


/-- `(c • f).smulRight g = c • f.smulRight g`. -/
theorem smul_smulRight (c : ℝ) (f : E4 →L[ℝ] ℝ) (g : V5) :
    (c • f).smulRight g = c • f.smulRight g := by
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
    smul_eq_mul]

/-- The Klein lift is differentiable at every point of the open unit ball, with derivative
`dHypOfKlein y`. -/
theorem hasFDerivAt_hypOfKlein {y : E4} (hy : y ∈ ball) :
    HasFDerivAt hypOfKlein (dHypOfKlein y) y := by
  have hpos : 0 < 1 - ‖y‖ ^ 2 := one_sub_norm_sq_pos_of_mem_ball hy
  have hne : 1 - ‖y‖ ^ 2 ≠ 0 := ne_of_gt hpos
  have hsqrtne : Real.sqrt (1 - ‖y‖ ^ 2) ≠ 0 := (Real.sqrt_ne_zero').mpr hpos
  have hsq : Real.sqrt (1 - ‖y‖ ^ 2) ^ 2 = 1 - ‖y‖ ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  have h1 : HasFDerivAt (fun z : E4 => ‖z‖ ^ 2) (2 • innerSL ℝ y) y := by
    simpa using (hasFDerivAt_id (E := E4) y).norm_sq
  have hG : HasFDerivAt (fun z : E4 => 1 - ‖z‖ ^ 2) ((-2 : ℝ) • innerSL ℝ y) y := by
    have h := h1.const_sub 1
    have h2 : -((2 : ℕ) • innerSL ℝ y) = (-2 : ℝ) • innerSL ℝ y := by
      have hcast : ((2 : ℕ) • innerSL ℝ y) = (2 : ℝ) • innerSL ℝ y :=
        (Nat.cast_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ y)).symm
      rw [hcast, neg_smul]
    rwa [h2] at h
  have hscoef : (-((Real.sqrt (1 - ‖y‖ ^ 2)) ^ 2)⁻¹) •
        ((1 / (2 * Real.sqrt (1 - ‖y‖ ^ 2))) • ((-2 : ℝ) • innerSL ℝ y))
      = kleinS y ^ 3 • innerSL ℝ y := by
    rw [kleinS, smul_smul, smul_smul]
    congr 1
    field_simp [hsqrtne, hne]
  have hs : HasFDerivAt (fun z : E4 => (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹)
      (kleinS y ^ 3 • innerSL ℝ y) y := by
    have hcc := (hasDerivAt_inv hsqrtne).comp_hasFDerivAt y (hG.sqrt hne)
    rwa [hscoef] at hcc
  have hray : HasFDerivAt (fun z : E4 => ray z) inlCLM y := by
    have h : (fun z : E4 => ray z) = (fun _ : E4 => ray 0) + inlCLM := by
      funext z; rw [Pi.add_apply, inlCLM_apply]; exact ray_eq_const_add_inl z
    rw [h]
    simpa using (hasFDerivAt_const (ray 0) y).add
      (ContinuousLinearMap.hasFDerivAt inlCLM (x := y))
  have hprod := hs.smul hray
  have hder : (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • inlCLM +
        (kleinS y ^ 3 • innerSL ℝ y).smulRight (ray y) = dHypOfKlein y := by
    rw [dHypOfKlein, smul_smulRight, add_comm]
    rfl
  rw [hder] at hprod
  exact hprod

/-- `dHypOfKlein y` is tangent to the hyperboloid at `hypOfKlein y`. -/
theorem tangent_hypOfKlein {y : E4} (hy : y ∈ ball) (v : E4) :
    lorentz (hypOfKlein y) (dHypOfKlein y v) = 0 := by
  have hpos : 0 < 1 - ‖y‖ ^ 2 := one_sub_norm_sq_pos_of_mem_ball hy
  have hs2 : kleinS y ^ 2 = (1 - ‖y‖ ^ 2)⁻¹ := by
    rw [kleinS, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
  have hc4 : kleinS y ^ 4 = ((1 - ‖y‖ ^ 2)⁻¹) ^ 2 := by rw [← hs2]; ring
  simp only [show hypOfKlein y = kleinS y • ray y from rfl, dHypOfKlein_apply,
    lorentz_add_right, lorentz_smul_left, lorentz_smul_right, lorentz_ray_self,
    lorentz_ray_inl]
  ring_nf
  rw [hc4, hs2]
  field_simp
  ring

/-- The Lorentz pairing of the derivatives of `hypOfKlein` is the Klein metric. -/
theorem lorentz_dHypOfKlein {y : E4} (hy : y ∈ ball) (v w : E4) :
    lorentz (dHypOfKlein y v) (dHypOfKlein y w) = kleinMetric y v w := by
  have hpos : 0 < 1 - ‖y‖ ^ 2 := one_sub_norm_sq_pos_of_mem_ball hy
  have hg : (1 - ‖y‖ ^ 2) ≠ 0 := ne_of_gt hpos
  have hs2 : kleinS y ^ 2 = (1 - ‖y‖ ^ 2)⁻¹ := by
    rw [kleinS, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
  have hc4 : kleinS y ^ 4 = ((1 - ‖y‖ ^ 2)⁻¹) ^ 2 := by rw [← hs2]; ring
  have hc6 : kleinS y ^ 6 = ((1 - ‖y‖ ^ 2)⁻¹) ^ 3 := by rw [← hs2]; ring
  simp only [dHypOfKlein_apply, lorentz_add_left, lorentz_add_right, lorentz_smul_left,
    lorentz_smul_right, lorentz_ray_self, lorentz_ray_inl, lorentz_inl_ray, lorentz_inl_inl,
    real_inner_comm v y, kleinMetric]
  ring_nf
  rw [hc6, hc4, hs2]
  field_simp
  ring

@[simp] private theorem dUhsOfHyp_apply_zero (P v : V5) :
    dUhsOfHyp P v 0 = v 0 / (P 4 - P 3) - P 0 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

@[simp] private theorem dUhsOfHyp_apply_one (P v : V5) :
    dUhsOfHyp P v 1 = v 1 / (P 4 - P 3) - P 1 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

@[simp] private theorem dUhsOfHyp_apply_two (P v : V5) :
    dUhsOfHyp P v 2 = v 2 / (P 4 - P 3) - P 2 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

@[simp] private theorem dUhsOfHyp_apply_three (P v : V5) :
    dUhsOfHyp P v 3 = v 3 / (P 4 - P 3) ^ 2 - v 4 / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]
  ring

private theorem dHypOfUHS_comp_dUhsOfHyp {P : V5} (hP : P ∈ upperSheet) {v : V5}
    (hv : lorentz P v = 0) : dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) = v := by
  have hδ : P 4 - P 3 ≠ 0 := ne_of_gt (upperSheet_four_sub_three_pos hP)
  have hsq : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 - P 4 ^ 2 = -1 := by
    have h := hP.1
    simp only [lorentz] at h
    nlinarith
  have hN : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + 1 = (P 4 - P 3) * (P 4 + P 3) := by nlinarith [hsq]
  have hv'' : P 0 * v 0 + P 1 * v 1 + P 2 * v 2 = P 4 * v 4 - P 3 * v 3 := by
    have h := hv
    simp only [lorentz] at h
    nlinarith
  ext i
  fin_cases i
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 0 = v 0
    simp only [dHypOfUHS_apply_zero, uhsOfHyp_apply_zero, uhsOfHyp_apply_three,
      dUhsOfHyp_apply_zero, dUhsOfHyp_apply_three]
    field_simp
    ring
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 1 = v 1
    simp only [dHypOfUHS_apply_one, uhsOfHyp_apply_one, uhsOfHyp_apply_three,
      dUhsOfHyp_apply_one, dUhsOfHyp_apply_three]
    field_simp
    ring
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 2 = v 2
    simp only [dHypOfUHS_apply_two, uhsOfHyp_apply_two, uhsOfHyp_apply_three,
      dUhsOfHyp_apply_two, dUhsOfHyp_apply_three]
    field_simp
    ring
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 3 = v 3
    simp only [dHypOfUHS_apply_three, uhsOfHyp_apply_three, dUhsOfHyp_apply_zero,
      dUhsOfHyp_apply_one, dUhsOfHyp_apply_two, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_zero, uhsOfHyp_apply_one, uhsOfHyp_apply_two,
      inner_E4_eq_coords, norm_sq_E4_eq_coords]
    field_simp
    ring_nf
    linear_combination (2 * (P 4 - P 3)) * hv'' + (v 3 - v 4) * hN
  · show dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) 4 = v 4
    simp only [dHypOfUHS_apply_four, uhsOfHyp_apply_three, dUhsOfHyp_apply_zero,
      dUhsOfHyp_apply_one, dUhsOfHyp_apply_two, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_zero, uhsOfHyp_apply_one, uhsOfHyp_apply_two,
      inner_E4_eq_coords, norm_sq_E4_eq_coords]
    field_simp
    ring_nf
    linear_combination (2 * (P 4 - P 3)) * hv'' + (v 3 - v 4) * hN

/-! ### 4. The metric of the upper half space in terms of the Lorentz form -/

/-- The upper half space metric of a chart point, applied to the images under `d(uhsOfHyp P)` of
two tangent vectors at `P`, is their Lorentz pairing: `d(uhsOfHyp P)` is the inverse of
`d(hypOfUHS)`, which is a Lorentz isometry. -/
private theorem uhsMetric_dUhsOfHyp {P : V5} (hP : P ∈ upperSheet) {X Y : V5}
    (hX : lorentz P X = 0) (hY : lorentz P Y = 0) :
    uhsMetric (uhsOfHyp P) (dUhsOfHyp P X) (dUhsOfHyp P Y) = lorentz X Y := by
  have hq3 : (uhsOfHyp P) 3 ≠ 0 := ne_of_gt (uhsOfHyp_three_pos hP)
  rw [← lorentz_dHypOfUHS hq3 (dUhsOfHyp P X) (dUhsOfHyp P Y),
    dHypOfUHS_comp_dUhsOfHyp hP hX, dHypOfUHS_comp_dUhsOfHyp hP hY]

/-- The linear map `x ↦ A *ᵥ x` as a continuous linear map. -/
private def mulVecCLM (A : Matrix (Fin 5) (Fin 5) ℝ) : V5 →L[ℝ] V5 :=
  (Matrix.mulVecLin A).toContinuousLinearMap

private theorem mulVecCLM_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (x : V5) :
    mulVecCLM A x = A *ᵥ x := by
  simp [mulVecCLM]

/-- **The derivative of the Klein action.**  The map `mobiusKlein M` is the composite of the Klein
lift `hypOfKlein`, the linear action `M ·`, and the upper half space coordinate map `uhsOfHyp`; each
factor is differentiable at the relevant point, so the chain rule gives the stated derivative. -/
theorem hasFDerivAt_mobiusKlein {M : Matrix (Fin 5) (Fin 5) ℝ} (hM : IsLorentzMat M) {y : E4}
    (hy : y ∈ ball) :
    HasFDerivAt (mobiusKlein M)
      (dUhsOfHyp (M *ᵥ hypOfKlein y) ∘L mulVecCLM M ∘L dHypOfKlein y) y := by
  have hP : hypOfKlein y ∈ upperSheet := hypOfKlein_mem_upperSheet hy
  have hQ : M *ᵥ hypOfKlein y ∈ upperSheet := isLorentzMat_mem_upperSheet hM hP
  have hδ : (M *ᵥ hypOfKlein y) 4 - (M *ᵥ hypOfKlein y) 3 ≠ 0 :=
    ne_of_gt (upperSheet_four_sub_three_pos hQ)
  have h1 : HasFDerivAt hypOfKlein (dHypOfKlein y) y := hasFDerivAt_hypOfKlein hy
  have h2 : HasFDerivAt (fun P : V5 => M *ᵥ P) (mulVecCLM M) (hypOfKlein y) := by
    have h := ContinuousLinearMap.hasFDerivAt (mulVecCLM M) (x := hypOfKlein y)
    rw [show (⇑(mulVecCLM M)) = (fun P : V5 => M *ᵥ P) from funext (mulVecCLM_apply M)] at h
    exact h
  have h3 : HasFDerivAt uhsOfHyp (dUhsOfHyp (M *ᵥ hypOfKlein y)) (M *ᵥ hypOfKlein y) :=
    hasFDerivAt_uhsOfHyp hδ
  have hfun : mobiusKlein M = fun x : E4 => uhsOfHyp (M *ᵥ hypOfKlein x) := rfl
  rw [hfun]
  exact (h3.comp (hypOfKlein y) h2).comp y h1

/-- **The Klein action is an isometry.**  For a Lorentz matrix `M` preserving the upper sheet and a
point `y` of the Klein ball, the upper half space metric at the image of `y` applied to the
differential of `mobiusKlein M` is the Klein metric at `y`. -/
theorem mobiusKlein_isometry {M : Matrix (Fin 5) (Fin 5) ℝ} (hM : IsLorentzMat M) {y : E4}
    (hy : y ∈ ball) (v w : E4) :
    uhsMetric (mobiusKlein M y) (fderiv ℝ (mobiusKlein M) y v) (fderiv ℝ (mobiusKlein M) y w) =
      kleinMetric y v w := by
  have hP : hypOfKlein y ∈ upperSheet := hypOfKlein_mem_upperSheet hy
  have hQ : M *ᵥ hypOfKlein y ∈ upperSheet := isLorentzMat_mem_upperSheet hM hP
  have hX : lorentz (M *ᵥ hypOfKlein y) (M *ᵥ dHypOfKlein y v) = 0 := by
    rw [lorentz_mulVec_of_isLorentzMat hM, tangent_hypOfKlein hy v]
  have hY : lorentz (M *ᵥ hypOfKlein y) (M *ᵥ dHypOfKlein y w) = 0 := by
    rw [lorentz_mulVec_of_isLorentzMat hM, tangent_hypOfKlein hy w]
  have hfd : fderiv ℝ (mobiusKlein M) y
      = dUhsOfHyp (M *ᵥ hypOfKlein y) ∘L mulVecCLM M ∘L dHypOfKlein y := by
    rw [show mobiusKlein M = (fun x : E4 => uhsOfHyp (M *ᵥ hypOfKlein x)) from rfl]
    exact (hasFDerivAt_mobiusKlein hM hy).fderiv
  rw [hfd]
  simp only [mobiusKlein, ContinuousLinearMap.comp_apply, mulVecCLM_apply]
  rw [uhsMetric_dUhsOfHyp hQ hX hY, lorentz_mulVec_of_isLorentzMat hM,
    lorentz_dHypOfKlein hy v w]

end Work.HypModel
