/-
# The anharmonic action of `SL(2,ℤ)` on the modular lambda function

The group `SL(2, ℤ)/Γ(2) ≅ S₃` acts on `λ = θ₁₀⁴/θ₀₀⁴` through the six *anharmonic*
(cross-ratio) transformations

  `x, 1 - x, x/(x-1), 1/(1-x), (x-1)/x, 1/x`

of `ℂ ∖ {0,1}`: for every `γ ∈ SL(2,ℤ)` there is `i : Fin 6` with
`λ (γ • τ) = anh i (λ τ)`.

This file defines the six maps (`anh`) and their orbit `ANH`, records the closure of `ANH`
under the two generators `σ(x) = 1 - x` (from `S`) and `τ_T(x) = x/(x-1)` (from `T`), the
inverse relations, the non-vanishing of all six maps at points of `ℂ ∖ {0,1}` and their
continuity, and then proves the two main statements: the induction over
`SL(2,ℤ) = ⟨S, T⟩` giving `λ (γ • τ) ∈ ANH (λ τ)`, and the fact that all six elements of the
anharmonic group are realised by explicit words in `S` and `T`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaBasic

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter Topology
open Work.Kernels
open scoped MatrixGroups ModularForm Modular

namespace Work.Rigidity

/-! ## The six anharmonic transformations -/

/-- The six anharmonic (cross-ratio) transformations of `ℂ ∖ {0,1}`, indexed by `Fin 6`. -/
def anh : Fin 6 → ℂ → ℂ
  | 0 => fun w => w
  | 1 => fun w => 1 - w
  | 2 => fun w => w / (w - 1)
  | 3 => fun w => 1 / (1 - w)
  | 4 => fun w => (w - 1) / w
  | 5 => fun w => 1 / w

/-- The orbit of `w` under the anharmonic group. -/
def ANH (w : ℂ) : Set ℂ := Set.range (fun i => anh i w)

/-! ## Closure of the anharmonic orbit under the two generators -/

/-- The anharmonic orbit is closed under `x ↦ 1 - x` (the action of `S`). -/
lemma anh_sigma (i : Fin 6) :
    ∃ j, ∀ w : ℂ, w ≠ 0 → w ≠ 1 → anh j w = 1 - anh i w := by
  fin_cases i
  · refine ⟨1, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨0, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨3, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨2, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨5, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨4, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring

/-- The anharmonic orbit is closed under `x ↦ x/(x-1)` (the action of `T`). -/
lemma anh_tau (i : Fin 6) :
    ∃ j, ∀ w : ℂ, w ≠ 0 → w ≠ 1 → anh j w = anh i w / (anh i w - 1) := by
  fin_cases i
  · refine ⟨2, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨4, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨0, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨5, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨1, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨3, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring

/-- Every element of the anharmonic group is invertible within the orbit: for each `i`
there is `j` with `anh j (anh i w) = w` for `w ∈ ℂ ∖ {0,1}`. -/
lemma anh_left_inv (i : Fin 6) :
    ∃ j, ∀ w : ℂ, w ≠ 0 → w ≠ 1 → anh j (anh i w) = w := by
  fin_cases i
  · refine ⟨0, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨1, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨2, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨4, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨3, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring
  · refine ⟨5, fun w h0 h1 => ?_⟩
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr h1.symm
    simp only [anh]; try field_simp [h0, hw1, h1w]; try ring

/-! ## The anharmonic orbit of a point of `ℂ ∖ {0,1}` -/

/-- No element of the anharmonic orbit of `w ≠ 0, 1` vanishes. -/
lemma anh_ne_zero (i : Fin 6) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) : anh i w ≠ 0 := by
  fin_cases i <;> simp only [anh]
  · exact h0
  · exact fun h => h1 (by linear_combination -h)
  · exact div_ne_zero h0 (sub_ne_zero.mpr h1)
  · exact div_ne_zero one_ne_zero (sub_ne_zero.mpr h1.symm)
  · exact div_ne_zero (sub_ne_zero.mpr h1) h0
  · exact div_ne_zero one_ne_zero h0

/-- No element of the anharmonic orbit of `w ≠ 0, 1` equals `1`. -/
lemma anh_ne_one (i : Fin 6) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) : anh i w ≠ 1 := by
  fin_cases i <;> simp only [anh]
  · exact h1
  · exact fun h => h0 (by linear_combination -h)
  · intro h; rw [div_eq_one_iff_eq (sub_ne_zero.mpr h1)] at h
    exact one_ne_zero (by linear_combination h)
  · intro h; rw [div_eq_one_iff_eq (sub_ne_zero.mpr h1.symm)] at h
    exact h0 (by linear_combination h)
  · intro h; rw [div_eq_one_iff_eq h0] at h
    exact one_ne_zero (by linear_combination -h)
  · intro h; rw [div_eq_one_iff_eq h0] at h
    exact h1 h.symm

/-- Every anharmonic transformation is continuous at every point of `ℂ ∖ {0,1}`. -/
lemma continuousAt_anh (i : Fin 6) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ContinuousAt (anh i) w := by
  fin_cases i <;> simp only [anh]
  · exact continuousAt_id
  · exact continuousAt_const.sub continuousAt_id
  · exact continuousAt_id.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr h1)
  · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.mpr h1.symm)
  · exact (continuousAt_id.sub continuousAt_const).div continuousAt_id h0
  · exact continuousAt_const.div continuousAt_id h0

/-! ## The `S`- and `T`-transformation laws of `λ` in anharmonic form -/

/-- `λ(-1/τ) = 1 - λ(τ)`. -/
lemma lambdaFun_S_eq (τ : ℍ) :
    lambdaFun (ModularGroup.S • τ) = 1 - lambdaFun τ := by
  rw [Work.Kernels.LogLambda.lambdaFun_S]
  have h := lambdaFun_add_lambdaSFun τ
  linear_combination h

/-- `λ(τ+1) = λ(τ)/(λ(τ)-1)`. -/
lemma lambdaFun_T_eq (τ : ℍ) :
    lambdaFun (ModularGroup.T • τ) = lambdaFun τ / (lambdaFun τ - 1) := by
  rw [Work.Kernels.LogLambda.lambdaFun_T]
  have hLS : lambdaSFun τ = 1 - lambdaFun τ := by
    have := lambdaFun_add_lambdaSFun τ
    linear_combination this
  rw [hLS, div_eq_mul_inv, div_eq_mul_inv,
    show (1 : ℂ) - lambdaFun τ = -(lambdaFun τ - 1) by ring, inv_neg]
  ring

/-- `λ(T⁻¹ • τ) = λ(τ)/(λ(τ)-1)`. -/
lemma lambdaFun_T_inv_eq (τ : ℍ) :
    lambdaFun (ModularGroup.T⁻¹ • τ) = lambdaFun τ / (lambdaFun τ - 1) := by
  have hT : (ModularGroup.T⁻¹ : SL(2, ℤ)) = ModularGroup.T * (ModularGroup.T ^ 2)⁻¹ := by
    group
  have hT2 : lambdaFun ((ModularGroup.T ^ 2)⁻¹ • τ) = lambdaFun τ := by
    have h := lambdaFun_T2 ((ModularGroup.T ^ 2)⁻¹ • τ)
    rw [smul_inv_smul] at h
    exact h.symm
  rw [hT, mul_smul, lambdaFun_T_eq, hT2]

/-! ## The induction over `SL(2,ℤ) = ⟨S, T⟩` -/

/-- **The anharmonic transformation law for a general element of `SL(2,ℤ)`**:
`λ (γ • τ)` lies in the anharmonic orbit of `λ τ`. -/
theorem lambdaFun_smul_mem_ANH (γ : SL(2, ℤ)) (τ : ℍ) :
    lambdaFun (γ • τ) ∈ ANH (lambdaFun τ) := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  have key : ∀ x ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)),
      ∀ τ : ℍ, lambdaFun (x • τ) ∈ ANH (lambdaFun τ) := by
    apply Subgroup.closure_induction_left
    · intro τ
      exact ⟨0, by simp [anh]⟩
    · intro x hx y hy ih τ
      rcases hx with rfl | rfl
      · -- `x = S`
        obtain ⟨i, hi⟩ := ih τ
        obtain ⟨j, hj⟩ := anh_sigma i
        refine ⟨j, ?_⟩
        rw [mul_smul, lambdaFun_S_eq, ← hi]
        exact hj (lambdaFun τ) (lambdaFun_ne_zero τ) (lambdaFun_ne_one τ)
      · -- `x = T`
        obtain ⟨i, hi⟩ := ih τ
        obtain ⟨j, hj⟩ := anh_tau i
        refine ⟨j, ?_⟩
        rw [mul_smul, lambdaFun_T_eq, ← hi]
        exact hj (lambdaFun τ) (lambdaFun_ne_zero τ) (lambdaFun_ne_one τ)
    · intro x hx y hy ih τ
      rcases hx with rfl | rfl
      · -- `x = S`, `S⁻¹ = S`
        obtain ⟨i, hi⟩ := ih τ
        obtain ⟨j, hj⟩ := anh_sigma i
        refine ⟨j, ?_⟩
        rw [mul_smul, ModularGroup.S_inv, ModularGroup.SL_neg_smul, lambdaFun_S_eq, ← hi]
        exact hj (lambdaFun τ) (lambdaFun_ne_zero τ) (lambdaFun_ne_one τ)
      · -- `x = T`
        obtain ⟨i, hi⟩ := ih τ
        obtain ⟨j, hj⟩ := anh_tau i
        refine ⟨j, ?_⟩
        rw [mul_smul, lambdaFun_T_inv_eq, ← hi]
        exact hj (lambdaFun τ) (lambdaFun_ne_zero τ) (lambdaFun_ne_one τ)
  exact key γ hmem τ

/-! ## Realisation of the six anharmonic maps by words in `S` and `T` -/

private lemma key3 (a : ℂ) (h : a - 1 ≠ 0) : 1 - a / (a - 1) = 1 / (1 - a) := by
  have h' : (1 : ℂ) - a ≠ 0 := by
    intro hh; exact h (by linear_combination -hh)
  field_simp
  ring

private lemma key4 (a : ℂ) (h : a ≠ 0) : (1 - a) / ((1 - a) - 1) = (a - 1) / a := by
  have h' : (1 : ℂ) - a - 1 ≠ 0 := by
    intro hh; exact h (by linear_combination -hh)
  field_simp
  ring

private lemma key5 (a : ℂ) (h : a ≠ 0) : 1 - (1 - a) / ((1 - a) - 1) = 1 / a := by
  have h' : (1 : ℂ) - a - 1 ≠ 0 := by
    intro hh; exact h (by linear_combination -hh)
  field_simp
  ring

/-- Every element of the anharmonic group is realised by an explicit element of `SL(2,ℤ)`. -/
theorem exists_lambdaFun_smul_eq_anh (i : Fin 6) :
    ∃ γ : SL(2, ℤ), ∀ τ : ℍ, lambdaFun (γ • τ) = anh i (lambdaFun τ) := by
  fin_cases i
  · exact ⟨1, fun τ => by simp [anh]⟩
  · refine ⟨ModularGroup.S, fun τ => ?_⟩
    rw [lambdaFun_S_eq]; simp [anh]
  · refine ⟨ModularGroup.T, fun τ => ?_⟩
    rw [lambdaFun_T_eq]; simp [anh]
  · refine ⟨ModularGroup.S * ModularGroup.T, fun τ => ?_⟩
    rw [mul_smul, lambdaFun_S_eq, lambdaFun_T_eq]
    simp only [anh]
    exact key3 (lambdaFun τ) (sub_ne_zero.mpr (lambdaFun_ne_one τ))
  · refine ⟨ModularGroup.T * ModularGroup.S, fun τ => ?_⟩
    rw [mul_smul, lambdaFun_T_eq, lambdaFun_S_eq]
    simp only [anh]
    exact key4 (lambdaFun τ) (lambdaFun_ne_zero τ)
  · refine ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S, fun τ => ?_⟩
    rw [mul_smul, mul_smul, lambdaFun_S_eq, lambdaFun_T_eq, lambdaFun_S_eq]
    simp only [anh]
    exact key5 (lambdaFun τ) (lambdaFun_ne_zero τ)

end Work.Rigidity
