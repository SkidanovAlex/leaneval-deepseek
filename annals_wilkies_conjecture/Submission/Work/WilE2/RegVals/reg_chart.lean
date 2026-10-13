import Mathlib
import Submission.Work.WilE2.RegVals.Basic
import Submission.Work.WilE2.RegVals.reg_aux

open MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.WilE2.RegVals

/-! ## 2. The straightening chart -/

section Chart

variable {k : ℕ}

/-- Forgetting the `j`-th coordinate. -/
def crj (j : Fin (k+2)) (z : Fin (k+2) → ℝ) : Fin (k+1) → ℝ := fun l => z (j.succAbove l)

@[simp] theorem crj_apply (j : Fin (k+2)) (z : Fin (k+2) → ℝ) (l : Fin (k+1)) :
    crj j z l = z (j.succAbove l) := rfl

/-- The linear map underlying `crj`. -/
def kdrj (j : Fin (k+2)) : (Fin (k+2) → ℝ) →L[ℝ] (Fin (k+1) → ℝ) :=
  ContinuousLinearMap.pi (fun l => ContinuousLinearMap.proj (j.succAbove l))

theorem kdrj_apply (j : Fin (k+2)) (v : Fin (k+2) → ℝ) : kdrj j v = crj j v := by
  funext l
  rw [kdrj, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, crj_apply]

/-- `Xi g i j z` replaces the `j`-th coordinate of `z` by `g z i`. -/
def Xi (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (z : Fin (k+2) → ℝ) : Fin (k+2) → ℝ :=
  z + (g z i - z j) • (Pi.single j (1:ℝ) : Fin (k+2) → ℝ)

theorem Xi_apply (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (z : Fin (k+2) → ℝ) (m : Fin (k+2)) :
    Xi g i j z m = if m = j then g z i else z m := by
  by_cases hm : m = j
  · subst hm; simp [Xi, Pi.single_eq_same]
  · rw [Xi, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hm, smul_zero, add_zero]
    exact (if_neg hm).symm

theorem crj_Xi (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (z : Fin (k+2) → ℝ) : crj j (Xi g i j z) = crj j z := by
  funext l
  rw [crj_apply, crj_apply, Xi_apply]
  exact if_neg (Fin.succAbove_ne j l)

/-- The derivative of `Xi` at `x₀`. -/
def XiD (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (x₀ : Fin (k+2) → ℝ) : (Fin (k+2) → ℝ) →L[ℝ] (Fin (k+2) → ℝ) :=
  ContinuousLinearMap.pi (fun m =>
    if m = j then fderiv ℝ (fun z => g z i) x₀ else ContinuousLinearMap.proj m)

theorem XiD_apply (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (x₀ v : Fin (k+2) → ℝ) (m : Fin (k+2)) :
    XiD g i j x₀ v m = if m = j then (fderiv ℝ (fun z => g z i) x₀) v else v m := by
  rw [XiD, ContinuousLinearMap.pi_apply]
  by_cases hm : m = j
  · subst hm; simp [ContinuousLinearMap.proj_apply]
  · rw [if_neg hm, if_neg hm, ContinuousLinearMap.proj_apply]

theorem hasFDerivAt_Xi (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (x₀ : Fin (k+2) → ℝ) (hg : ContDiff ℝ 2 g) :
    HasFDerivAt (Xi g i j) (XiD g i j x₀) x₀ := by
  rw [show Xi g i j = fun z m => if m = j then g z i else z m from
    funext fun z => funext fun m => Xi_apply g i j z m]
  refine (hasFDerivAt_pi).mpr fun m => ?_
  by_cases hm : m = j
  · have hfun : (fun z : Fin (k+2) → ℝ => if m = j then g z i else z m) = fun z => g z i := by
      funext z; rw [if_pos hm]
    rw [hfun, if_pos hm]
    have hdc : fderiv ℝ (fun z => g z i) x₀
        = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i).comp
            (fderiv ℝ g x₀) :=
      fderiv_coord g x₀ (hg.contDiffAt.differentiableAt (by norm_num)) i
    rw [hdc]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i).hasFDerivAt.comp x₀
      ((hg.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt)
  · have hfun : (fun z : Fin (k+2) → ℝ => if m = j then g z i else z m) = fun z => z m := by
      funext z; rw [if_neg hm]
    rw [hfun, if_neg hm]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) m).hasFDerivAt

theorem contDiffAt_Xi (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (x₀ : Fin (k+2) → ℝ) (hg : ContDiff ℝ 2 g) : ContDiffAt ℝ 2 (Xi g i j) x₀ := by
  have h1 : ContDiff ℝ 2 (fun z : Fin (k+2) → ℝ => z) := contDiff_id
  have h2 : ContDiff ℝ 2 (fun z : Fin (k+2) → ℝ => g z i) := by
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i).contDiff).comp hg
    rwa [show (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i) ∘ g
      = fun z => g z i from rfl] at h
  have h3 : ContDiff ℝ 2 (fun z : Fin (k+2) → ℝ => z j) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j).contDiff
  have h4 : ContDiff ℝ 2 (fun z : Fin (k+2) → ℝ => g z i - z j) := h2.sub h3
  have h5 : ContDiff ℝ 2
      (fun z : Fin (k+2) → ℝ => (g z i - z j) • (Pi.single j (1:ℝ) : Fin (k+2) → ℝ)) :=
    h4.smul contDiff_const
  have h6 := h1.add h5
  rw [show (fun z : Fin (k+2) → ℝ => z + (g z i - z j) • (Pi.single j (1:ℝ) : Fin (k+2) → ℝ))
      = Xi g i j from rfl] at h6
  exact h6.contDiffAt

/-- `XiD` is injective when `∂_j g_i(x₀) ≠ 0`. -/
theorem XiD_eq_zero (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (x₀ : Fin (k+2) → ℝ)
    (hj : (fderiv ℝ (fun z => g z i) x₀) (Pi.single j (1:ℝ)) ≠ 0)
    (v : Fin (k+2) → ℝ) (h : XiD g i j x₀ v = 0) : v = 0 := by
  have hoff : ∀ m, m ≠ j → v m = 0 := by
    intro m hm
    have hh := congrFun h m
    simp only [XiD_apply, if_neg hm, Pi.zero_apply] at hh
    exact hh
  have hv : v = (v j) • (Pi.single j (1:ℝ) : Fin (k+2) → ℝ) := by
    funext m
    by_cases hm : m = j
    · subst hm; rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hm, smul_zero, hoff m hm]
  have hvj : v j = 0 := by
    have hh := congrFun h j
    simp only [XiD_apply, if_pos rfl, Pi.zero_apply] at hh
    rw [hv, map_smul, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_right hj
  rw [hv, hvj, zero_smul]

/-- `XiD` is surjective when `∂_j g_i(x₀) ≠ 0`. -/
theorem XiD_surjective (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ)) (i : Fin (k+1)) (j : Fin (k+2))
    (x₀ : Fin (k+2) → ℝ)
    (hj : (fderiv ℝ (fun z => g z i) x₀) (Pi.single j (1:ℝ)) ≠ 0) :
    Function.Surjective (XiD g i j x₀) := by
  intro w
  set s : Fin (k+2) → ℝ := (Pi.single j (1:ℝ) : Fin (k+2) → ℝ) with hs
  set b : (Fin (k+2) → ℝ) →L[ℝ] ℝ := fderiv ℝ (fun z => g z i) x₀ with hb
  have hbs : b s ≠ 0 := by rw [hb, hs]; exact hj
  set A : Fin (k+2) → ℝ := w - (w j) • s with hA
  set c : ℝ := (b s)⁻¹ * (w j - b A) with hc
  refine ⟨A + c • s, ?_⟩
  have hAm : ∀ m, A m = if m = j then 0 else w m := by
    intro m
    rw [hA]
    by_cases hm : m = j
    · subst hm
      rw [Pi.sub_apply, Pi.smul_apply, hs, Pi.single_eq_same, smul_eq_mul, mul_one, sub_self,
        if_pos rfl]
    · rw [Pi.sub_apply, Pi.smul_apply, hs, Pi.single_eq_of_ne hm, smul_zero, sub_zero, if_neg hm]
  have hcβ : c * (b s) = w j - b A := by
    rw [hc, mul_assoc, mul_comm (w j - b A) (b s), ← mul_assoc, inv_mul_cancel₀ hbs, one_mul]
  funext m
  by_cases hm : m = j
  · subst hm
    rw [XiD_apply, if_pos rfl, ← hb, map_add, map_smul, smul_eq_mul, hcβ]
    abel
  · rw [XiD_apply, if_neg hm, Pi.add_apply, Pi.smul_apply, hAm m, if_neg hm, hs,
      Pi.single_eq_of_ne hm, smul_zero, add_zero]

end Chart


end Work.WilE2.RegVals
