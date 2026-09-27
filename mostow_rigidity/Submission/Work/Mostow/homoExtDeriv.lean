import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.homoExtAux

/-!
# Differentiability of `phiFun` and of `homoExt`

`phiFun g ξ = (dfun g ξ)⁻¹ • topVec g ξ` is the explicit quotient formula for the boundary
action, and `homoExt g x = ‖x‖ • phiFun g (‖x‖⁻¹ • x)` is its degree-one homogeneous extension.

This file records the (ordinary) differentiability of both maps: `phiFun g` is differentiable at
every `ξ` with `dfun g ξ ≠ 0` (in particular at every point of the unit sphere, where `dfun g` is
positive), and `homoExt g` is differentiable at every `x ≠ 0`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- `ξ ↦ (ξ, 0)` as a linear map `E n → ℝ^{Fin n ⊕ Fin 1}`. -/
def hvecLin (n : ℕ) : E n →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun ξ := Sum.elim (fun i => ξ i) (fun _ => 0)
  map_add' x y := by funext z; rcases z with i | j <;> simp [Pi.add_apply]
  map_smul' c x := by funext z; rcases z with i | j <;> simp [Pi.smul_apply]

/-- The constant vector `(0,1) = hvec 0`. -/
def evec (n : ℕ) : Fin n ⊕ Fin 1 → ℝ := Pi.single (Sum.inr 0) 1

/-- The projection `w ↦ (w (inl i))ᵢ : ℝ^{Fin n ⊕ Fin 1} → ℝ^{Fin n}`. -/
def sqProj (n : ℕ) : (Fin n ⊕ Fin 1 → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj (Sum.inl i))

/-- `hvec ξ = (ξ,0) + (0,1)`. -/
lemma hvec_eq (n : ℕ) (ξ : E n) : hvec ξ = hvecLin n ξ + evec n := by
  funext z; rcases z with i | j
  · simp [hvec, hvecLin, evec]
  · fin_cases j; simp [hvec, hvecLin, evec]

lemma hasFDerivAt_hvec (n : ℕ) (ξ : E n) :
    HasFDerivAt (fun ξ : E n => hvec ξ) (LinearMap.toContinuousLinearMap (hvecLin n)) ξ := by
  have h := (LinearMap.toContinuousLinearMap (hvecLin n)).hasFDerivAt (x := ξ)
  refine (h.add_const (evec n)).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  exact hvec_eq n y

/-- `ξ ↦ wvec_visualDefs g ξ = sMat g *ᵥ (ξ,1)` as a linear map. -/
def Wlin (n : ℕ) (g : PO n 1) : E n →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) :=
  (Matrix.mulVecLin (sMat g)).comp (hvecLin n)

lemma hasFDerivAt_wvec (n : ℕ) (g : PO n 1) (ξ : E n) :
    HasFDerivAt (fun ξ : E n => wvec_visualDefs g ξ) (LinearMap.toContinuousLinearMap (Wlin n g)) ξ := by
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (sMat g))).hasFDerivAt
    (x := hvec ξ)
  have h2 := HasFDerivAt.comp (x := ξ) h1 (hasFDerivAt_hvec n ξ)
  have h3 : (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (sMat g))).comp
      (LinearMap.toContinuousLinearMap (hvecLin n))
      = LinearMap.toContinuousLinearMap (Wlin n g) := by
    ext v; rfl
  rw [h3] at h2
  refine h2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  rfl

lemma hasFDerivAt_dfun (n : ℕ) (g : PO n 1) (ξ : E n) :
    HasFDerivAt (fun ξ : E n => dfun g ξ)
      ((ContinuousLinearMap.proj (Sum.inr 0)).comp
        (LinearMap.toContinuousLinearMap (Wlin n g))) ξ := by
  have h1 := (ContinuousLinearMap.proj (Sum.inr 0) :
    (Fin n ⊕ Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := wvec_visualDefs g ξ)
  have h2 := HasFDerivAt.comp (x := ξ) h1 (hasFDerivAt_wvec n g ξ)
  refine h2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y; rfl

/-- `Wlin n g` as a continuous linear map. -/
def WlinCL (n : ℕ) (g : PO n 1) : E n →L[ℝ] (Fin n ⊕ Fin 1 → ℝ) :=
  LinearMap.toContinuousLinearMap (Wlin n g)

lemma WlinCL_apply (n : ℕ) (g : PO n 1) (h : E n) : WlinCL n g h = Wlin n g h := rfl

/-- `WithLp.toLp 2` as a continuous linear map. -/
def toLpCL (n : ℕ) : (Fin n → ℝ) →L[ℝ] E n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

lemma toLpCL_apply (n : ℕ) (v : Fin n → ℝ) : toLpCL n v = WithLp.toLp 2 v := by
  change (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm v = WithLp.toLp 2 v
  exact PiLp.continuousLinearEquiv_symm_apply 2 ℝ (fun _ : Fin n => ℝ) v

/-- The spatial part of `wvec_visualDefs g ξ`, i.e. the numerator of `phiFun g ξ`. -/
def topVec (n : ℕ) (g : PO n 1) (ξ : E n) : E n :=
  WithLp.toLp 2 (fun i => wvec_visualDefs g ξ (Sum.inl i))

lemma hasFDerivAt_topVec (n : ℕ) (g : PO n 1) (ξ : E n) :
    HasFDerivAt (fun ξ : E n => topVec n g ξ)
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
          (Fin n → ℝ) →L[ℝ] E n).comp
        ((sqProj n).comp (LinearMap.toContinuousLinearMap (Wlin n g)))) ξ := by
  have h1 : HasFDerivAt (fun ξ : E n => (fun i : Fin n => wvec_visualDefs g ξ (Sum.inl i)))
      ((sqProj n).comp (LinearMap.toContinuousLinearMap (Wlin n g))) ξ := by
    have hpi : HasFDerivAt (fun w : Fin n ⊕ Fin 1 → ℝ => (fun i : Fin n => w (Sum.inl i)))
        (sqProj n) (wvec_visualDefs g ξ) := (sqProj n).hasFDerivAt (x := wvec_visualDefs g ξ)
    exact HasFDerivAt.comp (x := ξ) hpi (hasFDerivAt_wvec n g ξ)
  have h3 := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
      (Fin n → ℝ) →L[ℝ] E n).hasFDerivAt (x := (fun i => wvec_visualDefs g ξ (Sum.inl i)))
  have h4 := HasFDerivAt.comp (x := ξ) h3 h1
  refine h4.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y; rfl

/-- The derivative of `phiFun g` at `ξ` (a point where `dfun g ξ ≠ 0`). -/
noncomputable def dPhi (n : ℕ) (g : PO n 1) (ξ : E n) : E n →L[ℝ] E n :=
  (dfun g ξ)⁻¹ • ((toLpCL n).comp ((sqProj n).comp (WlinCL n g)))
    + ((ContinuousLinearMap.toSpanSingleton ℝ (-(dfun g ξ ^ 2)⁻¹)).comp
        ((ContinuousLinearMap.proj (Sum.inr 0)).comp (WlinCL n g))).smulRight (topVec n g ξ)

lemma hasFDerivAt_phiFun (n : ℕ) (g : PO n 1) (ξ : E n) (hd : dfun g ξ ≠ 0) :
    HasFDerivAt (phiFun g) (dPhi n g ξ) ξ := by
  have hdfun' : HasFDerivAt (fun ξ : E n => dfun g ξ)
      ((ContinuousLinearMap.proj (Sum.inr 0)).comp
        (LinearMap.toContinuousLinearMap (Wlin n g))) ξ := hasFDerivAt_dfun n g ξ
  have hinv : HasFDerivAt (fun ξ : E n => (dfun g ξ)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(dfun g ξ ^ 2)⁻¹)).comp
        ((ContinuousLinearMap.proj (Sum.inr 0)).comp
          (LinearMap.toContinuousLinearMap (Wlin n g)))) ξ :=
    HasFDerivAt.comp (x := ξ) (hasFDerivAt_inv (𝕜 := ℝ) hd) hdfun'
  have hsmul := HasFDerivAt.smul hinv (hasFDerivAt_topVec n g ξ)
  refine hsmul.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  show phiFun g y = (dfun g y)⁻¹ • topVec n g y
  rw [phiFun, topVec, ← WithLp.toLp_smul]
  congr 1
  funext i
  simp only [div_eq_inv_mul, Pi.smul_apply, smul_eq_mul]

lemma differentiableAt_phiFun (n : ℕ) (g : PO n 1) (ξ : E n) (hd : dfun g ξ ≠ 0) :
    DifferentiableAt ℝ (phiFun g) ξ := (hasFDerivAt_phiFun n g ξ hd).differentiableAt

/-- `homoExt g` is differentiable away from the origin. -/
lemma differentiableAt_homoExt (n : ℕ) (g : PO n 1) (x : E n) (hx : x ≠ 0) :
    DifferentiableAt ℝ (homoExt g) x := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : DifferentiableAt ℝ (fun y : E n => ‖y‖) x :=
    (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
  have hinvnorm : DifferentiableAt ℝ (fun y : E n => ‖y‖⁻¹) x := hnorm.inv hxn
  have hu : DifferentiableAt ℝ (fun y : E n => ‖y‖⁻¹ • y) x :=
    hinvnorm.smul (differentiableAt_id (𝕜 := ℝ) (x := x))
  have hu_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hxn]
  have hu_sph : ‖x‖⁻¹ • x ∈ Sph n := by
    rw [Sph, mem_sphere_zero_iff_norm]; exact hu_norm
  have hd : dfun g (‖x‖⁻¹ • x) ≠ 0 := ne_of_gt (dfunPosAux n g _ hu_sph)
  have hphi : DifferentiableAt ℝ (phiFun g) (‖x‖⁻¹ • x) :=
    differentiableAt_phiFun n g (‖x‖⁻¹ • x) hd
  have h1 : DifferentiableAt ℝ (fun y : E n => phiFun g (‖y‖⁻¹ • y)) x :=
    DifferentiableAt.comp (f := fun y : E n => ‖y‖⁻¹ • y) (x := x) hphi hu
  have h2 : DifferentiableAt ℝ (fun y : E n => ‖y‖ • phiFun g (‖y‖⁻¹ • y)) x :=
    hnorm.smul h1
  exact h2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq rfl)

/-- Fréchet derivative of the norm on `E n` away from the origin. -/
lemma hasFDerivAt_norm_of_ne_zero {n : ℕ} (x : E n) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E n => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hsq : HasFDerivAt (fun y : E n => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hxnorm
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt t)
      (1 / (2 * Real.sqrt (‖x‖ ^ 2))) (‖x‖ ^ 2) := Real.hasDerivAt_sqrt hne
  have hmain : HasFDerivAt (fun y : E n => Real.sqrt (‖y‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x := by
    simpa only [Function.comp_def] using hsqrt.comp_hasFDerivAt x hsq
  have hfun : (fun y : E n => Real.sqrt (‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [hfun] at hmain
  convert hmain using 1
  rw [Real.sqrt_sq (norm_nonneg x)]
  ext w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- Fréchet derivative of the radial renormalisation `y ↦ ‖y‖⁻¹ • y`. -/
lemma hasFDerivAt_invNorm_smul {n : ℕ} (x : E n) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E n => ‖y‖⁻¹ • y)
      (‖x‖⁻¹ • (1 : E n →L[ℝ] E n)
        - (((‖x‖ : ℝ) ^ 3)⁻¹) • ((innerSL ℝ x).smulRight x)) x := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm := hasFDerivAt_norm_of_ne_zero x hx
  have hcinv : HasFDerivAt (fun y : E n => (‖y‖)⁻¹)
      ((-(‖x‖ ^ 2)⁻¹) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
    (hasDerivAt_inv hxnorm).comp_hasFDerivAt x hnorm
  have hid : HasFDerivAt (fun y : E n => y) (1 : E n →L[ℝ] E n) x := hasFDerivAt_id x
  have hk := hcinv.smul hid
  show HasFDerivAt ((fun y : E n => (‖y‖)⁻¹) • fun y : E n => y)
      (‖x‖⁻¹ • (1 : E n →L[ℝ] E n)
        - (((‖x‖ : ℝ) ^ 3)⁻¹) • ((innerSL ℝ x).smulRight x)) x
  convert hk using 1
  apply ContinuousLinearMap.ext
  intro w
  simp only [sub_apply, add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  module

theorem homoExtFDerivAux (n : ℕ) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (x : Submission.Mostow.E n) (hx : x ≠ 0)
    (hd : Work.Mostow.dfun g (‖x‖⁻¹ • x) ≠ 0) :
    fderiv ℝ (Work.Mostow.homoExt g) x (‖x‖⁻¹ • x)
        = Work.Mostow.phiFun g (‖x‖⁻¹ • x) ∧
      ∀ v : Submission.Mostow.E n, inner ℝ x v = 0 →
        fderiv ℝ (Work.Mostow.homoExt g) x v
          = fderiv ℝ (Work.Mostow.phiFun g) (‖x‖⁻¹ • x) v := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  set K : E n →L[ℝ] E n := ‖x‖⁻¹ • (1 : E n →L[ℝ] E n)
      - (((‖x‖ : ℝ) ^ 3)⁻¹) • ((innerSL ℝ x).smulRight x) with hKdef
  have hk : HasFDerivAt (fun y : E n => ‖y‖⁻¹ • y) K x := by
    rw [hKdef]; exact hasFDerivAt_invNorm_smul x hx
  have hphid : DifferentiableAt ℝ (phiFun g) (‖x‖⁻¹ • x) :=
    differentiableAt_phiFun n g _ hd
  have hphi : HasFDerivAt (phiFun g) (fderiv ℝ (phiFun g) (‖x‖⁻¹ • x)) (‖x‖⁻¹ • x) :=
    hphid.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E n => phiFun g (‖y‖⁻¹ • y))
      ((fderiv ℝ (phiFun g) (‖x‖⁻¹ • x)).comp K) x :=
    HasFDerivAt.comp (f := fun y : E n => ‖y‖⁻¹ • y) x hphi hk
  have hnorm := hasFDerivAt_norm_of_ne_zero x hx
  have hprod := hnorm.smul hcomp
  have hmain : HasFDerivAt (homoExt g)
      (‖x‖ • (fderiv ℝ (phiFun g) (‖x‖⁻¹ • x) ∘SL K)
        + (‖x‖⁻¹ • innerSL ℝ x).smulRight (phiFun g (‖x‖⁻¹ • x))) x := hprod
  have hKu : K (‖x‖⁻¹ • x) = 0 := by
    rw [hKdef]
    simp only [sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq, one_apply_eq_self]
    rw [smul_smul, smul_smul, ← sub_smul]
    rw [show ‖x‖⁻¹ * ‖x‖⁻¹ - (‖x‖ ^ 3)⁻¹ * (‖x‖⁻¹ * ‖x‖ ^ 2) = 0 by field_simp; ring,
      zero_smul]
  have hAu : (‖x‖⁻¹ • innerSL ℝ x) (‖x‖⁻¹ • x) = 1 := by
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [smul_eq_mul]
    field_simp
  have hKv : ∀ v : E n, inner ℝ x v = 0 → K v = ‖x‖⁻¹ • v := by
    intro v hv
    rw [hKdef]
    simp only [sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, one_apply_eq_self, hv, zero_smul, smul_zero, sub_zero]
  have hAv : ∀ v : E n, inner ℝ x v = 0 → (‖x‖⁻¹ • innerSL ℝ x) v = 0 := by
    intro v hv; simp [hv]
  refine ⟨?_, ?_⟩
  · rw [hmain.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hKu, hAu, map_zero, smul_zero, zero_add, one_smul]
  · intro v hv
    rw [hmain.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hKv v hv, hAv v hv, zero_smul, smul_zero, add_zero]
    rw [map_smul, smul_smul, mul_inv_cancel₀ hxnorm, one_smul]

end

end Work.Mostow
