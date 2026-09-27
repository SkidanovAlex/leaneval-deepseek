import Mathlib
import Submission.Work.Mostow.fermiSetup
import Submission.Work.Mostow.det_one_add_smulRight
import Submission.Work.Mostow.hasFDerivAt_norm
import Submission.Work.Mostow.det_blockTriangular

set_option synthInstance.maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow
open ContinuousLinearMap

noncomputable section

/-- derivative of `sinhc` away from `0`. -/
def sinhcDeriv (s : ℝ) : ℝ := (s * Real.cosh s - Real.sinh s) / s ^ 2

lemma hasDerivAt_sinhc {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt Submission.Mostow.sinhc (sinhcDeriv s) s := by
  have h3 : HasDerivAt (fun t : ℝ => Real.sinh t / t)
      ((Real.cosh s * s - Real.sinh s * 1) / s ^ 2) s :=
    (Real.hasDerivAt_sinh s).div (hasDerivAt_id s) hs
  have h4 : (Real.cosh s * s - Real.sinh s * 1) / s ^ 2 = sinhcDeriv s := by
    rw [sinhcDeriv]; ring
  rw [h4] at h3
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hs] with t ht
  simp only [Submission.Mostow.sinhc, ite_eq_right ht]

lemma sinhc_pos {s : ℝ} (hs : 0 < s) : 0 < Submission.Mostow.sinhc s := by
  rw [Submission.Mostow.sinhc, ite_eq_right hs.ne']
  exact div_pos (Real.sinh_pos_iff.mpr hs) hs

lemma sinhc_add_smul_deriv {s : ℝ} (hs : 0 < s) :
    Submission.Mostow.sinhc s + s * sinhcDeriv s = Real.cosh s := by
  rw [Submission.Mostow.sinhc, ite_eq_right hs.ne', sinhcDeriv]
  field_simp
  ring

lemma coe_innerSL_apply {m : ℕ} (u v : Submission.Mostow.E m) :
    ((innerSL ℝ u : Submission.Mostow.E m →L[ℝ] ℝ) : Submission.Mostow.E m →ₗ[ℝ] ℝ) v =
      inner ℝ u v := rfl

theorem fermiG_det (k m : ℕ) (x : Submission.Mostow.E k × Submission.Mostow.E m) (hx : x.2 ≠ 0) :
    DifferentiableAt ℝ (fun y : Submission.Mostow.E k × Submission.Mostow.E m =>
        (Real.cosh ‖y.2‖ • y.1, Submission.Mostow.sinhc ‖y.2‖ • y.2)) x ∧
      |(fderiv ℝ (fun y : Submission.Mostow.E k × Submission.Mostow.E m =>
        (Real.cosh ‖y.2‖ • y.1, Submission.Mostow.sinhc ‖y.2‖ • y.2)) x).det| =
        Real.cosh ‖x.2‖ ^ (k + 1) * Submission.Mostow.sinhc ‖x.2‖ ^ (m - 1) := by
  set φ : ℝ := Submission.Mostow.sinhc ‖x.2‖ with hφdef
  have hs : 0 < ‖x.2‖ := norm_pos_iff.mpr hx
  have hsne : ‖x.2‖ ≠ 0 := hs.ne'
  have hφpos : 0 < φ := by rw [hφdef]; exact sinhc_pos hs
  have hφne : φ ≠ 0 := hφpos.ne'
  have hm : 0 < m := by
    have : Nontrivial (E m) := ⟨x.2, 0, hx⟩
    have h1 : 0 < Module.finrank ℝ (E m) := Module.finrank_pos
    rwa [finrank_euclideanSpace, Fintype.card_fin] at h1
  -- derivative of the norm
  have hnorm : HasFDerivAt (fun y : E m => ‖y‖) ((1 / ‖x.2‖) • innerSL ℝ x.2) x.2 :=
    hasFDerivAt_norm (E := E m) hx
  have hgnorm : HasFDerivAt (fun y : E k × E m => ‖y.2‖)
      (((1 / ‖x.2‖) • innerSL ℝ x.2).comp (snd ℝ (E k) (E m))) x :=
    hnorm.comp x (hasFDerivAt_snd (p := x))
  have hcosh : HasFDerivAt (fun y : E k × E m => Real.cosh ‖y.2‖)
      (Real.sinh ‖x.2‖ • ((1 / ‖x.2‖) • innerSL ℝ x.2).comp (snd ℝ (E k) (E m))) x := by
    have h := (Real.hasDerivAt_cosh ‖x.2‖).comp_hasFDerivAt
      (f := fun y : E k × E m => ‖y.2‖) x hgnorm
    simpa [Function.comp_def] using h
  have hsinhc : HasFDerivAt (fun y : E k × E m => Submission.Mostow.sinhc ‖y.2‖)
      (sinhcDeriv ‖x.2‖ • ((1 / ‖x.2‖) • innerSL ℝ x.2).comp (snd ℝ (E k) (E m))) x := by
    have h := (hasDerivAt_sinhc hsne).comp_hasFDerivAt
      (f := fun y : E k × E m => ‖y.2‖) x hgnorm
    simpa [Function.comp_def] using h
  have hfst : HasFDerivAt (fun y : E k × E m => y.1) (fst ℝ (E k) (E m)) x := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun y : E k × E m => y.2) (snd ℝ (E k) (E m)) x := hasFDerivAt_snd
  set L1 : (E k × E m) →L[ℝ] E k :=
    Real.cosh ‖x.2‖ • fst ℝ (E k) (E m)
      + (Real.sinh ‖x.2‖ • ((1 / ‖x.2‖) • innerSL ℝ x.2).comp (snd ℝ (E k) (E m))).smulRight x.1 with hL1
  set L2 : (E k × E m) →L[ℝ] E m :=
    φ • snd ℝ (E k) (E m)
      + (sinhcDeriv ‖x.2‖ • ((1 / ‖x.2‖) • innerSL ℝ x.2).comp (snd ℝ (E k) (E m))).smulRight x.2 with hL2
  have h1 : HasFDerivAt (fun y : E k × E m => Real.cosh ‖y.2‖ • y.1) L1 x := by
    rw [hL1]
    exact hcosh.smul hfst
  have h2 : HasFDerivAt (fun y : E k × E m => Submission.Mostow.sinhc ‖y.2‖ • y.2) L2 x := by
    rw [hL2, hφdef]
    exact hsinhc.smul hsnd
  have hmain : HasFDerivAt (fun y : E k × E m =>
      (Real.cosh ‖y.2‖ • y.1, Submission.Mostow.sinhc ‖y.2‖ • y.2)) (L1.prod L2) x :=
    h1.prodMk h2
  refine ⟨hmain.differentiableAt, ?_⟩
  rw [hmain.fderiv]
  -- determinant computation
  set A1 : ℝ := Real.sinh ‖x.2‖ * (1 / ‖x.2‖) with hA1
  set A2 : ℝ := sinhcDeriv ‖x.2‖ * (1 / ‖x.2‖) with hA2
  set dlt : ℝ := sinhcDeriv ‖x.2‖ / (‖x.2‖ * φ) with hdlt
  set fL : E k →ₗ[ℝ] E k := Real.cosh ‖x.2‖ • LinearMap.id with hfL
  set gL : E m →ₗ[ℝ] E k := A1 • (innerSL ℝ x.2 : E m →ₗ[ℝ] ℝ).smulRight x.1 with hgL
  set CL : E m →ₗ[ℝ] E m :=
    LinearMap.id + (innerSL ℝ (dlt • x.2) : E m →ₗ[ℝ] ℝ).smulRight x.2 with hCL
  set hL : E m →ₗ[ℝ] E m := φ • CL with hhL
  have hφdlt : φ * dlt = A2 := by
    rw [hA2, hdlt]
    field_simp
  have hfacL : (↑(L1.prod L2) : (E k × E m) →ₗ[ℝ] (E k × E m)) =
      LinearMap.prod (fL.comp (LinearMap.fst ℝ (E k) (E m)) + gL.comp (LinearMap.snd ℝ (E k) (E m)))
        (hL.comp (LinearMap.snd ℝ (E k) (E m))) := by
    apply LinearMap.ext
    intro p
    change (L1.prod L2) p =
      (LinearMap.prod (fL.comp (LinearMap.fst ℝ (E k) (E m)) + gL.comp (LinearMap.snd ℝ (E k) (E m)))
        (hL.comp (LinearMap.snd ℝ (E k) (E m)))) p
    rw [ContinuousLinearMap.prod_apply, LinearMap.prod_apply]
    refine Prod.ext ?_ ?_
    · show L1 p = fL p.1 + gL p.2
      rw [hL1, hfL, hgL]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, innerSL_apply_apply,
        coe_innerSL_apply, hA1, smul_eq_mul, smul_smul, mul_assoc]
    · show L2 p = hL p.2
      rw [hL2, hhL, hCL]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_snd',
        LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply, LinearMap.snd_apply, innerSL_apply_apply,
        coe_innerSL_apply, real_inner_smul_left,
        smul_add, smul_eq_mul, smul_smul, mul_assoc]
      rw [← mul_assoc, ← hA2, ← hφdlt, mul_assoc]
  have hkey : ‖x.2‖ * sinhcDeriv ‖x.2‖ = Real.cosh ‖x.2‖ - φ := by
    have h := sinhc_add_smul_deriv hs
    rw [← hφdef] at h
    linarith
  have h1dlt : 1 + dlt * ‖x.2‖ ^ 2 = Real.cosh ‖x.2‖ / φ := by
    have h2' : dlt * ‖x.2‖ ^ 2 = (‖x.2‖ * sinhcDeriv ‖x.2‖) / φ := by
      rw [hdlt]; field_simp
    rw [h2', hkey]
    field_simp
    ring
  have hfLdet : LinearMap.det fL = Real.cosh ‖x.2‖ ^ k := by
    rw [hfL, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_euclideanSpace,
      Fintype.card_fin]
  have hCLdet : LinearMap.det CL = 1 + dlt * ‖x.2‖ ^ 2 := by
    have hCL' : CL = (1 : E m →ₗ[ℝ] E m) +
        (innerSL ℝ (dlt • x.2) : E m →ₗ[ℝ] ℝ).smulRight x.2 := hCL
    rw [hCL', det_one_add_smulRight, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hhLdet : LinearMap.det hL = φ ^ m * (1 + dlt * ‖x.2‖ ^ 2) := by
    rw [hhL, LinearMap.det_smul, hCLdet, finrank_euclideanSpace, Fintype.card_fin]
  have hpow : φ ^ m / φ = φ ^ (m - 1) := by
    have hmm : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have h1 : φ ^ m = φ ^ (m - 1) * φ := by
      nth_rewrite 1 [← hmm]
      rw [pow_succ]
    rw [h1, mul_div_cancel_right₀ _ hφne]
  have hdet : LinearMap.det (↑(L1.prod L2) : (E k × E m) →ₗ[ℝ] (E k × E m)) =
      Real.cosh ‖x.2‖ ^ (k + 1) * φ ^ (m - 1) := by
    rw [hfacL, det_blockTriangular fL gL hL, hfLdet, hhLdet]
    have hsplit : φ ^ m * (Real.cosh ‖x.2‖ / φ) = (φ ^ m / φ) * Real.cosh ‖x.2‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [h1dlt, hsplit, hpow, pow_succ]
    ring
  have hpos : 0 < Real.cosh ‖x.2‖ ^ (k + 1) * φ ^ (m - 1) := by positivity
  rw [show (L1.prod L2).det = LinearMap.det (↑(L1.prod L2) : (E k × E m) →ₗ[ℝ] (E k × E m))
      from rfl, hdet, abs_of_pos hpos, hφdef]

end

end Work.Mostow
