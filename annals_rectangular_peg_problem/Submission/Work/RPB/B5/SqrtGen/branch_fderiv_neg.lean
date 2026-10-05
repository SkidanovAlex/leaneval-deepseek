import Mathlib
import Submission.Work.RPB.B5.SqrtGenDefs

/-!
# The Fréchet derivative of the negative branch `z ↦ z.2 ^ (n+1) • ψ (z.1, √(-z.2))`

On the open half-plane `z.2 < 0` the map `w ↦ w.2 ^ (n+1) • ψ (w.1, √(-w.2))`, with `ψ` smooth,
is differentiable at `z` with the explicit derivative recorded in `dG` (see `SqrtGenDefs`).

The computation is the chain rule along `u w = (w.1, √(-w.2))` (whose derivative is
`fst.prod ((1/(2√(-z.2))) • -snd)`) combined with the product rule for the scalar factor
`w.2 ^ (n+1)`; the two scalar contributions combine using `√(-x)² = -x`.
-/

noncomputable section

namespace Work.RPB.B5.SqrtGen

open scoped ContDiff

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous linear map on `X × ℝ` is determined by its restriction to `X` (through `fst`)
and its value at `(0,1)`. -/
private lemma clm_dec_comp_fst_smulRight (A : (X × ℝ) →L[ℝ] E) :
    A = (A.comp (ContinuousLinearMap.inl ℝ X ℝ)).comp (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight (A (0, 1)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  exact clm_apply_eq A v

/-- The derivative of the inner map `w ↦ (w.1, √(-w.2))` composed with `fderiv ℝ ψ`, rewritten in
terms of the partial derivatives `pdX` and `pdU`. -/
private lemma fderiv_comp_prod_neg (ψ : X × ℝ → E) (x : X) (ρ : ℝ) :
    (fderiv ℝ ψ (x, Real.sqrt (-ρ))).comp
        ((ContinuousLinearMap.fst ℝ X ℝ).prod
          ((1 / (2 * Real.sqrt (-ρ))) • (-(ContinuousLinearMap.snd ℝ X ℝ))))
      = (pdX ψ (x, Real.sqrt (-ρ))).comp (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight
            ((-(1 / (2 * Real.sqrt (-ρ)))) • pdU ψ (x, Real.sqrt (-ρ))) := by
  set L : (X × ℝ) →L[ℝ] (X × ℝ) :=
    (ContinuousLinearMap.fst ℝ X ℝ).prod
      ((1 / (2 * Real.sqrt (-ρ))) • (-(ContinuousLinearMap.snd ℝ X ℝ))) with hL
  have hLinl : L.comp (ContinuousLinearMap.inl ℝ X ℝ) = ContinuousLinearMap.inl ℝ X ℝ := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, hL, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
      neg_apply, ContinuousLinearMap.inl_apply]
    simp
  have hL01 : L (0, 1) = (0, -(1 / (2 * Real.sqrt (-ρ)))) := by
    simp only [hL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, neg_apply]
    simp
  have hAinl : ((fderiv ℝ ψ (x, Real.sqrt (-ρ))).comp L).comp
        (ContinuousLinearMap.inl ℝ X ℝ) = pdX ψ (x, Real.sqrt (-ρ)) := by
    rw [ContinuousLinearMap.comp_assoc, hLinl]
    rfl
  have hA01 : ((fderiv ℝ ψ (x, Real.sqrt (-ρ))).comp L) (0, 1)
      = (-(1 / (2 * Real.sqrt (-ρ)))) • pdU ψ (x, Real.sqrt (-ρ)) := by
    rw [ContinuousLinearMap.comp_apply, hL01]
    rw [show ((0 : X), (-(1 / (2 * Real.sqrt (-ρ)))))
        = (-(1 / (2 * Real.sqrt (-ρ)))) • ((0 : X), (1 : ℝ)) by simp]
    rw [map_smul]
    rfl
  rw [show (fderiv ℝ ψ (x, Real.sqrt (-ρ))).comp
        ((ContinuousLinearMap.fst ℝ X ℝ).prod
          ((1 / (2 * Real.sqrt (-ρ))) • (-(ContinuousLinearMap.snd ℝ X ℝ))))
      = (fderiv ℝ ψ (x, Real.sqrt (-ρ))).comp L from rfl]
  rw [clm_dec_comp_fst_smulRight ((fderiv ℝ ψ (x, Real.sqrt (-ρ))).comp L), hAinl, hA01]

/-- Chain rule for `z ↦ R (z.1, √(-z.2))` on the negative half-plane, `R` differentiable. -/
private lemma hasFDerivAt_sqrt_neg_comp {R : X × ℝ → E} (hRd : Differentiable ℝ R)
    {x : X} {ρ : ℝ} (hρ : ρ < 0) :
    HasFDerivAt (fun z : X × ℝ => R (z.1, Real.sqrt (-z.2)))
      ((fderiv ℝ R (x, Real.sqrt (-ρ))).comp
        ((ContinuousLinearMap.fst ℝ X ℝ).prod
          ((1 / (2 * Real.sqrt (-ρ))) • (-(ContinuousLinearMap.snd ℝ X ℝ))))) (x, ρ) := by
  have hsq : HasFDerivAt (fun z : X × ℝ => Real.sqrt (-z.2))
      ((1 / (2 * Real.sqrt (-ρ))) • (-(ContinuousLinearMap.snd ℝ X ℝ))) (x, ρ) :=
    ((hasFDerivAt_snd (p := (x, ρ))).neg).sqrt (show -ρ ≠ 0 by linarith)
  have hu : HasFDerivAt (fun z : X × ℝ => (z.1, Real.sqrt (-z.2)))
      ((ContinuousLinearMap.fst ℝ X ℝ).prod
        ((1 / (2 * Real.sqrt (-ρ))) • (-(ContinuousLinearMap.snd ℝ X ℝ)))) (x, ρ) :=
    HasFDerivAt.prodMk hasFDerivAt_fst hsq
  exact (hRd.differentiableAt.hasFDerivAt).comp (x, ρ) hu

/-- Pushing a scalar into the coefficient of a `smulRight` map. -/
private lemma smul_smulRight_neg (c : ℝ) (L : (X × ℝ) →L[ℝ] ℝ) (y : E) :
    c • (L.smulRight y) = L.smulRight (c • y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [smul_smul, smul_smul, mul_comm]

/-- Pushing a scalar into the defining functional of a `smulRight` map. -/
private lemma smul_smulRight_neg_c (c : ℝ) (L : (X × ℝ) →L[ℝ] ℝ) (y : E) :
    (c • L).smulRight y = L.smulRight (c • y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [smul_smul, mul_comm]

/-- Adding two `smulRight` maps with the same defining functional. -/
private lemma smulRight_add_neg (L : (X × ℝ) →L[ℝ] ℝ) (y₁ y₂ : E) :
    L.smulRight y₁ + L.smulRight y₂ = L.smulRight (y₁ + y₂) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [ContinuousLinearMap.smulRight_apply, smul_add]

/-- Scalar identity behind the second component of the derivative: `√(-x)² = -x`. -/
private lemma scalar_coeff_ident_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    x ^ (m + 1) * (-(1 / (2 * Real.sqrt (-x)))) = x ^ m * (1 / 2) * Real.sqrt (-x) := by
  have hs : 0 < Real.sqrt (-x) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (-x) ^ 2 = -x := Real.sq_sqrt (by linarith)
  have hmain : x * (-(1 / (2 * Real.sqrt (-x)))) = (1 / 2) * Real.sqrt (-x) := by
    field_simp
    nlinarith [hs2]
  rw [pow_succ, mul_assoc, hmain, ← mul_assoc]

/-- The two contributions to the second coordinate combine to the value recorded in `dG`. -/
private lemma neg_combine (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ) (hz : z.2 < 0) :
    z.2 ^ (n + 1) • ((-(1 / (2 * Real.sqrt (-z.2)))) • pdU ψ (z.1, Real.sqrt (-z.2)))
      + (z.2 ^ n * ((n + 1 : ℕ) : ℝ)) • ψ (z.1, Real.sqrt (-z.2))
    = z.2 ^ n • ((n + 1) • ψ (z.1, Real.sqrt (-z.2))
        + (1 / 2 : ℝ) • (Real.sqrt (-z.2) • pdU ψ (z.1, Real.sqrt (-z.2)))) := by
  have ht1 : z.2 ^ (n + 1) * (-(1 / (2 * Real.sqrt (-z.2))))
      = z.2 ^ n * (1 / 2) * Real.sqrt (-z.2) :=
    scalar_coeff_ident_neg hz n
  rw [smul_smul, ht1]
  rw [smul_add, smul_smul, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℝ (n + 1) (ψ (z.1, Real.sqrt (-z.2)))]
  rw [smul_smul, add_comm]

theorem branch_fderiv_neg {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ)
    (hψ : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ψ) (hz : z.2 < 0) :
    HasFDerivAt (fun w : X × ℝ => w.2 ^ (n + 1) • ψ (w.1, Real.sqrt (-w.2)))
      (Work.RPB.B5.SqrtGen.dG ψ n z) z := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hbase : HasFDerivAt (fun w : X × ℝ => ψ (w.1, Real.sqrt (-w.2)))
      ((fderiv ℝ ψ (z.1, Real.sqrt (-z.2))).comp
        ((ContinuousLinearMap.fst ℝ X ℝ).prod
          ((1 / (2 * Real.sqrt (-z.2))) • (-(ContinuousLinearMap.snd ℝ X ℝ))))) z :=
    hasFDerivAt_sqrt_neg_comp hψd hz
  have hbase' : HasFDerivAt (fun w : X × ℝ => ψ (w.1, Real.sqrt (-w.2)))
      ((pdX ψ (z.1, Real.sqrt (-z.2))).comp (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight
            ((-(1 / (2 * Real.sqrt (-z.2)))) • pdU ψ (z.1, Real.sqrt (-z.2)))) z :=
    hbase.congr_fderiv (fderiv_comp_prod_neg ψ z.1 z.2)
  have hpow : HasFDerivAt (fun w : X × ℝ => w.2 ^ (n + 1))
      ((z.2 ^ n * ((n + 1 : ℕ) : ℝ)) • (ContinuousLinearMap.snd ℝ X ℝ)) z := by
    have h1 : HasFDerivAt (fun w : X × ℝ => w.2) (ContinuousLinearMap.snd ℝ X ℝ) z :=
      hasFDerivAt_snd
    have h2 := h1.pow (n + 1)
    have hc : (((n + 1 : ℕ) • z.2 ^ ((n + 1) - 1)) : ℝ) = z.2 ^ n * ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.succ_sub_one, nsmul_eq_mul, mul_comm]
    rwa [hc] at h2
  have hprod := hpow.smul hbase'
  refine hprod.congr_fderiv ?_
  rw [dG_eq_neg ψ n z hz]
  conv_lhs => rw [smul_add]
  rw [← ContinuousLinearMap.smul_comp, smul_smulRight_neg, smul_smulRight_neg_c, add_assoc,
      smulRight_add_neg]
  rw [neg_combine ψ n z hz]

end Work.RPB.B5.SqrtGen
