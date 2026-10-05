import Mathlib
import Submission.Work.RPB.B5.SqrtGenDefs
import Submission.Work.RPB.B3.evenSqrtPeriodic

/-!
# The Fréchet derivative of the positive branch `z ↦ z.2 ^ (n+1) • ψ (z.1, √z.2)` (general `X`)

On the half-plane `z.2 > 0` the map `w ↦ w.2 ^ (n + 1) • ψ (w.1, √w.2)` is differentiable at `z`,
with Fréchet derivative the explicit expression `dG ψ n z` of `SqrtGenDefs`.  The computation is
the elementary chain rule: the derivative of `w ↦ (w.1, √w.2)` is
`fst.prod ((1/(2√z.2)) • snd)`, the coefficient `z.2 ^ (n+1)` contributes `(n+1) z.2 ^ n` in the
second coordinate, and the two scalar identities are collected in `coeff_identity_snd_aux`.

The chain rule for `w ↦ ψ (w.1, √w.2)` (with `X` an arbitrary real normed space) is
`Work.RPB.B3.hasFDerivAt_sqrt_comp`.
-/

noncomputable section

namespace Work.RPB.B5.SqrtGen

open scoped ContDiff

set_option autoImplicit false

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Auxiliary continuous-linear-map identities -/

/-- Pulling a scalar out of `smulRight`. -/
private lemma smul_smulRight_aux (c : ℝ) (L : (X × ℝ) →L[ℝ] ℝ) (y : E) :
    c • (L.smulRight y) = L.smulRight (c • y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [smul_comm]

/-- `smulRight` is additive in its vector argument. -/
private lemma smulRight_add_aux (L : (X × ℝ) →L[ℝ] ℝ) (x y : E) :
    L.smulRight x + L.smulRight y = L.smulRight (x + y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_add]

/-- The composition of `D` with the derivative of `w ↦ (w.1, c * w.2)`, expanded along the two
factors of `X × ℝ`. -/
private lemma comp_prod_smul_snd_aux (D : (X × ℝ) →L[ℝ] E) (c : ℝ) :
    D.comp ((ContinuousLinearMap.fst ℝ X ℝ).prod (c • (ContinuousLinearMap.snd ℝ X ℝ)))
      = (D.comp (ContinuousLinearMap.inl ℝ X ℝ)).comp (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight (c • D (0, 1)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hsplit : D (v.1, c * v.2)
      = (D.comp (ContinuousLinearMap.inl ℝ X ℝ)) v.1 + (c * v.2) • D (0, 1) := by
    have h := clm_apply_eq D (v.1, c * v.2)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [hsplit, mul_smul, smul_comm]
  simp only [ContinuousLinearMap.comp_apply]

/-- The scalar identity behind the second component of the derivative. -/
private lemma coeff_identity_snd_aux (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (B Y : E) :
    ρ ^ (n + 1) • ((ContinuousLinearMap.snd ℝ X ℝ).smulRight ((1 / (2 * Real.sqrt ρ)) • B))
      + ((((n + 1 : ℕ) : ℝ) * ρ ^ n) • (ContinuousLinearMap.snd ℝ X ℝ)).smulRight Y
      = (ContinuousLinearMap.snd ℝ X ℝ).smulRight
          (ρ ^ n • ((n + 1) • Y + (1 / 2 : ℝ) • (Real.sqrt ρ • B))) := by
  have hsc : ρ ^ (n + 1) * (1 / (2 * Real.sqrt ρ)) = ρ ^ n * ((1 / 2 : ℝ) * Real.sqrt ρ) := by
    rw [Work.RPB.B3.pow_mul_inv_sqrt hρ (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]
    ring
  rw [smul_smulRight_aux, Work.RPB.B3.smul_smulRight', smulRight_add_aux]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ (n + 1) Y]
  simp only [smul_add, smul_smul]
  rw [hsc]
  module

/-! ## The derivative computation -/

theorem branch_fderiv_pos {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ)
    (hψ : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ψ) (hz : 0 < z.2) :
    HasFDerivAt (fun w : X × ℝ => w.2 ^ (n + 1) • ψ (w.1, Real.sqrt w.2))
      (Work.RPB.B5.SqrtGen.dG ψ n z) z := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  -- the smooth part `w ↦ ψ (w.1, √w.2)`, rewritten in terms of the partial derivatives
  have hbase : HasFDerivAt (fun w : X × ℝ => ψ (w.1, Real.sqrt w.2))
      ((fderiv ℝ ψ (z.1, Real.sqrt z.2)).comp
        ((ContinuousLinearMap.fst ℝ X ℝ).prod
          ((1 / (2 * Real.sqrt z.2)) • (ContinuousLinearMap.snd ℝ X ℝ)))) z :=
    Work.RPB.B3.hasFDerivAt_sqrt_comp hψd hz
  have hbase' : HasFDerivAt (fun w : X × ℝ => ψ (w.1, Real.sqrt w.2))
      ((pdX ψ (z.1, Real.sqrt z.2)).comp (ContinuousLinearMap.fst ℝ X ℝ)
        + (ContinuousLinearMap.snd ℝ X ℝ).smulRight
            ((1 / (2 * Real.sqrt z.2)) • pdU ψ (z.1, Real.sqrt z.2))) z := by
    refine hbase.congr_fderiv ?_
    simp only [pdX, pdU]
    exact comp_prod_smul_snd_aux (fderiv ℝ ψ (z.1, Real.sqrt z.2)) (1 / (2 * Real.sqrt z.2))
  -- the scalar coefficient `w ↦ w.2 ^ (n+1)`
  have hpow : HasFDerivAt (fun w : X × ℝ => w.2 ^ (n + 1))
      ((((n + 1 : ℕ) : ℝ) * z.2 ^ n) • (ContinuousLinearMap.snd ℝ X ℝ)) z := by
    have h0 : HasFDerivAt (fun y : ℝ => y ^ (n + 1))
        ((((n + 1 : ℕ) : ℝ) * z.2 ^ n) • ContinuousLinearMap.id ℝ ℝ) z.2 := by
      have h1 := (hasDerivAt_pow (n + 1) z.2).hasFDerivAt
      convert h1 using 1
      ext
      simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
    have h3 : HasFDerivAt ((fun y : ℝ => y ^ (n + 1)) ∘ fun w : X × ℝ => w.2)
        ((((n + 1 : ℕ) : ℝ) * z.2 ^ n) • (ContinuousLinearMap.snd ℝ X ℝ)) z :=
      HasFDerivAt.comp z h0
        (hasFDerivAt_snd : HasFDerivAt (fun w : X × ℝ => w.2)
          (ContinuousLinearMap.snd ℝ X ℝ) z)
    show HasFDerivAt (fun w : X × ℝ => w.2 ^ (n + 1))
        ((((n + 1 : ℕ) : ℝ) * z.2 ^ n) • (ContinuousLinearMap.snd ℝ X ℝ)) z
    exact h3
  have hprod := hpow.smul hbase'
  refine hprod.congr_fderiv ?_
  rw [dG_eq_pos ψ n z hz]
  conv_lhs =>
    rw [smul_add]
    rw [← ContinuousLinearMap.smul_comp]
    rw [add_assoc]
    rw [coeff_identity_snd_aux (X := X) n hz (pdU ψ (z.1, Real.sqrt z.2))
      (ψ (z.1, Real.sqrt z.2))]

end Work.RPB.B5.SqrtGen
