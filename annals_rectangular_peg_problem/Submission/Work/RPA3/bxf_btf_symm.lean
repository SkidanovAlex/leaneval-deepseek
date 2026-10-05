import Mathlib
import Submission.Work.RPA3.flux_prim_defs
import Submission.Work.RPA3.flux_prim_smooth

namespace Work.RPA3

noncomputable section

/-! ## The linear part of `τ_π`, and its constant part -/

/-- `q₁` as a continuous linear functional on `PS`. -/
private def tlq1 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `q₂` as a continuous linear functional on `PS`. -/
private def tlq2 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `p₁` as a continuous linear functional on `PS`. -/
private def tlp1 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `p₂` as a continuous linear functional on `PS`. -/
private def tlp2 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- The linear part `tauLin` of `τ_π` as a continuous linear map:
`(q₁, q₂, p₁, p₂) ↦ (-q₁, q₂, -p₁, p₂)`. -/
def tauLinL : PS →L[ℝ] PS :=
  (((-1 : ℝ) • tlq1).prod tlq2).prod (((-1 : ℝ) • tlp1).prod tlp2)

@[simp] theorem tauLinL_apply (a : PS) : tauLinL a = tauLin a := by
  simp [tauLinL, tauLin, tlq1, tlq2, tlp1, tlp2, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- The constant part of `τ_π`. -/
def tauShift : PS := ((0, Real.pi), (0, 0))

/-- `τ_π` is the affine map `y ↦ tauLin y + tauShift`. -/
theorem tau_pi_affine (a : PS) : tau Real.pi a = tauLin a + tauShift := by
  rw [tau_pi]
  ext <;> simp [tauLin, tauShift]

/-- The `τ_π`-symmetry of the family, in the form
`ℓ σ (-x, t+π) = tauLin (ℓ σ (x,t)) + tauShift`. -/
lemma symm_tauLin (L : LagFamily) (σ x t : ℝ) :
    L.ℓ σ (-x, t + Real.pi) = tauLin (L.ℓ σ (x, t)) + tauShift := by
  rw [L.symm σ x t, tau_pi_affine]

/-- Differentiating the composition of a curve with the (continuous) linear map `tauLin`
followed by a translation multiplies the derivative by `tauLin`:
`deriv (tauLin ∘ f + c) a = tauLin (deriv f a)`. -/
lemma deriv_tauLin_add_const (f : ℝ → PS) (c : PS) {a : ℝ} (hf : DifferentiableAt ℝ f a) :
    deriv (fun s => tauLin (f s) + c) a = tauLin (deriv f a) := by
  have hb : HasFDerivAt (⇑tauLinL) tauLinL (f a) := ContinuousLinearMap.hasFDerivAt tauLinL
  have h1 : HasFDerivAt (fun s => tauLinL (f s)) (tauLinL.comp (fderiv ℝ f a)) a := by
    have := hb.comp a hf.hasFDerivAt
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_def] using this
  have h2 : HasFDerivAt (fun s => tauLinL (f s) + c) (tauLinL.comp (fderiv ℝ f a)) a :=
    h1.add_const c
  have h3 : deriv (fun s => tauLinL (f s) + c) a = tauLinL (deriv f a) := by
    rw [← fderiv_apply_one_eq_deriv (f := fun s => tauLinL (f s) + c) (x := a), h2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv]
  have h4 : (fun s => tauLin (f s) + c) = fun s => tauLinL (f s) + c := by
    funext s; rw [tauLinL_apply]
  rw [h4, h3, tauLinL_apply]

/-! ## The three differentiated symmetry relations -/

/-- `∂_τℓ(τ, -x, t+π) = tauLin (∂_τℓ(τ, x, t))`. -/
lemma deriv_fst_symm (L : LagFamily) (τ x t : ℝ) :
    deriv (fun σ => L.ℓ σ (-x, t + Real.pi)) τ
      = tauLin (deriv (fun σ => L.ℓ σ (x, t)) τ) := by
  have hfun : (fun σ => L.ℓ σ (-x, t + Real.pi))
      = fun σ => tauLin (L.ℓ σ (x, t)) + tauShift := by
    funext σ; exact symm_tauLin L σ x t
  rw [hfun]
  exact deriv_tauLin_add_const (fun σ => L.ℓ σ (x, t)) tauShift
    (((contDiff_slice_fst L x t).differentiable (by norm_num)) τ)

/-- `∂_xℓ(τ, -x, t+π) = - tauLin (∂_xℓ(τ, x, t))`. -/
lemma deriv_snd_symm (L : LagFamily) (τ x t : ℝ) :
    deriv (fun y => L.ℓ τ (y, t + Real.pi)) (-x)
      = - tauLin (deriv (fun y => L.ℓ τ (y, t)) x) := by
  have hfun : (fun y => L.ℓ τ (y, t + Real.pi))
      = fun y => tauLin (L.ℓ τ (-y, t)) + tauShift := by
    funext y
    simpa using symm_tauLin L τ (-y) t
  rw [hfun]
  have hcomp : deriv (fun y => tauLin (L.ℓ τ (-y, t)) + tauShift) (-x)
      = - deriv (fun z => tauLin (L.ℓ τ (z, t)) + tauShift) x := by
    simpa using deriv_comp_neg (fun z => tauLin (L.ℓ τ (z, t)) + tauShift) (-x)
  rw [hcomp, deriv_tauLin_add_const (fun z => L.ℓ τ (z, t)) tauShift
    (((contDiff_slice_snd L τ t).differentiable (by norm_num)) x)]

/-- `∂_tℓ(τ, -x, t+π) = tauLin (∂_tℓ(τ, x, t))`. -/
lemma deriv_trd_symm (L : LagFamily) (τ x t : ℝ) :
    deriv (fun s => L.ℓ τ (-x, s)) (t + Real.pi)
      = tauLin (deriv (fun s => L.ℓ τ (x, s)) t) := by
  have hcomp : deriv (fun s => L.ℓ τ (-x, s)) (t + Real.pi)
      = deriv (fun s => L.ℓ τ (-x, s + Real.pi)) t :=
    (deriv_comp_add_const (fun s => L.ℓ τ (-x, s)) Real.pi t).symm
  rw [hcomp]
  have hfun : (fun s => L.ℓ τ (-x, s + Real.pi))
      = fun s => tauLin (L.ℓ τ (x, s)) + tauShift := by
    funext s; exact symm_tauLin L τ x s
  rw [hfun]
  exact deriv_tauLin_add_const (fun s => L.ℓ τ (x, s)) tauShift
    (((contDiff_slice_trd L τ x).differentiable (by norm_num)) t)

/-- The `τ_π`-symmetry of the family `ℓ τ (-x, t+π) = τ_π (ℓ τ (x,t))` makes the flux form
anti-invariant in its `x`-component and invariant in its `t`-component, under
`(x,t) ↦ (-x, t+π)`.

Route.  With `tauLin a = ((-a.1.1, a.1.2), (-a.2.1, a.2.2))` the linear part of `τ_π`
(`Work.RPA3.tau_pi`: `tau π a = tauLin a + ((0,π),(0,0))`), `LagFamily.symm` gives
`ℓ σ (-x, t+π) = tauLin (ℓ σ (x,t)) + ((0,π),(0,0))` for all `σ`.  Differentiating this identity
(a) in `σ` at `τ`, (b) in the second variable at `x` (using `deriv_comp_neg`:
`deriv (fun y => f (-y)) x = - deriv f (-x)`), and (c) in the second variable at `t` (using
`deriv_comp_add_const`) gives the three relations
`∂_τℓ(τ,-x,t+π) = tauLin (∂_τℓ(τ,x,t))`,
`∂_xℓ(τ,-x,t+π) = - tauLin (∂_xℓ(τ,x,t))` and
`∂_tℓ(τ,-x,t+π) = tauLin (∂_tℓ(τ,x,t))`.
One way to formalise (a) and (c) is to build the `ℝ`-linear identification
`tauLinL : PS →L[ℝ] PS` with `⇑tauLinL = tauLin` and use
`ContinuousLinearMap.hasFDerivAt` + `HasFDerivAt.comp_hasDerivAt` + `HasDerivAt.add_const`
(the differentiability of the slices is available as `Work.RPA3.contDiff_slice_fst`,
`contDiff_slice_snd`, `contDiff_slice_trd` in `flux_prim_smooth`). Finally
`Work.RPA3.symp_tauLin : symp (tauLin a) (tauLin b) = symp a b` (in `flux_prim_defs`), together
with `symp_neg_right`, gives `bxf`-anti-invariance and `btf`-invariance. -/
theorem bxf_btf_symm (L : Work.RPA3.LagFamily) (τ x t : ℝ) :
    Work.RPA3.bxf L τ (-x) (t + Real.pi) = -Work.RPA3.bxf L τ x t ∧
    Work.RPA3.btf L τ (-x) (t + Real.pi) = Work.RPA3.btf L τ x t := by
  have hA := deriv_fst_symm L τ x t
  have hB := deriv_snd_symm L τ x t
  have hC := deriv_trd_symm L τ x t
  constructor
  · show symp (deriv (fun σ => L.ℓ σ (-x, t + Real.pi)) τ)
        (deriv (fun y => L.ℓ τ (y, t + Real.pi)) (-x))
      = - symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x)
    rw [hA, hB, symp_neg_right, symp_tauLin]
  · show symp (deriv (fun σ => L.ℓ σ (-x, t + Real.pi)) τ)
        (deriv (fun s => L.ℓ τ (-x, s)) (t + Real.pi))
      = symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun s => L.ℓ τ (x, s)) t)
    rw [hA, hC, symp_tauLin]

end
end Work.RPA3
