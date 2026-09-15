import Submission.FUP.Dbar2Calc

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The covariant shift and the invariance of `ϑ = ∂̄^*` under it

For a smooth real weight `φ` and `y ∈ ℂᵈ`, the *covariant shift* of a form `ψ` is

  `shiftForm φ y ψ = fun z => e^{φ z - φ (z+y)} • ψ (z+y)`.

Since the weight `e^{-φ}` is carried along, the formal adjoints `ϑ₁ = dbarAdjoint` and
`ϑ₂ = dbarAdjoint2` are *covariantly* translation invariant:

  `ϑ (shiftForm φ y ψ) z = e^{φ z - φ (z+y)} · (ϑ ψ) (z+y)`.

Equivalently `e^{-φ z} (ϑ (shift ψ)) z = e^{-φ (z+y)} (ϑ ψ) (z+y)`: the quantity `e^{-φ} ϑψ` is
translation invariant.  This is the key identity behind the fact that the *weighted* weak
`∂̄`-relation is preserved by convolution with a mollifier.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The phase factor `e^{φ(z) - φ(z+y)}` of the covariant shift. -/
noncomputable def covShift (φ : FormDu d → ℝ) (y z : FormDu d) : ℂ :=
  Complex.exp (((φ z : ℝ) : ℂ) - ((φ (z + y) : ℝ) : ℂ))

/-- The covariant shift `ψ ↦ e^{φ(·) - φ(·+y)} ψ(·+y)`. -/
noncomputable def shiftForm (φ : FormDu d → ℝ) (y : FormDu d)
    (ψ : FormDu d → FormSpace d) : FormDu d → FormSpace d :=
  fun z => covShift φ y z • ψ (z + y)

@[simp] lemma covShift_apply (φ : FormDu d → ℝ) (y z : FormDu d) :
    covShift φ y z = Complex.exp (((φ z : ℝ) : ℂ) - ((φ (z + y) : ℝ) : ℂ)) := rfl

@[simp] lemma shiftForm_apply (φ : FormDu d → ℝ) (y z : FormDu d)
    (ψ : FormDu d → FormSpace d) :
    shiftForm φ y ψ z = covShift φ y z • ψ (z + y) := rfl

/-- The Wirtinger derivative `∂_j` commutes with translation. -/
lemma partialZ_comp_add (j : Fin d) (g : FormDu d → ℂ) (y z : FormDu d) :
    partialZ j (fun w => g (w + y)) z = partialZ j g (z + y) := by
  simp only [partialZ, fderiv_comp_add_right]

/-- `toFormFun` of a covariant shift. -/
lemma toFormFun_shiftForm (φ : FormDu d → ℝ) (y : FormDu d)
    (ψ : FormDu d → FormSpace d) :
    toFormFun (shiftForm φ y ψ)
      = fun z j => covShift φ y z * toFormFun ψ (z + y) j := by
  funext z j
  simp only [toFormFun_apply, shiftForm_apply, WithLp.equiv_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]

/-- The covariant shift of a smooth form is smooth. -/
lemma contDiff_shiftForm {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ) {y : FormDu d}
    {ψ : FormDu d → FormSpace d} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (shiftForm φ y ψ) := by
  have hc : ContDiff ℝ ∞ fun z : FormDu d => covShift φ y z := by
    unfold covShift
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp hφ).sub
        ((Complex.ofRealCLM.contDiff.comp hφ).comp (contDiff_id.add contDiff_const)))
  exact hc.smul (hψ.comp (contDiff_id.add contDiff_const))

/-- The covariant shift preserves compact support. -/
lemma hasCompactSupport_shiftForm {φ : FormDu d → ℝ} {y : FormDu d}
    {ψ : FormDu d → FormSpace d} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (shiftForm φ y ψ) := by
  have h1 : HasCompactSupport (fun z : FormDu d => ψ (z + y)) :=
    hψ.comp_homeomorph (Homeomorph.addRight y)
  exact h1.smul_left (f := fun z : FormDu d => covShift φ y z)

/-- `∂_j` of the phase factor. -/
lemma partialZ_covShift {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {y z : FormDu d} (j : Fin d) :
    partialZ j (fun w => covShift φ y w) z
      = covShift φ y z * (partialZ j (fun w => ((φ w : ℝ) : ℂ)) z
          - partialZ j (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
  have hΦ : ContDiff ℝ 2 fun w : FormDu d => ((φ w : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have h2 : DifferentiableAt ℝ (fun w : FormDu d => ((φ (w + y) : ℝ) : ℂ)) z :=
    (hΦ.comp (contDiff_id.add contDiff_const)).differentiable (by norm_num) z
  have hd : DifferentiableAt ℝ
      (fun w : FormDu d => ((φ w : ℝ) : ℂ) - ((φ (w + y) : ℝ) : ℂ)) z :=
    (hΦ.differentiable (by norm_num) z).sub h2
  have h := partialZ_exp (ψ := fun w : FormDu d => ((φ w : ℝ) : ℂ) - ((φ (w + y) : ℝ) : ℂ))
    hd (k := j) (z := z)
  have hsub : partialZ j (fun w : FormDu d => ((φ w : ℝ) : ℂ) - ((φ (w + y) : ℝ) : ℂ)) z
      = partialZ j (fun w : FormDu d => ((φ w : ℝ) : ℂ)) z
        - partialZ j (fun w : FormDu d => ((φ w : ℝ) : ℂ)) (z + y) := by
    rw [partialZ_sub j (hΦ.differentiable (by norm_num) z) h2]
    rw [show partialZ j (fun w : FormDu d => ((φ (w + y) : ℝ) : ℂ)) z
        = partialZ j (fun w : FormDu d => ((φ w : ℝ) : ℂ)) (z + y) from
      partialZ_comp_add j (fun w => ((φ w : ℝ) : ℂ)) y z]
  rw [show (fun w : FormDu d => covShift φ y w)
      = fun w => Complex.exp (((φ w : ℝ) : ℂ) - ((φ (w + y) : ℝ) : ℂ)) from rfl, h, hsub]
  rfl

/-- **Covariant translation invariance of `ϑ₁ = dbarAdjoint`.** -/
theorem dbarAdjoint_shiftForm {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {ψ : FormDu d → FormSpace d} (hψ : ContDiff ℝ ∞ ψ) (y z : FormDu d) :
    dbarAdjoint φ (toFormFun (shiftForm φ y ψ)) z
      = covShift φ y z * dbarAdjoint φ (toFormFun ψ) (z + y) := by
  have hΦ : ContDiff ℝ 2 fun w : FormDu d => ((φ w : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hcd : DifferentiableAt ℝ (fun w : FormDu d => covShift φ y w) z := by
    have h : ContDiff ℝ 2 (fun w : FormDu d => covShift φ y w) := by
      unfold covShift
      exact Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp hφ).sub
          ((Complex.ofRealCLM.contDiff.comp hφ).comp (contDiff_id.add contDiff_const)))
    exact h.differentiable (by norm_num) z
  have hgd : ∀ j : Fin d, DifferentiableAt ℝ (fun w : FormDu d => toFormFun ψ (w + y) j) z := by
    intro j
    have h : ContDiff ℝ 1 (fun w : FormDu d => toFormFun ψ w j) :=
      (contDiff_toFormFun hψ j).of_le (by simp)
    exact (h.comp (contDiff_id.add contDiff_const)).differentiable (by norm_num) z
  have hkey : ∀ j : Fin d,
      (partialZ j (fun w => toFormFun (shiftForm φ y ψ) w j) z
          - toFormFun (shiftForm φ y ψ) z j
              * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
        = covShift φ y z
          * (partialZ j (fun w => toFormFun ψ w j) (z + y)
              - toFormFun ψ (z + y) j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
    intro j
    have hfun : (fun w => toFormFun (shiftForm φ y ψ) w j)
        = fun w => covShift φ y w * toFormFun ψ (w + y) j := by
      funext w
      rw [toFormFun_shiftForm]
    have hval : toFormFun (shiftForm φ y ψ) z j
        = covShift φ y z * toFormFun ψ (z + y) j := by
      rw [toFormFun_shiftForm]
    have hcomp : partialZ j (fun w : FormDu d => toFormFun ψ (w + y) j) z
        = partialZ j (fun w => toFormFun ψ w j) (z + y) :=
      partialZ_comp_add j (fun w => toFormFun ψ w j) y z
    rw [hfun, partialZ_mul hcd (hgd j), partialZ_covShift hφ (y := y) (z := z) j, hcomp, hval]
    ring
  have hsum : dbarAdjoint φ (toFormFun (shiftForm φ y ψ)) z
      = - (∑ j : Fin d, covShift φ y z
          * (partialZ j (fun w => toFormFun ψ w j) (z + y)
              - toFormFun ψ (z + y) j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) (z + y))) := by
    rw [dbarAdjoint]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hkey j
  rw [hsum, dbarAdjoint, mul_neg, Finset.mul_sum]

/-! ## The `(0,2)` version -/

/-- The covariant shift of a `(0,2)`-form. -/
noncomputable def shiftForm2 (φ : FormDu d → ℝ) (y : FormDu d)
    (Ψ : FormDu d → FormSpace2 d) : FormDu d → FormSpace2 d :=
  fun z => covShift φ y z • Ψ (z + y)

@[simp] lemma shiftForm2_apply (φ : FormDu d → ℝ) (y z : FormDu d)
    (Ψ : FormDu d → FormSpace2 d) :
    shiftForm2 φ y Ψ z = covShift φ y z • Ψ (z + y) := rfl

/-- `toFormFun2` of a covariant shift. -/
lemma toFormFun2_shiftForm2 (φ : FormDu d → ℝ) (y : FormDu d)
    (Ψ : FormDu d → FormSpace2 d) :
    toFormFun2 (shiftForm2 φ y Ψ)
      = fun z i => covShift φ y z * toFormFun2 Ψ (z + y) i := by
  funext z i
  simp only [toFormFun2_apply, shiftForm2_apply, WithLp.equiv_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]

/-- The covariant shift of a smooth `(0,2)`-form is smooth. -/
lemma contDiff_shiftForm2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ) {y : FormDu d}
    {Ψ : FormDu d → FormSpace2 d} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (shiftForm2 φ y Ψ) := by
  have hc : ContDiff ℝ ∞ fun z : FormDu d => covShift φ y z := by
    unfold covShift
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp hφ).sub
        ((Complex.ofRealCLM.contDiff.comp hφ).comp (contDiff_id.add contDiff_const)))
  exact hc.smul (hΨ.comp (contDiff_id.add contDiff_const))

/-- The covariant shift preserves compact support. -/
lemma hasCompactSupport_shiftForm2 {φ : FormDu d → ℝ} {y : FormDu d}
    {Ψ : FormDu d → FormSpace2 d} (hΨ : HasCompactSupport Ψ) :
    HasCompactSupport (shiftForm2 φ y Ψ) :=
  (hΨ.comp_homeomorph (Homeomorph.addRight y)).smul_left
    (f := fun z : FormDu d => covShift φ y z)

/-- **Covariant translation invariance of `ϑ₂ = dbarAdjoint2`.** -/
theorem dbarAdjoint2_shiftForm2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ψ : FormDu d → FormSpace2 d} (hΨ : ∀ i, ContDiff ℝ ∞ (fun z => Ψ z i))
    (y z : FormDu d) (j : Fin d) :
    dbarAdjoint2 φ (toFormFun2 (shiftForm2 φ y Ψ)) z j
      = covShift φ y z * dbarAdjoint2 φ (toFormFun2 Ψ) (z + y) j := by
  have hcd : DifferentiableAt ℝ (fun w : FormDu d => covShift φ y w) z := by
    have h : ContDiff ℝ 2 (fun w : FormDu d => covShift φ y w) := by
      unfold covShift
      exact Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp hφ).sub
          ((Complex.ofRealCLM.contDiff.comp hφ).comp (contDiff_id.add contDiff_const)))
    exact h.differentiable (by norm_num) z
  have hΔd : ∀ k : Fin d,
      DifferentiableAt ℝ (fun w : FormDu d =>
        toFormFun2 Ψ (w + y) (j, k) - toFormFun2 Ψ (w + y) (k, j)) z := by
    intro k
    have h1 : ContDiff ℝ 1 (fun w : FormDu d =>
        toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) :=
      ((hΨ (j, k)).of_le (by simp)).sub ((hΨ (k, j)).of_le (by simp))
    exact (h1.comp (contDiff_id.add contDiff_const)).differentiable (by norm_num) z
  have hkey : ∀ k : Fin d,
      (partialZ k (fun w => toFormFun2 (shiftForm2 φ y Ψ) w (j, k)
            - toFormFun2 (shiftForm2 φ y Ψ) w (k, j)) z
          - (toFormFun2 (shiftForm2 φ y Ψ) z (j, k)
              - toFormFun2 (shiftForm2 φ y Ψ) z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z)
        = covShift φ y z
          * (partialZ k (fun w => toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) (z + y)
              - (toFormFun2 Ψ (z + y) (j, k) - toFormFun2 Ψ (z + y) (k, j))
                * partialZ k (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
    intro k
    have hfun : (fun w => toFormFun2 (shiftForm2 φ y Ψ) w (j, k)
          - toFormFun2 (shiftForm2 φ y Ψ) w (k, j))
        = fun w => covShift φ y w
            * (toFormFun2 Ψ (w + y) (j, k) - toFormFun2 Ψ (w + y) (k, j)) := by
      funext w
      simp only [toFormFun2_shiftForm2]
      ring
    have hval : toFormFun2 (shiftForm2 φ y Ψ) z (j, k)
          - toFormFun2 (shiftForm2 φ y Ψ) z (k, j)
        = covShift φ y z * (toFormFun2 Ψ (z + y) (j, k) - toFormFun2 Ψ (z + y) (k, j)) := by
      simp only [toFormFun2_shiftForm2]
      ring
    have hP : partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
        - partialZ k (fun w => ((φ w : ℝ) : ℂ)) (z + y)
        = partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
          - partialZ k (fun w => ((φ w : ℝ) : ℂ)) (z + y) := rfl
    have hcomp : partialZ k (fun w : FormDu d =>
          toFormFun2 Ψ (w + y) (j, k) - toFormFun2 Ψ (w + y) (k, j)) z
        = partialZ k (fun w => toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) (z + y) :=
      partialZ_comp_add k (fun w => toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) y z
    rw [hfun, partialZ_mul hcd (hΔd k), partialZ_covShift hφ (y := y) (z := z) k, hcomp, hval]
    ring
  have hsum : dbarAdjoint2 φ (toFormFun2 (shiftForm2 φ y Ψ)) z j
      = - (∑ k : Fin d, covShift φ y z
          * (partialZ k (fun w => toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) (z + y)
              - (toFormFun2 Ψ (z + y) (j, k) - toFormFun2 Ψ (z + y) (k, j))
                * partialZ k (fun w => ((φ w : ℝ) : ℂ)) (z + y))) := by
    rw [dbarAdjoint2]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hkey k
  rw [hsum, dbarAdjoint2, mul_neg, Finset.mul_sum]

end Submission.FUP
