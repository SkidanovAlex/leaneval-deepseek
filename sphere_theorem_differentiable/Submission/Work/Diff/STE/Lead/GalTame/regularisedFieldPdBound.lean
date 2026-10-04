import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-! ## The model map on `ℂ` and its derivative

The regularised field is the composite of the `ℂ`-valued field `w` with the *model* map

`Φ z = (‖z‖^2 + ε^2)^((p-2)/2) • conj z`,   `z : ℂ`,

and `‖z‖² + ε² > 0` everywhere, so `Φ` is (real-)differentiable at every point.  We first record
its derivative and then the pointwise norm bound that is the whole content of the estimate:

`‖(fderiv ℝ Φ z) u‖ ≤ (p-1) * (‖z‖²+ε²)^((p-2)/2) * ‖u‖`.

Writing `S = ‖z‖² + ε²`, `r = (p-2)/2`, the derivative of `Φ` at `z` in the direction `u` is

`(r * S^(r-1) * (2 * ⟪z,u⟫_ℝ)) • conj z + S^r • conj u`,

whose norm is at most `2r S^(r-1) ‖z‖² ‖u‖ + S^r ‖u‖ = S^(r-1) ((p-2)‖z‖² + S)‖u‖`, and
`(p-2)‖z‖² + S ≤ (p-1)S` because `S = ‖z‖² + ε²`. -/

private lemma hasFDerivAt_regFieldComplex (z : ℂ) (p : ℝ) (ε : ℝ) (hε : 0 < ε) :
    HasFDerivAt (fun ζ : ℂ => (‖ζ‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) ζ)
      (((‖z‖^2+ε^2)^((p-2)/2)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        + ((((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1)) • (2 • innerSL ℝ z))).smulRight ((starRingEnd ℂ) z)) z := by
  have hS : (0:ℝ) < ‖z‖^2 + ε^2 := by positivity
  have h1 : HasFDerivAt (fun ζ : ℂ => ‖ζ‖^2 + ε^2) (2 • innerSL ℝ z) z := by
    have h := (hasFDerivAt_id z).norm_sq
    simpa using h.add_const (ε^2)
  have h2 : HasFDerivAt (fun ζ : ℂ => (‖ζ‖^2 + ε^2)^((p-2)/2))
      (((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1)) • (2 • innerSL ℝ z)) z :=
    h1.rpow_const (Or.inl hS.ne')
  have h3 : HasFDerivAt (fun ζ : ℂ => (starRingEnd ℂ) ζ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z :=
    Complex.conjCLE.hasFDerivAt
  exact h2.smul h3

private lemma fderiv_regFieldComplex_apply_le (z u : ℂ) (p : ℝ) (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ‖(fderiv ℝ (fun ζ : ℂ => (‖ζ‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) ζ) z) u‖
      ≤ (p - 1) * ((‖z‖^2 + ε^2)^((p-2)/2)) * ‖u‖ := by
  have hS : (0:ℝ) < ‖z‖^2 + ε^2 := by positivity
  have hr : 0 ≤ (p-2)/2 := by linarith
  have hSn : 0 ≤ (‖z‖^2+ε^2)^((p-2)/2 - 1) := Real.rpow_nonneg hS.le _
  have hSp : 0 ≤ (‖z‖^2+ε^2)^((p-2)/2) := Real.rpow_nonneg hS.le _
  rw [(hasFDerivAt_regFieldComplex z p ε hε).fderiv]
  have hkey : ((((‖z‖^2+ε^2)^((p-2)/2)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        + (((((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1)) • (2 • innerSL ℝ z)))).smulRight ((starRingEnd ℂ) z)) u)
      = (‖z‖^2+ε^2)^((p-2)/2) • (starRingEnd ℂ) u
        + ((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * inner ℝ z u)) • (starRingEnd ℂ) z := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [show (Complex.conjCLE : ℂ →L[ℝ] ℂ) u = (starRingEnd ℂ) u from Complex.conjCLE_apply u]
    ring_nf
  rw [hkey]
  have hA : ‖(‖z‖^2+ε^2)^((p-2)/2) • (starRingEnd ℂ) u‖ ≤ (‖z‖^2+ε^2)^((p-2)/2) * ‖u‖ := by
    rw [norm_smul, Complex.norm_conj, Real.norm_eq_abs, abs_of_nonneg hSp]
  have hB : ‖((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * inner ℝ z u)) • (starRingEnd ℂ) z‖
      ≤ (2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * ‖z‖^2) * ‖u‖ := by
    rw [norm_smul, Complex.norm_conj, Real.norm_eq_abs]
    have habs : |(p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * inner ℝ z u)|
        = (p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * |inner ℝ z u|) := by
      simp only [abs_mul, abs_of_nonneg hr, abs_of_nonneg hSn,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [habs]
    have hA' : 0 ≤ (p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) := mul_nonneg hr hSn
    calc (p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * |inner ℝ z u|) * ‖z‖
        ≤ (p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * (‖z‖ * ‖u‖)) * ‖z‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
          apply mul_le_mul_of_nonneg_left _ hA'
          linarith [abs_real_inner_le_norm z u]
      _ = (2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * ‖z‖^2) * ‖u‖ := by ring
  have hstep : 2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * ‖z‖^2
      ≤ (p-2) * (‖z‖^2+ε^2)^((p-2)/2) := by
    have h1 : ‖z‖^2 ≤ ‖z‖^2 + ε^2 := le_add_of_nonneg_right (sq_nonneg ε)
    have h2 : 0 ≤ 2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) := by positivity
    have hSr : (‖z‖^2+ε^2)^((p-2)/2-1) * (‖z‖^2+ε^2) = (‖z‖^2+ε^2)^((p-2)/2) := by
      have h := Real.rpow_add hS ((p-2)/2 - 1) 1
      rw [Real.rpow_one] at h
      rw [← h]; congr 1; ring
    calc 2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * ‖z‖^2
        ≤ 2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * (‖z‖^2+ε^2) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (p-2) * ((‖z‖^2+ε^2)^((p-2)/2-1) * (‖z‖^2+ε^2)) := by ring
      _ = (p-2) * (‖z‖^2+ε^2)^((p-2)/2) := by rw [hSr]
  have hfin : (‖z‖^2+ε^2)^((p-2)/2) * ‖u‖
        + (2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * ‖z‖^2) * ‖u‖
      ≤ (p-1) * (‖z‖^2+ε^2)^((p-2)/2) * ‖u‖ := by
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
    have hid : (p-1) * (‖z‖^2+ε^2)^((p-2)/2)
        = (p-2) * (‖z‖^2+ε^2)^((p-2)/2) + (‖z‖^2+ε^2)^((p-2)/2) := by ring
    linarith [hstep, hid]
  calc ‖(‖z‖^2+ε^2)^((p-2)/2) • (starRingEnd ℂ) u
        + ((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * inner ℝ z u)) • (starRingEnd ℂ) z‖
      ≤ ‖(‖z‖^2+ε^2)^((p-2)/2) • (starRingEnd ℂ) u‖
        + ‖((p-2)/2 * (‖z‖^2+ε^2)^((p-2)/2-1) * (2 * inner ℝ z u)) • (starRingEnd ℂ) z‖ :=
        norm_add_le _ _
    _ ≤ (‖z‖^2+ε^2)^((p-2)/2) * ‖u‖
        + (2 * ((p-2)/2) * (‖z‖^2+ε^2)^((p-2)/2-1) * ‖z‖^2) * ‖u‖ := add_le_add hA hB
    _ ≤ (p-1) * (‖z‖^2+ε^2)^((p-2)/2) * ‖u‖ := hfin

/-- **Pointwise derivative bound for the `ε`-regularised field.**

For `p ≥ 2`, `ε > 0` and a `C^∞` field `w : (ι → ℝ) → ℂ`, the directional derivative along `eᵢ`
of the regularised field `y ↦ (‖w y‖² + ε²)^((p-2)/2) • conj (w y)` is bounded by
`(p-1) (‖w x‖² + ε²)^((p-2)/2) ‖∂ᵢ w x‖` at every point `x`.

This is the pointwise half of the `ε`-regularisation proof of the sharp periodic integration by
parts `∫_{cube} ‖∂ᵢ g‖^p ≤ (p-1) ∫_{cube} ‖g‖ ‖∂ᵢ g‖^{p-2} ‖∂ᵢ∂ᵢ g‖`; a proof of that statement
(which uses this lemma) is sketched in `Submission/Work/Diff/STE/GN/ibp_rpow_complex.lean` and the
statement above is exactly the goal stated there.  Note `‖w x‖² + ε² > 0`, so `t ↦ t^((p-2)/2)`
is smooth at the base point and the chain/product rule applies; the estimate uses
`‖conj (w x)‖ = ‖w x‖` and `(‖w x‖²+ε²)^((p-4)/2)‖w x‖² ≤ (‖w x‖²+ε²)^((p-2)/2)`. -/
theorem regularisedFieldPdBound {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (p : ℝ)
    (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (x : ι → ℝ) :
    ‖Work.Diff.STE.pd i
        (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2)) • (starRingEnd ℂ) (w y)) x‖
      ≤ (p - 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2)) * ‖Work.Diff.STE.pd i w x‖ := by
  have hFd : DifferentiableAt ℝ
      (fun z : ℂ => (‖z‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) z) (w x) :=
    (hasFDerivAt_regFieldComplex (w x) p ε hε).differentiableAt
  have hwd : DifferentiableAt ℝ w x := (hw.contDiffAt).differentiableAt (by simp)
  have hcomp : fderiv ℝ ((fun z : ℂ => (‖z‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) z) ∘ w) x
      = (fderiv ℝ (fun z : ℂ => (‖z‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) z) (w x)).comp
          (fderiv ℝ w x) :=
    fderiv_comp x hFd hwd
  have hpd : Work.Diff.STE.pd i
        (fun y : ι → ℝ => (‖w y‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) (w y)) x
      = (fderiv ℝ (fun z : ℂ => (‖z‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) z) (w x))
          (Work.Diff.STE.pd i w x) := by
    simp only [Work.Diff.STE.pd]
    have h1 : (fun y : ι → ℝ => (‖w y‖^2 + ε^2)^((p-2)/2) • (starRingEnd ℂ) (w y))
        = (fun z : ℂ => (‖z‖^2+ε^2)^((p-2)/2) • (starRingEnd ℂ) z) ∘ w := rfl
    rw [h1, hcomp, ContinuousLinearMap.comp_apply]
  rw [hpd]
  exact fderiv_regFieldComplex_apply_le (w x) (Work.Diff.STE.pd i w x) p hp ε hε

end Work.Diff.STE.Lead.GalTame
