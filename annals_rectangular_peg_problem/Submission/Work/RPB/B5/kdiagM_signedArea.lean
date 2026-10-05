import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs

/-!
# `kdiagM_signedArea`: the real-linear normalisation scales the signed area by `g`

Node B5 normalises the glued family by the *real-linear* map
`kdiagM g : (x, y) ↦ (x, g · y)` of `ℂ ≅ ℝ²` (see `Submission.Work.RPB.B5.kappaDefs`).
Its determinant is `g`, so it multiplies the signed area `(1/2) ∮ ω_ℂ(c, c')` by `g`:

`signedArea (t ↦ kdiagM g (c t)) = g * signedArea c`,  for **every** `g : ℝ` and **every**
`c : ℝ → ℂ` (no regularity is assumed).

Two ingredients.

* **The area form.**  `ω_ℂ (kdiagM g z) (kdiagM g w) = g * ω_ℂ z w`: in coordinates `kdiagM g`
  acts on `z = x + iy` by `(x, y) ↦ (x, g y)`, and `ω_ℂ a b = a.re * b.im - a.im * b.re`, so
  both coordinates are simply multiplied by `g`.

* **The chain rule, hypothesis-free.**  The curve is arbitrary, so at a point where `c` fails to
  be differentiable `deriv` returns `0` for *both* curves — but only because `kdiagM g` is a
  linear *section*: it has the left inverse `kdiagM g⁻¹` when `g ≠ 0`.  In general (for a
  continuous linear map `L` with a left inverse `M`) we prove
  `deriv (L ∘ c) t = L (deriv c t)` by splitting on differentiability of `c`: if `c` is
  differentiable this is the chain rule; otherwise `L ∘ c` cannot be differentiable either,
  since `c = M ∘ (L ∘ c)` would then be differentiable, and both sides read `0`.

  The degenerate case `g = 0` is handled separately: `kdiagM 0 ∘ c` is the real-valued curve
  `t ↦ ((c t).re : ℂ)`, whose area integrand `ω_ℂ (d t) (deriv d t)` vanishes because `d` is
  real-valued (hence `deriv d` is real as well).  That is the lemma `signedArea_ofReal_zero`,
  proved by applying the same left-inverse chain rule to `Complex.ofRealCLM` (left inverse
  `Complex.reCLM`).
-/

namespace Work.RPB.B5

noncomputable section

/-! ## The algebra of `kdiagM` -/

/-- Component form of the area form: `ω_ℂ a b = a.re * b.im - a.im * b.re`. -/
private lemma kdiagM_omegaC_eq (a b : ℂ) :
    Work.RPV.ωC a b = a.re * b.im - a.im * b.re := by
  simp [Work.RPV.ωC, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The real part of `kdiagM g z` is the real part of `z`. -/
private lemma kdiagM_re (g : ℝ) (z : ℂ) : (kdiagM g z).re = z.re := by
  simp [kdiagM]

/-- The imaginary part of `kdiagM g z` is `g` times the imaginary part of `z`. -/
private lemma kdiagM_im (g : ℝ) (z : ℂ) : (kdiagM g z).im = g * z.im := by
  simp [kdiagM]

/-- `kdiagM g` scales the area form by `g`. -/
private lemma omegaC_kdiagM (g : ℝ) (z w : ℂ) :
    Work.RPV.ωC (kdiagM g z) (kdiagM g w) = g * Work.RPV.ωC z w := by
  rw [kdiagM_omegaC_eq, kdiagM_omegaC_eq, kdiagM_re, kdiagM_im, kdiagM_re, kdiagM_im]
  ring

/-- For `g ≠ 0`, `kdiagM g⁻¹` is a left inverse of `kdiagM g`. -/
private lemma kdiagM_left_inv (g : ℝ) (hg : g ≠ 0) (z : ℂ) : kdiagM g⁻¹ (kdiagM g z) = z := by
  apply Complex.ext
  · rw [kdiagM_re, kdiagM_re]
  · rw [kdiagM_im, kdiagM_im, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]

/-- `kdiagM g` as a continuous `ℝ`-linear map. -/
private def kdiagMCLM (g : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) + g • Complex.imCLM.smulRight Complex.I

/-- The continuous linear map `kdiagMCLM g` is the map `kdiagM g`. -/
private lemma kdiagMCLM_apply (g : ℝ) (z : ℂ) : kdiagMCLM g z = kdiagM g z := by
  rw [kdiagM]
  simp only [kdiagMCLM, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul]
  rw [Complex.ofReal_mul]
  ring

/-! ## The hypothesis-free chain rule for a linear section -/

/-- **Chain rule along a continuous linear map with a left inverse.**

If `L : E →L[ℝ] ℂ` has a left inverse `M` (`M (L z) = z`), then for every curve
`c : ℝ → E` and every `t`,
`deriv (L ∘ c) t = L (deriv c t)` — with no differentiability assumption on `c`.
At a point where `c` is not differentiable, `L ∘ c` is not differentiable either (otherwise
`c = M ∘ (L ∘ c)` would be), so both sides are `0`. -/
private lemma deriv_comp_clm_of_leftInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (M : ℂ →L[ℝ] E) (hML : ∀ z, M (L z) = z)
    (c : ℝ → E) (t : ℝ) :
    deriv (fun u => L (c u)) t = L (deriv c t) := by
  by_cases hc : DifferentiableAt ℝ c t
  · have h3 : HasFDerivAt (fun u => L (c u)) (L.comp (fderiv ℝ c t)) t :=
      L.hasFDerivAt.comp t hc.hasFDerivAt
    rw [h3.hasDerivAt.deriv, ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv]
  · have hc2 : ¬ DifferentiableAt ℝ (fun u => L (c u)) t := by
      intro h
      have hM : DifferentiableAt ℝ (fun u => M (L (c u))) t := M.differentiableAt.comp t h
      have hfun : (fun u => M (L (c u))) = c := by funext u; exact hML (c u)
      exact hc (hfun ▸ hM)
    rw [deriv_zero_of_not_differentiableAt hc2, deriv_zero_of_not_differentiableAt hc, map_zero]

/-- `deriv (fun u => kdiagM g (c u)) t = kdiagM g (deriv c t)` for `g ≠ 0`, with no
differentiability assumption. -/
private lemma deriv_kdiagM_comp (g : ℝ) (hg : g ≠ 0) (c : ℝ → ℂ) (t : ℝ) :
    deriv (fun u => kdiagM g (c u)) t = kdiagM g (deriv c t) := by
  have h := deriv_comp_clm_of_leftInverse (kdiagMCLM g) (kdiagMCLM g⁻¹) ?_ c t
  · simpa only [kdiagMCLM_apply] using h
  · intro z
    rw [kdiagMCLM_apply, kdiagMCLM_apply]
    exact kdiagM_left_inv g hg z

/-! ## Real-valued curves have vanishing signed area -/

/-- A curve of the shape `t ↦ ((u t : ℝ) : ℂ)` — i.e. a real-valued curve — has signed area `0`:
`ω_ℂ (d t) (deriv d t) = 0` because `d` and `deriv d` are both real. -/
private lemma signedArea_ofReal_zero (u : ℝ → ℝ) :
    Work.RPB.signedArea (fun t => ((u t : ℝ) : ℂ)) = 0 := by
  have hderiv : ∀ t, deriv (fun t => ((u t : ℝ) : ℂ)) t = ((deriv u t : ℝ) : ℂ) := by
    intro t
    have h := deriv_comp_clm_of_leftInverse Complex.ofRealCLM Complex.reCLM ?_ u t
    · simpa only [Complex.ofRealCLM_apply, Complex.reCLM_apply] using h
    · intro z
      simp
  have hpoint : (fun t => Work.RPV.ωC ((u t : ℝ) : ℂ)
      (deriv (fun t => ((u t : ℝ) : ℂ)) t)) = fun _ => (0 : ℝ) := by
    funext t
    rw [hderiv t, kdiagM_omegaC_eq]
    simp
  rw [Work.RPB.signedArea, hpoint, intervalIntegral.integral_zero, mul_zero]

/-! ## The main statement -/

theorem kdiagM_signedArea (g : ℝ) (c : ℝ → ℂ) :
    Work.RPB.signedArea (fun t => Work.RPB.B5.kdiagM g (c t))
      = g * Work.RPB.signedArea c := by
  by_cases hg : g = 0
  · -- degenerate case: `kdiagM 0` is the projection onto the real axis
    subst hg
    have hfun : (fun t => kdiagM 0 (c t)) = fun t => (((c t).re : ℝ) : ℂ) := by
      funext t; simp [kdiagM]
    rw [hfun, signedArea_ofReal_zero (fun t => (c t).re)]
    ring
  · -- generic case: pointwise chain rule plus the scaling of the area form
    have hderiv : ∀ t, deriv (fun u => kdiagM g (c u)) t = kdiagM g (deriv c t) :=
      fun t => deriv_kdiagM_comp g hg c t
    have hfun : (fun t => Work.RPV.ωC (kdiagM g (c t))
        (deriv (fun u => kdiagM g (c u)) t)) = fun t => g * Work.RPV.ωC (c t) (deriv c t) := by
      funext t
      rw [hderiv t, omegaC_kdiagM]
    rw [Work.RPB.signedArea, Work.RPB.signedArea, hfun, intervalIntegral.integral_const_mul]
    ring

end

end Work.RPB.B5
