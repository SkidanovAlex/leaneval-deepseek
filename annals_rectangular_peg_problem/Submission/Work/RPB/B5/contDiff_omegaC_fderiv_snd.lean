import Mathlib
import Submission.Work.RPB.B4.flux_two_point

/-!
# `ωC (Φ z) (∂₂Φ z)` is `C¹` when `Φ` is `C²`

The symplectic form `Work.RPV.ωC a b = Im (conj a * b) = a.re * b.im - a.im * b.re` on `ℂ`
is `ℝ`-bilinear, hence `C^∞` as a map `ℂ × ℂ → ℝ`; composing it with two `C^n` functions is
`C^n` (`contDiff_omegaC_comp`).  Applying this to `Φ : ℝ × ℝ → ℂ` (which is `C²`, hence `C¹`)
and to `z ↦ fderiv ℝ Φ z (0,1)` (a continuous linear functional evaluated on the `C¹` map
`fderiv ℝ Φ`, using `ContDiff.fderiv_right` and `ContDiff.clm_apply`) yields that the
"verical derivative paired against `Φ`" is `C¹`.
-/

namespace Work.RPB.B5

open scoped ContDiff

/-- `ωC` preserves smoothness: composing the `ℝ`-bilinear form `ωC` with two `ContDiff`
functions of the same regularity is again `ContDiff` of that regularity. -/
theorem contDiff_omegaC_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {f g : X → ℂ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => Work.RPV.ωC (f x) (g x)) := by
  rw [show (fun x => Work.RPV.ωC (f x) (g x))
        = fun x => (f x).re * (g x).im - (f x).im * (g x).re by
      funext x
      simp only [Work.RPV.ωC, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring]
  exact (((Complex.reCLM.contDiff).comp hf).mul ((Complex.imCLM.contDiff).comp hg)).sub
    (((Complex.imCLM.contDiff).comp hf).mul ((Complex.reCLM.contDiff).comp hg))

theorem contDiff_omegaC_fderiv_snd {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 2 Φ) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => Work.RPV.ωC (Φ z) (fderiv ℝ Φ z (0, 1))) := by
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hd : ContDiff ℝ 1 (fun z : ℝ × ℝ => fderiv ℝ Φ z (0, 1)) :=
    hfderiv.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)))
  exact contDiff_omegaC_comp (hΦ.of_le (by norm_num)) hd

end Work.RPB.B5
