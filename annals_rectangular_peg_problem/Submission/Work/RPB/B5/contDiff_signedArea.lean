import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPA3.contDiff_param_intervalIntegral
import Submission.Work.RPA3.deriv_deriv_swap

/-!
# B5: smoothness of the signed area in the family parameter

`Work.RPB.B5.contDiff_signedArea`: if a two-parameter family of closed plane curves
`(σ, t) ↦ V σ t` is jointly `C^{k+1}` and `2π`-periodic in the curve parameter `t`, then the
signed area

  `σ ↦ signedArea (V σ) = (1/2) ∫_0^{2π} ω_ℂ (V σ t, ∂_t V σ t) dt`

is `C^k` in `σ`.

The proof is the composition of two facts.

* The integrand `(σ,t) ↦ ω_ℂ (V σ t, ∂_t V σ t)` is jointly `C^k`.  Indeed `∂_t V σ t` is the
  evaluation at `(0,1)` of the Fréchet derivative of the joint map `z ↦ V z.1 z.2`
  (`Work.RPA3.deriv_prodMk_right`), which is `C^k` because the joint map is `C^{k+1}`
  (`ContDiff.fderiv_right`); and `ω_ℂ` is smooth (`contDiff_omegaC`).
* A parametric interval integral of a jointly `C^k` family is `C^k`
  (`Work.RPA3.contDiff_param_intervalIntegral`).

The periodicity hypothesis is not needed for the statement: `deriv` of the slice is taken inside
the integrand, so no boundary term arises.  It is kept because it is part of the interface the
consumers of this lemma expect.
-/

open MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false

-- `hper` is part of the interface of the requested statement but is not needed for the proof.
set_option linter.unusedVariables false

noncomputable section

namespace Work.RPB.B5

/-- The symplectic form `ω_ℂ (a,b) = Im (conj a * b)` is smooth: for jointly `C^n` families
`f, g : E → ℂ` the function `x ↦ ω_ℂ (f x) (g x)` is `C^n`.

The form is the composition of the (real) linear conjugation `starRingEnd ℂ`, the product in `ℂ`
and the (real) linear map `Complex.imCLM`. -/
lemma contDiff_omegaC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {f g : E → ℂ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => Work.RPV.ωC (f x) (g x)) := by
  have hconj : ContDiff ℝ n (fun x => (starRingEnd ℂ) (f x)) := by
    have h := Complex.conjCLE.contDiff.comp hf
    convert h using 1
    ext x; simp [Complex.conjCLE]
  have hmul : ContDiff ℝ n (fun x => (starRingEnd ℂ) (f x) * g x) := hconj.mul hg
  have h := Complex.imCLM.contDiff.comp hmul
  convert h using 1
  ext x
  simp only [Function.comp_apply, Complex.imCLM_apply, Work.RPV.ωC]

/-- The `t`-derivative `∂_t V σ t` of a `C^{k+1}` joint family is the evaluation of the Fréchet
derivative of the curried joint map at `(0,1)`, hence `C^k` in `(σ,t)`. -/
lemma contDiff_sliceDeriv (V : ℝ → ℝ → ℂ) {k : ℕ}
    (hV : ContDiff ℝ (k + 1) (fun z : ℝ × ℝ => V z.1 z.2)) :
    ContDiff ℝ k (fun z : ℝ × ℝ => deriv (fun s => V z.1 s) z.2) := by
  let W : ℝ × ℝ → ℂ := fun z => V z.1 z.2
  have hW : ContDiff ℝ (k + 1) W := hV
  have hdiffW : Differentiable ℝ W := hW.differentiable (by simp)
  have hfd : ContDiff ℝ k (fderiv ℝ W) :=
    hW.fderiv_right (m := (k : WithTop ℕ∞)) (by norm_num)
  have hderivVal : ContDiff ℝ k (fun z : ℝ × ℝ => (fderiv ℝ W z) (0, 1)) :=
    hfd.clm_apply contDiff_const
  have heq : (fun z : ℝ × ℝ => deriv (fun s => V z.1 s) z.2)
      = fun z => (fderiv ℝ W z) (0, 1) := by
    funext z
    exact Work.RPA3.deriv_prodMk_right ((hdiffW z).hasFDerivAt)
  rw [heq]
  exact hderivVal

theorem contDiff_signedArea (V : ℝ → ℝ → ℂ) (k : ℕ) (hV : ContDiff ℝ (k + 1) (fun z : ℝ × ℝ => V z.1 z.2)) (hper : ∀ σ t, V σ (t + 2 * Real.pi) = V σ t) : ContDiff ℝ k (fun σ => Work.RPB.signedArea (fun t => V σ t)) := by
  have hWk : ContDiff ℝ k (fun z : ℝ × ℝ => V z.1 z.2) := hV.of_le (by norm_num)
  have hderivCont : ContDiff ℝ k (fun z : ℝ × ℝ => deriv (fun s => V z.1 s) z.2) :=
    contDiff_sliceDeriv V hV
  have hg : ContDiff ℝ k
      (fun z : ℝ × ℝ => Work.RPV.ωC (V z.1 z.2) (deriv (fun s => V z.1 s) z.2)) :=
    contDiff_omegaC hWk hderivCont
  have hint : ContDiff ℝ k
      (fun σ => ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V σ t) (deriv (fun s => V σ s) t)) :=
    Work.RPA3.contDiff_param_intervalIntegral (k : ℕ∞)
      (fun σ t => Work.RPV.ωC (V σ t) (deriv (fun s => V σ s) t)) hg 0 (2 * Real.pi)
  have h2 : ContDiff ℝ k
      (fun σ => (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V σ t) (deriv (fun s => V σ s) t)) :=
    ContDiff.const_smul (1 / 2 : ℝ) hint
  simpa only [Work.RPB.signedArea] using h2

end Work.RPB.B5
