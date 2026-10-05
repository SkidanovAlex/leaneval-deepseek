import Mathlib
import Submission.Work.RPV.Defs

/-!
# Smoothness of the chord map `chordPS`

`Work.RPV.chordPS z w a` reads, in coordinates,
`(((e^{-ia}(z+w)/√2).im, a), ((e^{-ia}(z+w)/√2).re, (‖z‖²+‖w‖²)/2 - 1))`.

Since the closed-form right hand side is built from `cexp`, the real/imaginary parts
(real-linear maps `reCLM`, `imCLM`), the embedding `ℝ ↪ ℂ` (`ofRealCLM`) and the
polynomial `‖z‖² = z.re*z.re + z.im*z.im`, it is `ContDiff ℝ n` for every `n`
(real-analytic, in fact).  We teach `fun_prop` about the three missing pieces
(real part, imaginary part and the real embedding) and reduce `‖·‖²` to the
polynomial expression via `Complex.sq_norm`.
-/

namespace Work.RPB.B5

open Complex
open scoped ContDiff

set_option autoImplicit false

/-- `fun_prop` rule: the real part of a `ContDiff` complex-valued function is `ContDiff`. -/
@[fun_prop] theorem contDiff_re_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ∞} {f : E → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => (f x).re :=
  Complex.reCLM.contDiff.comp hf

/-- `fun_prop` rule: the imaginary part of a `ContDiff` complex-valued function is
`ContDiff`. -/
@[fun_prop] theorem contDiff_im_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ∞} {f : E → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => (f x).im :=
  Complex.imCLM.contDiff.comp hf

/-- `fun_prop` rule: `ℝ ↪ ℂ` composed with a `ContDiff` real-valued function is `ContDiff`. -/
@[fun_prop] theorem contDiff_ofReal_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x => ((f x : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem chordPS_contDiff (n : ℕ∞) :
    ContDiff ℝ n (fun v : ℂ × (ℂ × ℝ) => Work.RPV.chordPS v.1 v.2.1 v.2.2) := by
  simp only [Work.RPV.chordPS, Complex.sq_norm, Complex.normSq_apply]
  fun_prop

end Work.RPB.B5
