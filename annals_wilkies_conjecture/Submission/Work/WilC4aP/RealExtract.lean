/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): the real extraction.

  From the complex Puiseux expansion of the complexified coefficients we extract the real
  branches: a branch that is complex-analytic at `0` is either real-valued near `0` (and then
  restricts to a real-analytic function) or has no real value on `(0, ε)`.
-/
import Submission.Work.WilC4aP.Props
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- The restriction of a function that is complex-analytic at `0` to the real axis is
real-analytic at `0`. -/
theorem analyticAt_real_of_complex {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℝ (fun x : ℝ => f (x : ℂ)) 0 := by
  have h := AnalyticAt.restrictScalars (𝕜 := ℝ) hf
  have h2 := h.compContinuousLinearMap (u := Complex.ofRealCLM) (x := 0)
  simpa [Function.comp_def, Complex.ofRealCLM_apply] using h2

/-- The imaginary part of a function that is complex-analytic at `0` is real-analytic at `0`. -/
lemma analyticAt_im_of_complex {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℝ (fun x : ℝ => (f (x : ℂ)).im) 0 :=
  AnalyticAt.comp (g := fun z : ℂ => z.im) (f := fun x : ℝ => f (x : ℂ)) (x := 0)
    (Complex.imCLM.analyticAt (f 0)) (analyticAt_real_of_complex hf)

/-- **Reality criterion.** A branch that is complex-analytic at `0` is either real-valued near
`0` or has no real value near `0` off the origin. -/
theorem reality_criterion {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    (∀ᶠ x : ℝ in 𝓝 0, (f (x : ℂ)).im = 0) ∨
      (∀ᶠ x : ℝ in 𝓝[≠] 0, (f (x : ℂ)).im ≠ 0) :=
  (analyticAt_im_of_complex hf).eventually_eq_zero_or_eventually_ne_zero

/-- The polynomial whose coefficient of `Y ^ j` is the complexified `c j`. -/
def polyOf {d : ℕ} (F : Fin d → ℂ → ℂ) : Polynomial (ℂ → ℂ) :=
  X ^ d + ∑ j : Fin d, C (F j) * X ^ (j : ℕ)

lemma Pz_polyOf {d : ℕ} (F : Fin d → ℂ → ℂ) (s : ℂ) :
    Pz (polyOf F) s = X ^ d + ∑ j : Fin d, C (F j s) * X ^ (j : ℕ) := by
  simp only [polyOf, Pz, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, evAt_apply]

end Work.WilC4aP
