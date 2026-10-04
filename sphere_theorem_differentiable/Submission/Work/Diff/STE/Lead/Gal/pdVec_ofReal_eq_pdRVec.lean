import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The complex partial derivatives of a real function are the complexifications of its
real partial derivatives

`Work.Diff.STE.pd i F x` is the directional derivative of `F : (ι → ℝ) → ℂ` at `x` along the
`i`-th coordinate direction, i.e. `fderiv ℝ F x (Pi.single i 1)`, and `Work.Diff.STE.pdR i G` is
the analogous object for a real valued `G`.  Likewise `pdVec`/`pdRVec` are the iterated versions
along a tuple of directions.

The lemma proved here says that these two constructions commute with the inclusion
`Complex.ofReal`: for a real valued `f`, differentiating the complexification of `f` is the same
as complexifying the derivative of `f`:

`pdVec i γ (fun y => ((f y : ℝ) : ℂ)) = fun x => ((pdRVec i γ f x : ℝ) : ℂ)`.

This is the "local, non-smooth" statement; in particular **no differentiability hypothesis** is
needed on `f`, because `fderiv` of a non-differentiable function is `0` (`fderiv_zero_of_not_
differentiableAt`), and `f` is differentiable at `x` exactly when its complexification is
(`ofRealCLM` is injective, `reCLM` is a left inverse).
-/

namespace Work.Diff.STE.Lead.Gal

open Work.Diff.STE

/-- The `fderiv` of the complexification of a real valued function, evaluated at a vector.

No differentiability hypothesis: if `g` is not differentiable at `x` then neither is its
complexification, so both sides vanish (via `fderiv_zero_of_not_differentiableAt`). -/
private lemma fderiv_ofReal_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (x v : E) :
    fderiv ℝ (fun y => ((g y : ℝ) : ℂ)) x v = ((fderiv ℝ g x v : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ g x
  · have hfd : fderiv ℝ (fun y => ((g y : ℝ) : ℂ)) x
        = Complex.ofRealCLM.comp (fderiv ℝ g x) := by
      have h' := (Complex.ofRealCLM.hasFDerivAt.comp x h.hasFDerivAt).fderiv
      have h2 : (fun y => ((g y : ℝ) : ℂ)) = (⇑Complex.ofRealCLM ∘ g) := rfl
      rw [h2]; exact h'
    rw [hfd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  · -- `g` is not differentiable at `x`, hence neither is its complexification
    have hf : fderiv ℝ g x = 0 := fderiv_zero_of_not_differentiableAt h
    have hnd : ¬ DifferentiableAt ℝ (fun y => ((g y : ℝ) : ℂ)) x := by
      intro hd
      have hg : DifferentiableAt ℝ (fun y => Complex.re ((g y : ℝ) : ℂ)) x :=
        Complex.reCLM.differentiableAt.comp x hd
      exact h (by simpa [Complex.ofReal_re] using hg)
    rw [hf, fderiv_zero_of_not_differentiableAt hnd]
    simp

/-- The one-step version of the target: `pd` of the complexification of a real function is the
complexification of `pdR`. -/
private lemma pd_ofReal_eq_pdR {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (g : (ι → ℝ) → ℝ) :
    pd i (fun y => ((g y : ℝ) : ℂ)) = fun x => ((pdR i g x : ℝ) : ℂ) := by
  funext x
  simp only [Work.Diff.STE.pd, Work.Diff.STE.pdR]
  exact fderiv_ofReal_eq (ι → ℝ) g x (Pi.single i 1)

/-- Iterating the one-step lemma along a list of directions. -/
private lemma pdList_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List ι) (g : (ι → ℝ) → ℝ) :
    pdList l (fun y => ((g y : ℝ) : ℂ)) = fun x => ((pdRList l g x : ℝ) : ℂ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change pd i (pdList l (fun y => ((g y : ℝ) : ℂ)))
      = fun x => ((pdR i (pdRList l g) x : ℝ) : ℂ)
    rw [ih]
    exact pd_ofReal_eq_pdR i (pdRList l g)

theorem pdVec_ofReal_eq_pdRVec {n : ℕ} (i : ℕ) (γ : Fin i → Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdVec i γ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRVec i γ f x : ℝ) : ℂ) :=
  pdList_ofReal (List.ofFn γ) f

end Work.Diff.STE.Lead.Gal
