import Mathlib
import Submission.Work.Diff.STE.B3.iteratedFDeriv_fderiv_le_of_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

/-
ROUTE (no differentiability hypothesis is needed; both sides are *junk-free* identities of
`fderiv`s).

Notation: `pdX i g x = fderiv ℝ g x (Pi.single i 1)` and `pdVecX` its iterated version for an
arbitrary codomain (`Work.Diff.STE.B3.pdX`, `pdVecX`, in
`Submission/Work/Diff/STE/B3/iteratedFDeriv_fderiv_le_of_pdVec.lean`), where the two `rfl`-lemmas
`Work.Diff.STE.B3.pdVecX_eq_pdVec` (`pdVecX k l H = pdVec k l H` for `H : (Fin n → ℝ) → ℂ`) and
`Work.Diff.STE.B3.pdVecX_eq_pdRVec` (`pdVecX k l f = pdRVec k l f` for `f` real-valued) are proved.

1. **The one-step lemma**: for every `g : (Fin n → ℝ) → ℝ`, `i : Fin n`,
   `pdX i (fun y => ((g y : ℝ) : ℂ)) = fun x => ((pdX i g x : ℝ) : ℂ)`.
   Case split on `DifferentiableAt ℝ g x`:
   * differentiable: `fderiv ℝ (Complex.ofRealCLM ∘ g) x
     = Complex.ofRealCLM.comp (fderiv ℝ g x)` (`fderiv_comp`, `ContinuousLinearMap.differentiableAt`,
     `ContinuousLinearMap.fderiv`), then evaluate at `Pi.single i 1` and use
     `Complex.ofRealCLM_apply`.
   * not differentiable: `Complex.re : ℂ →L[ℝ] ℝ` satisfies `re ∘ ofRealCLM = id`, so
     `g = re ∘ (ofRealCLM ∘ g)`; hence `ofRealCLM ∘ g` is not differentiable at `x` either
     (otherwise `g` would be, by the chain rule).  Both `fderiv`s are `0`
     (`fderiv_zero_of_not_differentiableAt`) and both sides are `0`.
2. **Induction on the list**: `pdVecX k l (ofRealCLM ∘ f) = ofRealCLM ∘ pdVecX k l f` for every
   `k`/`l`, by `List`/`Fin` induction peeling `l 0` (the definitional recursion
   `pdVecX (k+1) l H = pdX (l 0) (pdVecX k (Fin.tail l) H)`, cf. the `hpd` identity used in
   `pdVec_congr_of_eventuallyEq`).
3. Rewrite with `pdVecX_eq_pdVec` and `pdVecX_eq_pdRVec`.

(A version of this statement already sits, unproved, in
`Submission/Work/Diff/STE/Lead/Gal/pdVec_ofReal_eq_pdRVec.lean`; do NOT import that module — its
declaration has the same *name* as this one.  Copy the proof into this file under this path.)
-/

open scoped ContDiff

/-- **The one-step lemma.**  Complexification commutes with the first partial derivative:
`∂ᵢ (↑g) = ↑(∂ᵢ g)`, with no differentiability hypothesis (both sides are `0` where `g` is not
differentiable). -/
lemma pd_ofReal {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pd i (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdR i g x : ℝ) : ℂ) := by
  funext x
  show (fderiv ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x) (Pi.single i 1)
    = ((fderiv ℝ g x) (Pi.single i 1) : ℂ)
  have hcomp : (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ g := by
    funext y; exact (Complex.ofRealCLM_apply (g y)).symm
  by_cases hg : DifferentiableAt ℝ g x
  · rw [hcomp]
    have h := (Complex.ofRealCLM.hasFDerivAt (x := g x)).comp x hg.hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  · have hg' : ¬ DifferentiableAt ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x := by
      intro h
      refine hg ?_
      have h2 := Complex.reCLM.differentiableAt.comp x h
      simpa [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using h2
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
    simp

/-- **The list induction.**  For every list of directions, the iterated partial derivative of the
complexification is the complexification of the iterated partial derivative. -/
lemma pdList_ofReal {n : ℕ} (l : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdList l (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRList l f x : ℝ) : ℂ) := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    show Work.Diff.STE.pd i (Work.Diff.STE.pdList rest (fun y => ((f y : ℝ) : ℂ)))
      = fun x => ((Work.Diff.STE.pdR i (Work.Diff.STE.pdRList rest f) x : ℝ) : ℂ)
    rw [ih]
    exact pd_ofReal i (Work.Diff.STE.pdRList rest f)

/-- **The `List.ofFn` form of the target.**  Both `pdVec`/`pdRVec` unfold definitionally to
`pdList`/`pdRList` of `List.ofFn γ`, so this is the statement above. -/
theorem ofRealPdVecDict_ofFn {n : ℕ} (m : ℕ) (γ : Fin m → Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRVec m γ f x : ℝ) : ℂ) :=
  pdList_ofReal (List.ofFn γ) f

theorem ofRealPdVecDict {n : ℕ} (m : ℕ) (γ : Fin m → Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRVec m γ f x : ℝ) : ℂ) :=
  ofRealPdVecDict_ofFn m γ f

end Work.Diff.STE.Lead.Gal
