import Mathlib
import Submission.Work.RPA3.contDiff_param_intervalIntegral

namespace Work.RPB.B4

open MeasureTheory
open scoped Interval

universe uX uE

/-- Smoothness of a parametric interval integral, in the argument order `f : ℝ → X → E`
(integration variable first).  This is `Work.RPA3.contDiff_param_intervalIntegral` (which is
stated for a parameter space and a codomain living in the *same* universe, a restriction forced by
the induction that proves it) preceded by an argument swap and followed by the `ULift` reduction
that bridges the universe gap. -/
private theorem key {E : Type uE} {X : Type uX} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ → X → E) (a b : ℝ) (n : ℕ)
    (hf : ContDiff ℝ n (fun z : ℝ × X => f z.1 z.2)) :
    ContDiff ℝ n (fun x : X => ∫ s in a..b, f s x) := by
  -- Push `X` and `E` into a common universe.
  let X' : Type (max uX uE) := ULift.{uE} X
  let E' : Type (max uX uE) := ULift.{uX} E
  let eX : X' ≃L[ℝ] X := ContinuousLinearEquiv.ulift
  let eE : E' ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  let g : X' → ℝ → E' := fun x' s => eE.symm (f s (eX x'))
  -- The lifted integrand is jointly `C^n`.
  have hgsm : ContDiff ℝ n (fun z : X' × ℝ => g z.1 z.2) := by
    show ContDiff ℝ n (fun z : X' × ℝ => eE.symm (f z.2 (eX z.1)))
    have hφ : ContDiff ℝ n (fun z : X' × ℝ => (z.2, eX z.1)) := by
      fun_prop
    exact (ContinuousLinearMap.contDiff (eE.symm : E →L[ℝ] E')).comp (hf.comp hφ)
  -- Apply the same-universe theorem.
  have hΦ : ContDiff ℝ n (fun x' : X' => ∫ s in a..b, g x' s) :=
    Work.RPA3.contDiff_param_intervalIntegral (n : ENat) g hgsm a b
  -- Push back along the `ULift` equivalences.
  have hfin : ContDiff ℝ n (fun x : X => eE (∫ s in a..b, g (eX.symm x) s)) :=
    (ContinuousLinearMap.contDiff (eE : E' →L[ℝ] E)).comp
      (hΦ.comp (ContinuousLinearEquiv.contDiff eX.symm))
  have hfun : (fun x : X => eE (∫ s in a..b, g (eX.symm x) s))
      = fun x : X => ∫ s in a..b, f s x := by
    funext x
    have hcomp : g (eX.symm x) = fun s => eE.symm (f s x) := by
      funext s
      simp only [g]
      rw [ContinuousLinearEquiv.apply_symm_apply]
    have hinter : (∫ s in a..b, g (eX.symm x) s) = eE.symm (∫ s in a..b, f s x) := by
      rw [hcomp]
      have hint : IntervalIntegrable (fun s : ℝ => f s x) volume a b :=
        ((hf.continuous.comp (continuous_id.prodMk continuous_const)) :
          Continuous (fun s : ℝ => f s x)).intervalIntegrable a b
      exact ContinuousLinearMap.intervalIntegral_comp_comm (eE.symm : E →L[ℝ] E') hint
    rw [hinter]
    exact eE.apply_symm_apply _
  rw [← hfun]
  exact hfin

theorem contDiff_parametric_integral {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ → X → E) (a b : ℝ) (n : ℕ)
    (hf : ContDiff ℝ n (fun z : ℝ × X => f z.1 z.2)) :
    ContDiff ℝ n (fun x : X => ∫ s in a..b, f s x) :=
  key f a b n hf

end Work.RPB.B4
