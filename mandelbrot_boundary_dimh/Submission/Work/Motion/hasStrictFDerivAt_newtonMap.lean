import Mathlib
import Submission.Work.Motion.pertSetup

namespace Work.Motion

namespace Pert

/-- The iterate polynomial `(c,x) ↦ (Tc c)^[n] x` is smooth (indeed analytic) over `ℂ`.
This is the complex counterpart of `Pert.contDiff_TcIter`, needed to obtain strict
differentiability of the iterate from `ContDiff.hasStrictFDerivAt`. -/
theorem contDiff_TcIter_complex (n : ℕ) : ContDiff ℂ ⊤ (TcIter n) := by
  induction n with
  | zero => simpa using (contDiff_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ) (n := ⊤))
  | succ n ih =>
    have hF : ContDiff ℂ ⊤ (fun r : ℂ × ℂ => r.2 ^ 2 + r.1) :=
      ((contDiff_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ) (n := ⊤)).pow 2).add
        (contDiff_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ) (n := ⊤))
    have hJ : ContDiff ℂ ⊤ (fun q : ℂ × ℂ => (q.1, TcIter n q)) :=
      (contDiff_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ) (n := ⊤)).prodMk ih
    have heq : TcIter (n + 1) =
        (fun r : ℂ × ℂ => r.2 ^ 2 + r.1) ∘ (fun q : ℂ × ℂ => (q.1, TcIter n q)) := by
      funext q
      simp [TcIter_succ_apply, LeanEval.Dynamics.MandelbrotBoundary.Tc]
    rw [heq]
    exact hF.comp hJ

end Pert

open Set Metric Filter in
/-- The Newton "residual" `p ↦ (Tc p.1.1)^[m] (τ p.1.2 + p.2) - p.1.2` is strictly differentiable
at `u` (with derivative `fderiv`), whenever `τ` is differentiable in a neighbourhood of `u.1.2`. -/
theorem hasStrictFDerivAt_newtonMap {τ : ℂ → ℂ} {m : ℕ} {u : (ℂ × ℂ) × ℂ}
    (hτ : ∀ᶠ z in nhds u.1.2, DifferentiableAt ℂ τ z) :
    HasStrictFDerivAt
      (fun p : (ℂ × ℂ) × ℂ => Work.Motion.Pert.TcIter m (p.1.1, τ p.1.2 + p.2) - p.1.2)
      (fderiv ℂ (fun p : (ℂ × ℂ) × ℂ => Work.Motion.Pert.TcIter m (p.1.1, τ p.1.2 + p.2) - p.1.2) u)
      u := by
  -- `τ`, differentiable near `u.1.2`, is complex analytic there, hence strictly differentiable.
  have hτs : HasStrictFDerivAt τ (fderiv ℂ τ u.1.2) u.1.2 :=
    (Complex.analyticAt_iff_eventually_differentiableAt.mpr hτ).hasStrictFDerivAt
  -- the second coordinate projection `p ↦ p.1.2` of the parameter space
  have hS : HasStrictFDerivAt (fun p : (ℂ × ℂ) × ℂ => p.1.2)
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)) u :=
    hasStrictFDerivAt_snd.comp u hasStrictFDerivAt_fst
  -- `p ↦ τ p.1.2`
  have hτ2 : HasStrictFDerivAt (fun p : (ℂ × ℂ) × ℂ => τ p.1.2)
      ((fderiv ℂ τ u.1.2).comp
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ))) u :=
    hτs.comp u hS
  -- the third coordinate `p ↦ p.2`
  have hP : HasStrictFDerivAt (fun p : (ℂ × ℂ) × ℂ => p.2)
      (ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ) u :=
    hasStrictFDerivAt_snd
  -- the inner argument `p ↦ τ p.1.2 + p.2`
  have hsum : HasStrictFDerivAt (fun p : (ℂ × ℂ) × ℂ => τ p.1.2 + p.2)
      ((fderiv ℂ τ u.1.2).comp
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ))
        + ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ) u :=
    hτ2.add hP
  -- the first coordinate `p ↦ p.1.1`
  have hP1 : HasStrictFDerivAt (fun p : (ℂ × ℂ) × ℂ => p.1.1)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)) u :=
    hasStrictFDerivAt_fst.comp u hasStrictFDerivAt_fst
  -- the pair map `p ↦ (p.1.1, τ p.1.2 + p.2)`
  have hJ : HasStrictFDerivAt (fun p : (ℂ × ℂ) × ℂ => (p.1.1, τ p.1.2 + p.2))
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)).prod
        ((fderiv ℂ τ u.1.2).comp
          ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ))
          + ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ)) u :=
    hP1.prodMk hsum
  -- the iterate is smooth, hence strictly differentiable
  have hG : HasStrictFDerivAt (Work.Motion.Pert.TcIter m)
      (fderiv ℂ (Work.Motion.Pert.TcIter m) (u.1.1, τ u.1.2 + u.2))
      (u.1.1, τ u.1.2 + u.2) :=
    (Pert.contDiff_TcIter_complex m).hasStrictFDerivAt (by simp)
  have hcomp := hG.comp u hJ
  -- remove the `- p.1.2` term
  have hres := hcomp.sub hS
  convert hres using 1
  exact hres.hasFDerivAt.fderiv

end Work.Motion
