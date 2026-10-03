import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

namespace Work.KMTPlan.A6

/-- The derivative of the "slice" `t ↦ (t, c)` is the constant vector `(1, 0)`. -/
lemma deriv_slice_mk_left_one_zero (c x : ℝ) :
    deriv (fun t : ℝ => (t, c)) x = ((1 : ℝ), (0 : ℝ)) := by
  have h : HasDerivAt (fun t : ℝ => (t, c)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x c)
  exact h.deriv

/-- The first partial derivative of a `C^{m+1}` function of two real variables is `C^m`.

`dp1 1 Φ x y` is the derivative of the one-variable slice `t ↦ Φ t y` at `x`; writing
`Ψ x y = Φ x y` as a function on `ℝ × ℝ`, this is the Fréchet derivative of `Ψ` at `(x,y)`
applied to `(1, 0)`.  `ContDiff.fderiv_apply` makes `(x,y) ↦ fderiv ℝ Ψ (x,y) (1,0)` `C^m` as
soon as `Ψ` is `C^{m+1}` (the two argument functions `x ↦ x` and `x ↦ (1,0)` are even `C^∞`),
and the chain rule `fderiv_comp_deriv` identifies the two expressions. -/
theorem SymToolbox_dp1_one_contDiff (Φ : ℝ → ℝ → ℂ) (m : ℕ)
    (hsm : ContDiff ℝ (m + 1) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ContDiff ℝ m (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp1 1 Φ p.1 p.2) := by
  have hgoal : (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp1 1 Φ p.1 p.2)
      = fun p : ℝ × ℝ => deriv (fun t : ℝ => Φ t p.2) p.1 := by
    funext p
    simp [dp1, iteratedDeriv_one]
  rw [hgoal]
  set Ψ : ℝ × ℝ → ℂ := fun p => Φ p.1 p.2 with hΨdef
  have hΨ : ContDiff ℝ (m + 1) Ψ := hsm
  have hf : ContDiff ℝ (m + 1) (Function.uncurry (fun (_ : ℝ × ℝ) => Ψ)) :=
    hΨ.comp contDiff_snd
  have hmain : ContDiff ℝ m (fun p : ℝ × ℝ => fderiv ℝ Ψ p ((1 : ℝ), (0 : ℝ))) :=
    hf.fderiv_apply (g := fun x : ℝ × ℝ => x) (k := fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))
      contDiff_id contDiff_const (le_refl _)
  have hfun : (fun p : ℝ × ℝ => deriv (fun t : ℝ => Φ t p.2) p.1)
      = fun p : ℝ × ℝ => fderiv ℝ Ψ p ((1 : ℝ), (0 : ℝ)) := by
    funext p
    have hd : deriv (fun t : ℝ => (t, p.2)) p.1 = ((1 : ℝ), (0 : ℝ)) :=
      deriv_slice_mk_left_one_zero p.2 p.1
    have hdiffslice : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
      (hasFDerivAt_prodMk_left p.1 p.2).differentiableAt
    have hdiffΨ : DifferentiableAt ℝ Ψ p :=
      (ContDiff.differentiable hΨ (by simp)).differentiableAt
    have h := fderiv_comp_deriv (l := Ψ) (f := fun t : ℝ => (t, p.2)) (x := p.1)
      hdiffΨ hdiffslice
    rw [hd] at h
    have heq : (Ψ ∘ fun t : ℝ => (t, p.2)) = fun t : ℝ => Φ t p.2 := rfl
    rw [heq] at h
    exact h
  rw [hfun]
  exact hmain

end Work.KMTPlan.A6
