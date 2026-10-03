import Mathlib

namespace Work.KMTAreas.A7

/-- The derivative of the section `y ↦ f (y, c)` at `x` is the Fréchet derivative of `f` at
`(x, c)` applied to the first basis vector `(1, 0)`. -/
lemma deriv_section_eq_fderiv (f : ℝ × ℝ → ℂ) (x c : ℝ) (hf : DifferentiableAt ℝ f (x, c)) :
    deriv (fun y : ℝ => f (y, c)) x = fderiv ℝ f (x, c) (1, 0) := by
  have hg : HasDerivAt (fun y : ℝ => (y, c)) (1, 0) x :=
    (hasDerivAt_id' (x := x)).prodMk (hasDerivAt_const (x := x) (c := c))
  have hl : HasFDerivAt f (fderiv ℝ f (x, c)) (x, c) := hf.hasFDerivAt
  have hcomp : HasDerivAt (fun y : ℝ => f (y, c)) (fderiv ℝ f (x, c) (1, 0)) x :=
    HasFDerivAt.comp_hasDerivAt_of_eq (f := fun y : ℝ => (y, c)) (y := (x, c)) x hl hg rfl
  exact hcomp.deriv

/-- The previous identity as an equality of functions of the first variable. -/
lemma deriv_section_eq (f : ℝ × ℝ → ℂ) (hf : Differentiable ℝ f) (c : ℝ) :
    deriv (fun y : ℝ => f (y, c)) = fun y => fderiv ℝ f (y, c) (1, 0) := by
  funext x
  exact deriv_section_eq_fderiv f x c (hf (x, c))

/-- Differentiating a `C^{n+1}` function of two variables in the first variable gives a `C^n`
function. -/
lemma contDiff_secD {n : ℕ} {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (fun p : ℝ × ℝ => fderiv ℝ f p (1, 0)) := by
  have h1 : ContDiff ℝ n (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (fderiv ℝ f q.1 : (ℝ × ℝ) →L[ℝ] ℂ) q.2) :=
    hf.contDiff_fderiv_apply (m := n) (by simp)
  have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => (p, ((1, 0) : ℝ × ℝ))) :=
    contDiff_id.prodMk contDiff_const
  exact h1.comp h2

theorem continuous_iteratedDeriv_two_section (Ψ : ℝ × ℝ → ℂ) (h : ContDiff ℝ 2 Ψ) :
    Continuous fun p : ℝ × ℝ => iteratedDeriv 2 (fun y : ℝ => Ψ (y, p.2)) p.1 := by
  have hΨ : Differentiable ℝ Ψ := h.differentiable (by norm_num)
  have hsec : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ Ψ p (1, 0)) :=
    contDiff_secD (n := 1) h
  have hsecD : Differentiable ℝ (fun p : ℝ × ℝ => fderiv ℝ Ψ p (1, 0)) :=
    hsec.differentiable (by norm_num)
  have hcont : Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ Ψ q (1, 0)) p (1, 0)) :=
    contDiff_zero.mp (contDiff_secD (n := 0) hsec)
  refine hcont.congr fun p => ?_
  have h1 : deriv (fun y : ℝ => Ψ (y, p.2)) = fun y => fderiv ℝ Ψ (y, p.2) (1, 0) :=
    deriv_section_eq Ψ hΨ p.2
  have h2 : deriv (fun y : ℝ => fderiv ℝ Ψ (y, p.2) (1, 0)) =
      fun y => fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ Ψ q (1, 0)) (y, p.2) (1, 0) := by
    simpa only [] using
      deriv_section_eq (fun q : ℝ × ℝ => fderiv ℝ Ψ q (1, 0)) hsecD p.2
  have h3 : iteratedDeriv 2 (fun y : ℝ => Ψ (y, p.2)) p.1 =
      deriv (fun y : ℝ => fderiv ℝ Ψ (y, p.2) (1, 0)) p.1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, h1]
  rw [h3, h2]

end Work.KMTAreas.A7
