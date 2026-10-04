import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the slice derivative

If `A : ℝ × E → ℝ` is `C^∞` at `(t, y)`, then the partial derivative in the first variable
`y' ↦ ∂_t A (t, y')` is again `C^∞` at `y`.

This is the `k = 0` instance of the fact that the `t`-jet of a smooth function of `(t, y)` depends
smoothly on `y`; it is the base case of the Clairaut/commutation machinery of area `EXT`
(compare `Work.Diff.EXT.slice_tDeriv_commute`), where `A` is the chart expression of the curvature
tensor along a Ricci flow.

The proof is the parametric Fréchet derivative lemma `ContDiffAt.fderiv` (the derivative of a
smooth family `s ↦ A (s, y')` depends smoothly on the parameter `y'`), followed by the
identification `(fderiv ℝ f t) 1 = deriv f t`.
-/

namespace Work.Diff.EXT.ConnCov

/-- Auxiliary form: if `A` is smooth at `(t, y)` then also `y' ↦ fderiv ℝ (fun s => A (s, y')) t`
is smooth at `y`. -/
theorem contDiffAt_fderiv_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A (t, y)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => fderiv ℝ (fun s : ℝ => A (s, y')) t) y := by
  -- swap the two variables: `(y', s) ↦ A (s, y')` is smooth at `(y, t)`
  have hclm : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : E × ℝ => (p.2, p.1)) (y, t) := by fun_prop
  have hswap : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : E × ℝ => A (p.2, p.1)) (y, t) :=
    hA.comp (y, t) hclm
  -- parametric Fréchet derivative: differentiate `s ↦ A (s, y')` with respect to `s` at `t`
  refine ContDiffAt.fderiv (n := (⊤ : ℕ∞)) (f := fun (y' : E) (s : ℝ) => A (s, y'))
    (g := fun _ : E => t) ?_ ?_ ?_
  · exact hswap
  · exact contDiffAt_const
  · simp

theorem sliceDeriv_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A (t, y)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => deriv (fun s : ℝ => A (s, y')) t) y := by
  have hd := contDiffAt_fderiv_slice hA
  -- evaluate the derivative at `1 : ℝ` to turn `fderiv` into `deriv`
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => (fderiv ℝ (fun s : ℝ => A (s, y')) t) (1 : ℝ)) y :=
    hd.clm_apply contDiffAt_const
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards with y'
  exact (fderiv_apply_one_eq_deriv).symm

end Work.Diff.EXT.ConnCov
