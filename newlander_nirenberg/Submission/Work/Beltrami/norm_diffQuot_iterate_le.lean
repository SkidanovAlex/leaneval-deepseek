import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff

universe u

/-- The forward difference operator `Δ_h`, `(Δ_h f) x = f (x + h) - f x`. -/
private def fwdDiff {E : Type u} {F : Type u} [Add E] [Sub F] (h : E) : (E → F) → (E → F) :=
  fun f x => f (x + h) - f x

private lemma fwdDiff_apply {E : Type u} {F : Type u} [Add E] [Sub F] (h : E) (f : E → F)
    (x : E) : fwdDiff h f x = f (x + h) - f x := rfl

private lemma contDiff_fwdDiff {E : Type u} {F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {f : E → F}
    (hf : ContDiff ℝ n f) (h : E) : ContDiff ℝ n (fwdDiff h f) := by
  have h1 : ContDiff ℝ n (fun x : E => x + h) := contDiff_id.add contDiff_const
  exact (hf.comp h1).sub hf

/-- If `y ↦ A y` is a derivative of `f` everywhere, then `A (x + h) - A x` is a derivative of
`Δ_h f` at `x`. -/
private lemma hasFDerivAt_fwdDiff {E : Type u} {F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {A : E → (E →L[ℝ] F)} {h x : E} (hfA : ∀ y, HasFDerivAt f (A y) y) :
    HasFDerivAt (fwdDiff h f) (fwdDiff h A x) x := by
  have h1 : HasFDerivAt (fun y : E => f (y + h)) (A (x + h)) x :=
    (hasFDerivAt_comp_add_right h).mpr (hfA (x + h))
  exact h1.sub (hfA x)

/-- The `n`-th forward difference commutes with `fderiv`: the derivative of `Δ_h^n f` is
`Δ_h^n (fderiv ℝ f)`. -/
private lemma hasFDerivAt_fwdDiff_iterate (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type u}
      [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}, ContDiff ℝ (n + 1) f →
      ∀ (h x : E), HasFDerivAt (((fwdDiff h)^[n]) f) (((fwdDiff h)^[n]) (fderiv ℝ f) x) x := by
  induction n with
  | zero =>
    intro E _ _ F _ _ f hf h x
    simp only [Function.iterate_zero_apply]
    exact ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt
  | succ n ih =>
    intro E _ _ F _ _ f hf h x
    have hf1 : ContDiff ℝ (n + 1) f := hf.of_le (by simp)
    have hA : ∀ y : E,
        HasFDerivAt (((fwdDiff h)^[n]) f) (((fwdDiff h)^[n]) (fderiv ℝ f) y) y :=
      fun y => ih hf1 h y
    have hstep : HasFDerivAt (fwdDiff h (((fwdDiff h)^[n]) f))
        (fwdDiff h (((fwdDiff h)^[n]) (fderiv ℝ f)) x) x :=
      hasFDerivAt_fwdDiff hA
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hstep

/-- **The `N`-th forward difference is controlled by the `N`-th derivative.**  For a `C^N` map
`f` between real normed spaces whose `N`-th iterated derivative is bounded by `B`, the `N`-th
forward difference of `f` is bounded by `‖h‖^N * B`. -/
private theorem norm_fwdDiff_iterate_le (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type u}
      [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (B : ℝ), ContDiff ℝ n f →
      (∀ x : E, ‖iteratedFDeriv ℝ n f x‖ ≤ B) →
      ∀ (h x : E), ‖(((fwdDiff h)^[n]) f) x‖ ≤ ‖h‖ ^ n * B := by
  induction n with
  | zero =>
    intro E _ _ F _ _ f B hf hB h x
    simpa using hB x
  | succ n ih =>
    intro E _ _ F _ _ f B hf hB h x
    have hf' : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hB' : ∀ y : E, ‖iteratedFDeriv ℝ n (fderiv ℝ f) y‖ ≤ B := by
      intro y
      rw [norm_iteratedFDeriv_fderiv]
      exact hB y
    have hg : ∀ y : E, ‖(((fwdDiff h)^[n]) (fderiv ℝ f)) y‖ ≤ ‖h‖ ^ n * B :=
      ih (fderiv ℝ f) B hf' hB' h
    have hcomm : ∀ y : E, HasFDerivAt (((fwdDiff h)^[n]) f)
        ((((fwdDiff h)^[n]) (fderiv ℝ f)) y) y :=
      fun y => hasFDerivAt_fwdDiff_iterate n hf h y
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := (((fwdDiff h)^[n]) f)) (C := ‖h‖ ^ n * B) (s := segment ℝ x (x + h))
      (fun y _ => (hcomm y).differentiableAt)
      (fun y _ => by rw [(hcomm y).fderiv]; exact hg y)
      (convex_segment x (x + h)) (left_mem_segment ℝ x (x + h))
      (right_mem_segment ℝ x (x + h))
    rw [Function.iterate_succ_apply']
    refine le_trans hmvt ?_
    rw [add_sub_cancel_left]
    refine le_of_eq ?_
    rw [pow_succ]
    ring

/-- **The `N`-th forward difference of a `C^N` function is controlled by its `N`-th derivative.**
If `φ` is `N` times continuously differentiable and `‖iteratedFDeriv ℝ N φ‖` is bounded by `B`
everywhere, then `‖Δ_h^N φ x‖ ≤ ‖h‖^N * B` for all `h`, `x`.

For `N = 1` this is the mean value inequality; for general `N` it follows by induction, applying the
mean value inequality in the direction `h` to `Δ_h^{N-1} φ` and using that
`fderiv ℝ (Δ_h^{N-1} φ) = Δ_h^{N-1} (fderiv ℝ φ)`.  (For the induction one proves the analogous
statement for functions with values in a normed space.) -/
theorem norm_diffQuot_iterate_le {N : ℕ} {φ : ℂ → ℂ} {B : ℝ}
    (hφ : ContDiff ℝ N φ) (hB : ∀ x : ℂ, ‖iteratedFDeriv ℝ N φ x‖ ≤ B) :
    ∀ (h x : ℂ), ‖((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N] φ) x‖ ≤ ‖h‖ ^ N * B := by
  intro h x
  exact norm_fwdDiff_iterate_le N φ B hφ hB h x

end Work.Beltrami

