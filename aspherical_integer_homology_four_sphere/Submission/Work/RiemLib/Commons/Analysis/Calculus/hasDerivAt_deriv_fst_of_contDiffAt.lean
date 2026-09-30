import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Clairaut's theorem (Schwarz) in `deriv`/`HasDerivAt` form

For a curried function `f : ℝ → ℝ → F` whose uncurrying is `C²` at `(a, b)`, the
derivative at `a` of `s ↦ ∂_t f s b` is the derivative at `b` of `t ↦ ∂_s f a t`.
This is a `deriv`/`HasDerivAt` restatement of the symmetry of the second Fréchet
derivative (`ContDiffAt.isSymmSndFDerivAt`).
-/

open scoped ContDiff Topology
open Filter

namespace Commons.Analysis.Calculus

/-- For a differentiable two-variable function, the derivative of the second
partial application at a point is the second coordinate partial derivative. -/
private lemma deriv_snd_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × ℝ → F} {s b : ℝ} (hg : DifferentiableAt ℝ g (s, b)) :
    deriv (fun t => g (s, t)) b = fderiv ℝ g (s, b) (0, 1) := by
  have hφ : HasFDerivAt (fun t : ℝ => (s, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) b :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) s b
  have h := (hg.hasFDerivAt.comp b hφ).hasDerivAt
  have hh := h.deriv
  simp only [Function.comp_def] at hh
  rw [hh]
  simp

/-- For a differentiable two-variable function, the derivative of the first
partial application at a point is the first coordinate partial derivative. -/
private lemma deriv_fst_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × ℝ → F} {a t : ℝ} (hg : DifferentiableAt ℝ g (a, t)) :
    deriv (fun s => g (s, t)) a = fderiv ℝ g (a, t) (1, 0) := by
  have hφ : HasFDerivAt (fun s : ℝ => (s, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) a :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) a t
  have h := (hg.hasFDerivAt.comp a hφ).hasDerivAt
  have hh := h.deriv
  simp only [Function.comp_def] at hh
  rw [hh]
  simp

/-- Clairaut's theorem in `deriv` form, for an uncurried `C²` function. -/
private theorem key {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × ℝ → F} {a b : ℝ}
    (hf : ContDiffAt ℝ 2 g (a, b)) :
    HasDerivAt (fun s => deriv (fun t => g (s, t)) b)
      (deriv (fun t => deriv (fun s => g (s, t)) a) b) a := by
  have h1 : ContDiffAt ℝ 1 g (a, b) := hf.of_le (by norm_num)
  have hDg_cd : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hDg_diff : DifferentiableAt ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b) :=
    hDg_cd.differentiableAt (by simp)
  have hDg_has : HasFDerivAt (fun p : ℝ × ℝ => fderiv ℝ g p)
      (fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (a, b) :=
    hDg_diff.hasFDerivAt
  -- the derivative of `s ↦ (fderiv g (s,b)) (0,1)`
  have hL : HasDerivAt (fun s => (fderiv ℝ g (s, b)) (0, 1))
      ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (1, 0) (0, 1)) a := by
    have hφ : HasFDerivAt (fun s : ℝ => (s, b)) (ContinuousLinearMap.inl ℝ ℝ ℝ) a :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) a b
    have h1' : HasFDerivAt (fun s => fderiv ℝ g (s, b))
        ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)).comp
          (ContinuousLinearMap.inl ℝ ℝ ℝ)) a :=
      hDg_has.comp a hφ
    let L : ℝ →L[ℝ] F := (ContinuousLinearMap.apply ℝ F (0, 1)).comp
      ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ))
    have h2 : HasFDerivAt (fun s => (fderiv ℝ g (s, b)) (0, 1)) L a := by
      have := (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a h1'
      simpa [L, Function.comp_def] using this
    have h3 := h2.hasDerivAt
    convert h3 using 1
    simp [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hDev : ∀ᶠ s in 𝓝 a, DifferentiableAt ℝ g (s, b) := by
    have h1ev : ∀ᶠ p in 𝓝 (a, b), ContDiffAt ℝ 1 g p := h1.eventually (by simp)
    have hDeev : ∀ᶠ p in 𝓝 (a, b), DifferentiableAt ℝ g p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    have hφtend : Filter.Tendsto (fun s : ℝ => (s, b)) (𝓝 a) (𝓝 (a, b)) :=
      continuousAt_id.prodMk continuousAt_const
    exact hφtend.eventually hDeev
  have hEv : (fun s => deriv (fun t => g (s, t)) b) =ᶠ[𝓝 a]
      (fun s => (fderiv ℝ g (s, b)) (0, 1)) := by
    filter_upwards [hDev] with s hs
    exact deriv_snd_aux hs
  have hLHS : HasDerivAt (fun s => deriv (fun t => g (s, t)) b)
      ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (1, 0) (0, 1)) a :=
    hL.congr_of_eventuallyEq hEv
  -- the value of the right hand side
  have hR : HasDerivAt (fun t => (fderiv ℝ g (a, t)) (1, 0))
      ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (0, 1) (1, 0)) b := by
    have hφ : HasFDerivAt (fun t : ℝ => (a, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) b :=
      hasFDerivAt_prodMk_right (𝕜 := ℝ) a b
    have h1' : HasFDerivAt (fun t => fderiv ℝ g (a, t))
        ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ)) b :=
      hDg_has.comp b hφ
    let L : ℝ →L[ℝ] F := (ContinuousLinearMap.apply ℝ F (1, 0)).comp
      ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℝ))
    have h2 : HasFDerivAt (fun t => (fderiv ℝ g (a, t)) (1, 0)) L b := by
      have := (ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp b h1'
      simpa [L, Function.comp_def] using this
    have h3 := h2.hasDerivAt
    convert h3 using 1
    simp [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hDev' : ∀ᶠ t in 𝓝 b, DifferentiableAt ℝ g (a, t) := by
    have h1ev : ∀ᶠ p in 𝓝 (a, b), ContDiffAt ℝ 1 g p := h1.eventually (by simp)
    have hDeev : ∀ᶠ p in 𝓝 (a, b), DifferentiableAt ℝ g p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    have hφtend : Filter.Tendsto (fun t : ℝ => (a, t)) (𝓝 b) (𝓝 (a, b)) :=
      continuousAt_const.prodMk continuousAt_id
    exact hφtend.eventually hDeev
  have hEv' : (fun t => deriv (fun s => g (s, t)) a) =ᶠ[𝓝 b]
      (fun t => (fderiv ℝ g (a, t)) (1, 0)) := by
    filter_upwards [hDev'] with t ht
    exact deriv_fst_aux ht
  have hRHSfun : HasDerivAt (fun t => deriv (fun s => g (s, t)) a)
      ((fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (0, 1) (1, 0)) b :=
    hR.congr_of_eventuallyEq hEv'
  have hRHSval : deriv (fun t => deriv (fun s => g (s, t)) a) b
      = (fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (0, 1) (1, 0) :=
    hRHSfun.deriv
  -- symmetry of the second derivative
  have hsymm : IsSymmSndFDerivAt ℝ g (a, b) := hf.isSymmSndFDerivAt (by simp)
  have hsymm' : (fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (0, 1) (1, 0)
      = (fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ g p) (a, b)) (1, 0) (0, 1) := by
    have := hsymm.eq (0, 1) (1, 0)
    simpa using this
  rw [hRHSval, hsymm']
  exact hLHS

/-- **Clairaut's theorem (Schwarz), in `deriv`/`HasDerivAt` form.**  For a curried function
`f : ℝ → ℝ → F` whose uncurrying is `C²` at `(a, b)`, the derivative at `a` of
`s ↦ ∂_t f s b` is the derivative at `b` of `t ↦ ∂_s f a t`. -/
theorem hasDerivAt_deriv_fst_of_contDiffAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → ℝ → F} {a b : ℝ}
    (hf : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (a, b)) :
    HasDerivAt (fun s => deriv (f s) b)
      (deriv (fun t => deriv (fun s => f s t) a) b) a := by
  have h := key (g := fun p : ℝ × ℝ => f p.1 p.2) hf
  simpa using h

end Commons.Analysis.Calculus