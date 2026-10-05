import Mathlib
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.paramIntegral_contDiff_inf

/-!
# Smoothness of the divided chord `chordW` and its `τ`-derivative

If `c : ℝ → ℝ → ℂ` is jointly `C^∞` then so are

* `chordW c τ t r = ∫_{s ∈ [-1,1]} ∂_t c (τ, t + s r) ds`, viewed as a function of `(τ,t,r)`;
* its `τ`-derivative `chordWd c τ t r = ∂_τ chordW c τ t r`.

The proof is a three-step composition:

* the partial derivative `(τ, y) ↦ ∂_y c (τ, y)` of a jointly `C^∞` function is `C^∞`
  (`contDiff_deriv_snd'`);
* it is precomposed with the affine (hence smooth) substitution `(s,τ,t,r) ↦ (τ, t + s r)`;
* the parametric interval integral of a jointly `C^∞` family is `C^∞`
  (`Work.RPB.B2.paramIntegral_contDiff_inf`).

The `τ`-derivative is obtained from the same partial-derivative closure applied in the first
variable (`contDiff_deriv_fst'`).
-/

open Complex Real
open scoped ContDiff Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-- A partial derivative in the **second** coordinate of a jointly `C^∞` function is `C^∞`:
`(x, y) ↦ deriv (fun s => f (x, s)) y`.  This is the chain rule together with the fact that
`fderiv ℝ f` is `C^∞` and evaluation at a fixed vector preserves `C^∞`. -/
private theorem contDiff_deriv_snd' {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X × ℝ → E) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun z : X × ℝ => deriv (fun s : ℝ => f (z.1, s)) z.2) := by
  obtain ⟨hdiff, hfd⟩ := contDiff_infty_iff_fderiv.mp hf
  have hev : ContDiff ℝ ∞
      (fun z : X × ℝ => (fderiv ℝ f z) (ContinuousLinearMap.inr ℝ X ℝ (1 : ℝ))) :=
    hfd.clm_apply contDiff_const
  have hfun : (fun z : X × ℝ => deriv (fun s : ℝ => f (z.1, s)) z.2)
      = fun z : X × ℝ => (fderiv ℝ f z) (ContinuousLinearMap.inr ℝ X ℝ (1 : ℝ)) := by
    funext z
    have hd : HasFDerivAt f (fderiv ℝ f z) z :=
      hdiff.differentiableAt.hasFDerivAt
    have hg : HasDerivAt (fun s : ℝ => (z.1, s)) (ContinuousLinearMap.inr ℝ X ℝ (1 : ℝ)) z.2 :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2).hasDerivAt
    have hcomp := hd.comp_hasDerivAt z.2 hg
    simpa only [Function.comp_def, ContinuousLinearMap.inr_apply] using hcomp.deriv
  rw [hfun]
  exact hev

/-- A partial derivative in the **first** coordinate of a jointly `C^∞` function is `C^∞`:
`(x, y) ↦ deriv (fun s => f (s, y)) x`. -/
private theorem contDiff_deriv_fst' {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Y → E) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun z : ℝ × Y => deriv (fun s : ℝ => f (s, z.2)) z.1) := by
  obtain ⟨hdiff, hfd⟩ := contDiff_infty_iff_fderiv.mp hf
  have hev : ContDiff ℝ ∞
      (fun z : ℝ × Y => (fderiv ℝ f z) (ContinuousLinearMap.inl ℝ ℝ Y (1 : ℝ))) :=
    hfd.clm_apply contDiff_const
  have hfun : (fun z : ℝ × Y => deriv (fun s : ℝ => f (s, z.2)) z.1)
      = fun z : ℝ × Y => (fderiv ℝ f z) (ContinuousLinearMap.inl ℝ ℝ Y (1 : ℝ)) := by
    funext z
    have hd : HasFDerivAt f (fderiv ℝ f z) z :=
      hdiff.differentiableAt.hasFDerivAt
    have hg : HasDerivAt (fun s : ℝ => (s, z.2)) (ContinuousLinearMap.inl ℝ ℝ Y (1 : ℝ)) z.1 :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2).hasDerivAt
    have hcomp := hd.comp_hasDerivAt z.1 hg
    simpa only [Function.comp_def, ContinuousLinearMap.inl_apply] using hcomp.deriv
  rw [hfun]
  exact hev

theorem chordW_contDiff_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B2.chordW c z.1 z.2.1 z.2.2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B2.chordWd c z.1 z.2.1 z.2.2) := by
  -- `(τ, y) ↦ ∂_y c τ y` is jointly `C^∞`.
  have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => deriv (fun u => c z.1 u) z.2) :=
    contDiff_deriv_snd' (fun z : ℝ × ℝ => c z.1 z.2) hc
  -- the affine substitution `(s,τ,t,r) ↦ (τ, t + s r)`.
  have hPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × (ℝ × (ℝ × ℝ)) => (z.2.1, z.2.2.1 + z.1 * z.2.2.2)) := by fun_prop
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × (ℝ × (ℝ × ℝ)) => deriv (fun u => c z.2.1 u) (z.2.2.1 + z.1 * z.2.2.2)) :=
    hP.comp hPhi
  -- the parametric interval integral.
  have hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × (ℝ × ℝ) =>
        ∫ s in (-1 : ℝ)..1, deriv (fun u => c x.1 u) (x.2.1 + s * x.2.2)) :=
    paramIntegral_contDiff_inf
      (fun s (x : ℝ × (ℝ × ℝ)) => deriv (fun u => c x.1 u) (x.2.1 + s * x.2.2)) (-1) 1 hg
  refine ⟨?_, ?_⟩
  · simpa only [chordW] using hW
  · have h1 := contDiff_deriv_fst'
        (fun z : ℝ × (ℝ × ℝ) =>
          ∫ s in (-1 : ℝ)..1, deriv (fun u => c z.1 u) (z.2.1 + s * z.2.2)) hW
    simpa only [chordW, chordWd] using h1

end Work.RPB.B2
