import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobius_pushedStarIcc
import Submission.Work.Drive.N2Lead.mobius_upperArcs
import Submission.Work.Drive.N2Lead.mobiusArcSmooth

/-!
# `Work.Drive.N2C.mobiusArcCurveRow`

The curve rows of the two model arcs `α = mobiusAlpha`, `β = mobiusBeta` of the Möbius saddle
certificate, about the origin: for every `w ∈ [-2,2]` the planar projection of the pushed arc is
non-zero and the angular rate `Im (conj z * z')` of that projection is non-zero, where `z` is the
planar projection and `z'` its derivative.

The point of the file is that **both rows are the same statement about the angular rate**: writing
`z = proj2 (g w)`, a direct computation gives

  `(star z * deriv (fun u => proj2 (g u)) w).im = z.re * (z').im - z.im * (z').re`

and `z.re = g w 0`, `z.im = g w 1`, `(z').re = deriv (fun u => g u 0) w`,
`(z').im = deriv (fun u => g u 1) w`; so the left-hand side is *literally* the angular rate
`x y' - y x'` appearing in `Work.Drive.N2Lead.StarAboutZero`, and

* `proj2 (g w) ≠ 0` follows because the rate would vanish at `z = 0`,
* `Im (conj z * z') ≠ 0` follows from the constant non-zero sign of the rate.

The identity `(deriv (fun u => proj2 (g u)) w).re = deriv (fun u => g u 0) w` (and the analogous
`im` fact) is proved by transporting `deriv` along the continuous linear maps `Complex.reCLM`,
`Complex.imCLM` (`fderiv_comp_deriv` + `ContinuousLinearMap.fderiv`); it needs differentiability of
`g` at `w`, which for the two arcs is `mobiusArcSmooth` (`ContDiff ℝ 1`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2Lead

noncomputable section

/-- The planar projection `v ↦ (v 0) + (v 1) i` as a continuous linear map (a local copy of
`Work.Drive.N2Lead.proj2CLM`, so that this module needs no extra import). -/
noncomputable def arcRowProjCLM : E3 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (⟨v 0, v 1⟩ : ℂ)
      map_add' := fun a b => by apply Complex.ext <;> simp
      map_smul' := fun c a => by apply Complex.ext <;> simp }

lemma arcRowProjCLM_apply (v : E3) : arcRowProjCLM v = proj2 v := rfl

/-- **The coordinates of the derivative of the planar projection.**  For a curve `g : ℝ → ℝ³`
differentiable at `w`, the real and imaginary parts of `deriv (fun u => proj2 (g u)) w` are the
derivatives of the two coordinates of `g`. -/
lemma deriv_proj2_re_im {g : ℝ → E3} {w : ℝ} (hg : DifferentiableAt ℝ g w) :
    (deriv (fun u : ℝ => proj2 (g u)) w).re = deriv (fun u : ℝ => g u 0) w ∧
      (deriv (fun u : ℝ => proj2 (g u)) w).im = deriv (fun u : ℝ => g u 1) w := by
  have hF : DifferentiableAt ℝ (fun u : ℝ => proj2 (g u)) w := by
    have hfun : (fun u : ℝ => proj2 (g u)) = ⇑arcRowProjCLM ∘ g := by
      funext u; rw [Function.comp_apply, arcRowProjCLM_apply]
    rw [hfun]
    exact ContinuousLinearMap.differentiableAt arcRowProjCLM |>.comp w hg
  have hre' : deriv (fun u : ℝ => (proj2 (g u)).re) w
      = (deriv (fun u : ℝ => proj2 (g u)) w).re := by
    have hcomp : (fun u : ℝ => (proj2 (g u)).re)
        = ⇑Complex.reCLM ∘ (fun u : ℝ => proj2 (g u)) := by
      funext u; rw [Function.comp_apply, Complex.reCLM_apply]
    rw [hcomp]
    rw [fderiv_comp_deriv (𝕜 := ℝ) (x := w) (f := fun u : ℝ => proj2 (g u))
        (l := ⇑Complex.reCLM) Complex.reCLM.differentiableAt hF]
    rw [ContinuousLinearMap.fderiv, Complex.reCLM_apply]
  have him' : deriv (fun u : ℝ => (proj2 (g u)).im) w
      = (deriv (fun u : ℝ => proj2 (g u)) w).im := by
    have hcomp : (fun u : ℝ => (proj2 (g u)).im)
        = ⇑Complex.imCLM ∘ (fun u : ℝ => proj2 (g u)) := by
      funext u; rw [Function.comp_apply, Complex.imCLM_apply]
    rw [hcomp]
    rw [fderiv_comp_deriv (𝕜 := ℝ) (x := w) (f := fun u : ℝ => proj2 (g u))
        (l := ⇑Complex.imCLM) Complex.imCLM.differentiableAt hF]
    rw [ContinuousLinearMap.fderiv, Complex.imCLM_apply]
  refine ⟨?_, ?_⟩
  · rw [← hre']; rfl
  · rw [← him']; rfl

/-- **The angular rate is `Im (conj z * z')`.**  With `z = proj2 (g w)` (the planar projection of a
curve differentiable at `w`) one has `Im (conj z * z') = z.re * (z').im - z.im * (z').re`, which is
exactly the angular rate `x y' - y x'` of `Work.Drive.N2Lead.StarAboutZero`. -/
lemma im_star_proj2_mul_deriv {g : ℝ → E3} {w : ℝ} (hg : DifferentiableAt ℝ g w) :
    (star (proj2 (g w)) * deriv (fun u : ℝ => proj2 (g u)) w).im
      = g w 0 * deriv (fun u : ℝ => g u 1) w - g w 1 * deriv (fun u : ℝ => g u 0) w := by
  obtain ⟨hre, him⟩ := deriv_proj2_re_im (g := g) hg
  have hzre : (proj2 (g w)).re = g w 0 := rfl
  have hzim : (proj2 (g w)).im = g w 1 := rfl
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_im,
    hzre, hzim, hre, him]
  ring

/-- **The two rows from the star condition.**  If a curve `g : ℝ → ℝ³` is `C¹` and its angular rate
about the origin has a constant non-zero sign on `[-2,2]` (`StarAboutZero`), then on `[-2,2]` the
planar projection never vanishes and `Im (conj z * z')` never vanishes. -/
lemma arcRow_of_starAboutZero {g : ℝ → E3} (hsm : ContDiff ℝ 1 g)
    (hstar : StarAboutZero g (Set.Icc (-2) 2)) :
    ∀ w ∈ Set.Icc (-2 : ℝ) 2, proj2 (g w) ≠ 0 ∧
      (star (proj2 (g w)) * deriv (fun u : ℝ => proj2 (g u)) w).im ≠ 0 := by
  intro w hw
  have hdiff : DifferentiableAt ℝ g w := hsm.differentiable one_ne_zero w
  have hrate : g w 0 * deriv (fun u : ℝ => g u 1) w - g w 1 * deriv (fun u : ℝ => g u 0) w ≠ 0 := by
    rcases hstar with h | h
    · exact ne_of_gt (h w hw)
    · exact ne_of_lt (h w hw)
  refine ⟨?_, ?_⟩
  · intro h0
    have h1 : g w 0 = 0 := by
      have := congrArg Complex.re h0
      simpa [proj2] using this
    have h2 : g w 1 = 0 := by
      have := congrArg Complex.im h0
      simpa [proj2] using this
    exact hrate (by rw [h1, h2]; ring)
  · rw [im_star_proj2_mul_deriv hdiff]; exact hrate

/-- Each of the two pushed model arcs of the upper level is `C¹` (the twist `twistX ε (-1)` of the
twisted model arc is smooth, and `pushY Dp εp 1` is smooth). -/
lemma contDiff_pushY_comp {arc : ℝ → E3} {Dp εp : ℝ} (harc : ContDiff ℝ 1 arc) :
    ContDiff ℝ 1 (fun w : ℝ => pushY Dp εp 1 (arc w)) := by
  have hpush_smooth : ContDiff ℝ 1 (pushY Dp εp 1) := by
    have h1 : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun v : E3 => pushY Dp εp 1 v) := by
      have hpair : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun v : E3 => ((1 : ℝ), v)) :=
        (contDiff_const (c := (1 : ℝ))).prodMk contDiff_id
      exact (contDiff_pushY Dp εp).comp hpair
    exact h1.of_le (by simp)
  exact hpush_smooth.comp harc

theorem mobiusArcCurveRow {ηs δ a' ε Dp εp C₀ : ℝ} (hηs : 0 < ηs) (hηs' : ηs < 1 / 10)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (ha' : 0 < a') (hε : 0 < ε)
    (hεa : ε ≤ Real.sqrt (a' ^ 2 + ηs))
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * ηs ≤ δ)
    (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    (hpush : Work.Drive.N2Lead.StarAboutZero (fun w : ℝ => Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.mobiusAlpha ηs δ ηs a' ε w)) (Set.Icc (-2) 2) ∧
      Work.Drive.N2Lead.StarAboutZero (fun w : ℝ => Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.mobiusBeta ηs δ ηs a' ε w)) (Set.Icc (-2) 2)) :
    (∀ w ∈ Set.Icc (-2) 2,
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.mobiusAlpha ηs δ ηs a' ε w)) ≠ 0 ∧
        (star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.mobiusAlpha ηs δ ηs a' ε w)))
          * deriv (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
              (Work.Drive.N2Lead.mobiusAlpha ηs δ ηs a' ε u))) w).im ≠ 0) ∧
    (∀ w ∈ Set.Icc (-2) 2,
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.mobiusBeta ηs δ ηs a' ε w)) ≠ 0 ∧
        (star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.mobiusBeta ηs δ ηs a' ε w)))
          * deriv (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
              (Work.Drive.N2Lead.mobiusBeta ηs δ ηs a' ε u))) w).im ≠ 0) := by
  have hδ₂ : δ < 1 / 2 := by linarith
  have hα : ContDiff ℝ 1 (fun w : ℝ => pushY Dp εp 1 (mobiusAlpha ηs δ ηs a' ε w)) :=
    contDiff_pushY_comp (mobiusAlpha_contDiff hδ hδ₂ hηs)
  have hβ : ContDiff ℝ 1 (fun w : ℝ => pushY Dp εp 1 (mobiusBeta ηs δ ηs a' ε w)) :=
    contDiff_pushY_comp (mobiusBeta_contDiff hδ hδ₂ hηs)
  exact ⟨arcRow_of_starAboutZero hα hpush.1, arcRow_of_starAboutZero hβ hpush.2⟩

end

end Work.Drive.N2C
