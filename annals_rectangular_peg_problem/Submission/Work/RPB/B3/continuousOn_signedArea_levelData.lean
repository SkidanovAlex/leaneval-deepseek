import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPA3.deriv_deriv_swap

/-!
# `B3`: continuity of the signed area of the level curves

The signed area of the level curve `t ↦ Γ τ t s` is continuous in the level parameter `s` on the
whole strip `|s| < s₁`.

Writing `G (s,t) = Γ τ t s`, the signed area is

  `signedArea (G (s,·)) = (1/2) ∫_0^{2π} ω_ℂ (G (s,t)) (∂_t G (s,t)) dt`,

and `∂_t G (s,t)` is the evaluation of the Fréchet derivative `fderiv ℝ G (s,t)` at `(0,1)`
(`Work.RPA3.deriv_prodMk_right`).  On the *open* strip `|s| < s₁` the level data is `C³`, so the
Fréchet derivative is continuous there (`ContDiffOn.continuousOn_fderiv_of_isOpen`), and
`(s,t) ↦ (fderiv ℝ G (s,t)) (0,1)` is continuous.  Hence the integrand
`H (s,t) = ω_ℂ (G (s,t)) ((fderiv ℝ G (s,t)) (0,1))` is continuous on the strip, and
`s ↦ ∫_0^{2π} H (s,t) dt` is continuous by
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` applied to the
restriction of `H` to `Set.Ioo (-s₁) s₁ ×ˢ Set.univ` (a subtype, so no global continuity of `H`
is needed).

The abstract statement is isolated as `continuousOn_signedArea_of_contDiffOn`; the requested
theorem is the specialisation `G (s,t) = L.Γ τ t s`.
-/

open Filter
open Real
open scoped Topology ContDiff Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B3

/-! ## The bilinear form `ω_ℂ` -/

/-- `ω_ℂ` is continuous as a function of the pair. -/
lemma continuous_omegaC : Continuous (fun q : ℂ × ℂ => Work.RPV.ωC q.1 q.2) := by
  have h : (fun q : ℂ × ℂ => Work.RPV.ωC q.1 q.2)
      = fun q : ℂ × ℂ => ((starRingEnd ℂ) q.1 * q.2).im := rfl
  rw [h]
  exact Complex.continuous_im.comp
    ((Complex.continuous_conj.comp continuous_fst).mul continuous_snd)

/-! ## The abstract continuity statement -/

/-- **Continuity of the signed area in the family parameter.**

If `G : ℝ × ℝ → ℂ` is `C³` on the open strip `X ×ˢ univ`, then the signed area of the closed curve
`t ↦ G (x,t)` is continuous in `x` on `X`. -/
theorem continuousOn_signedArea_of_contDiffOn {X : Set ℝ} (hX : IsOpen X) {G : ℝ × ℝ → ℂ}
    (hG : ContDiffOn ℝ 3 G (X ×ˢ Set.univ)) :
    ContinuousOn (fun x : ℝ => Work.RPB.signedArea (fun t => G (x, t))) X := by
  have hU : IsOpen (X ×ˢ Set.univ) := hX.prod (isOpen_univ : IsOpen (Set.univ : Set ℝ))
  -- The partial `t`-derivative of `G`, as a function of the point, is continuous on the strip.
  have hderiv : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ G p) ((0, 1) : ℝ × ℝ))
      (X ×ˢ Set.univ) :=
    (hG.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  -- Hence the integrand is continuous on the strip.
  have hΨ : ContinuousOn
      (fun p : ℝ × ℝ => Work.RPV.ωC (G p) ((fderiv ℝ G p) ((0, 1) : ℝ × ℝ)))
      (X ×ˢ Set.univ) :=
    continuous_omegaC.comp_continuousOn (hG.continuousOn.prodMk hderiv)
  -- The parametric integral, over the subtype `X`, is continuous.
  have hInt : Continuous (fun x : X => ∫ t in (0 : ℝ)..(2 * π),
      Work.RPV.ωC (G ((x : ℝ), t)) ((fderiv ℝ G ((x : ℝ), t)) ((0, 1) : ℝ × ℝ))) := by
    have hsw : Continuous (fun p : X × ℝ => (((p.1 : X) : ℝ), p.2)) := by fun_prop
    have hmem : ∀ p : X × ℝ, (((p.1 : X) : ℝ), p.2) ∈ X ×ˢ Set.univ :=
      fun p => ⟨p.1.2, Set.mem_univ _⟩
    have hc : Continuous (Function.uncurry (fun x : X => fun t : ℝ =>
        Work.RPV.ωC (G ((x : ℝ), t)) ((fderiv ℝ G ((x : ℝ), t)) ((0, 1) : ℝ × ℝ)))) := by
      exact hΨ.comp_continuous hsw hmem
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 (2 * π)
  -- Transfer to `X` and replace `signedArea` by the integral of the Fréchet expression.
  rw [continuousOn_iff_continuous_domRestrict]
  refine (hInt.const_mul (1 / 2)).congr (fun x => ?_)
  show (1 / 2) * ∫ t in (0 : ℝ)..(2 * π),
      Work.RPV.ωC (G ((x : ℝ), t)) ((fderiv ℝ G ((x : ℝ), t)) ((0, 1) : ℝ × ℝ))
    = Work.RPB.signedArea (fun t => G ((x : ℝ), t))
  rw [Work.RPB.signedArea]
  congr 1
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have hhas : HasFDerivAt G (fderiv ℝ G ((x : ℝ), t)) ((x : ℝ), t) :=
    ((hG.contDiffAt (hU.mem_nhds ⟨x.2, Set.mem_univ t⟩)).differentiableAt
      (by norm_num)).hasFDerivAt
  rw [Work.RPA3.deriv_prodMk_right hhas]

/-! ## The level data is `C³` on the open strip -/

/-- The pair `(s,t) ↦ Γ τ t s` is `C³` on the open strip `|s| < s₁`, for `τ ∈ [0,1]`.

Indeed `(s,t) ↦ (τ,t,s)` maps the open strip `(-s₁,s₁) ×ˢ univ` into the set
`[0,1] × ℝ × (-s₁,s₁)` on which `L.smΓ` gives `C³` regularity, so `ContDiffOn.comp` applies. -/
lemma contDiffOn_levelData_pair {c : ℝ → ℝ → ℂ} {a : ℝ → ℝ → ℝ → ℝ}
    (L : Work.RPB.IsLevelData c a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => L.Γ τ p.2 p.1)
      (Set.Ioo (-L.s₁) L.s₁ ×ˢ Set.univ) := by
  have hg : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (τ, p.2, p.1))
      (Set.Ioo (-L.s₁) L.s₁ ×ˢ Set.univ) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (τ, p.2, p.1))
      (Set.Ioo (-L.s₁) L.s₁ ×ˢ Set.univ)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-L.s₁) L.s₁) := by
    rintro ⟨s, t⟩ ⟨hs, -⟩
    exact ⟨hτ, Set.mem_univ _, hs⟩
  have h := L.smΓ.comp hg hmap
  refine h.congr (fun p _ => ?_)
  rfl

/-! ## The requested theorem -/

-- The area of the level curves is continuous as a function of the level parameter (on the whole
-- strip `|s| < s₁`).  Plan: `signedArea (Γ τ · x) = (1/2) ∫_0^{2π} H x t dt` with
-- `H x t = ωC (Γ τ t x) (∂_t Γ (τ,t,x))`, and `H` is continuous on the *open* set
-- `Set.Ioo (-L.s₁) L.s₁ ×ˢ Set.univ` — the level data is `C³` there and the `t`-derivative of the
-- level data is again continuous, because it is the partial `fderiv` of the (t,s)-section
-- (`ContDiffOn.fderiv_of_isOpen` applied to the strip, together with
-- `Work.RPA3.deriv_prodMk_left/right` to identify `deriv`-sections with `fderiv` applied to
-- `(1,0)`/`(0,1)`; cf. the sibling pattern `Work.RPB.B3.contDiffAt_strip_comp` for how a
-- `ContDiffOn`-on-the-strip hypothesis is transported to the `(t,s)`-section).  Then
-- `x ↦ ∫_0^{2π} H x t dt` is continuous on the strip: either by the uniform continuity of `H` on
-- compact rectangles (`IsCompact.uniformContinuousOn_of_continuous`,
-- `intervalIntegral.norm_integral_le_of_norm_le_const`), or by
-- `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` applied to the
-- restriction of `H` to the open strip (the subtype `Set.Ioo (-L.s₁) L.s₁`).
theorem continuousOn_signedArea_levelData (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (L : Work.RPB.IsLevelData CI.c a)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun x : ℝ => Work.RPB.signedArea (fun t => L.Γ τ t x))
      (Set.Ioo (-L.s₁) L.s₁) := by
  have _ha := ha
  exact continuousOn_signedArea_of_contDiffOn (X := Set.Ioo (-L.s₁) L.s₁)
    (G := fun p : ℝ × ℝ => L.Γ τ p.2 p.1) isOpen_Ioo (contDiffOn_levelData_pair L hτ)

end Work.RPB.B3
