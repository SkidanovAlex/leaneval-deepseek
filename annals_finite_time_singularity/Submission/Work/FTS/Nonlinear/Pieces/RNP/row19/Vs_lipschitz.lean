/-
# Row 19 of the N4 table — the Lipschitz bound in `z` for the coefficient `V(Φ̃_*)`

The piece of row 19 is `N₃^{**} = -2α · V(Φ̃_*) · D_zF_*` (`Work.FTS.Nonlin.N3ss`), and the
whole difficulty of the row is that the coefficient `V = V(Φ̃_*) = ∂_θΦ̃_* - tan θ · Φ̃_*`
may be *discontinuous at `z = 0`*: the frozen `StarPkg` bounds it only in the weighted space
`𝒲^{4,∞}` (suprema over the closed domain `[0,∞) × [0,π/2]`, no continuity).  What saves the
decomposition `V·D_zF_* = (V/z)·(z·D_zF_*)` is that `V` *is* smooth down to `z = 0` — the
only singular ingredient of `Φ̃_*` is the `L₁₂`-correction `Θ_* = (1/(4α)) sin(2θ) L₁₂(F_*)`,
which collapses to the elementary `sin(2θ)/(2(1+z))` — so that `V` has a *bounded rate of
change* in `z`: this file proves

  `|V(z,θ) - V(0,θ)| ≤ max Cs 0 · α · z`  for `z ∈ [0,∞)`, `θ ∈ (0,π/2)`,

i.e. `V(·,θ)` is `max Cs 0 · α`-Lipschitz on the half line, which is exactly the
quantitative form of "`V` is continuous at `z = 0⁺`" (and hence of the existence of the
limit `V(0⁺,θ)`).

## The route

* `V(Φ̃_*)` is `C^∞` on the half strip `(-1,∞) × (0,π/2)` (`Vs_smoothQuad`):
  `Φ_s` is `SmoothQuad` (a field of `StarPkg`), `Θ_*` is smooth there because of the profile
  identity `L₁₂(F_*) = 2α/(1+z)` on `z > -1` (`L12Fstar_eq_pos`), and `Vop` is the
  differentiation-and-multiplication-by-`tan θ = sin θ/cos θ`, smooth on the strip;
* hence the `z`-slice is `C^∞` on `(-1,∞)` and one applies the mean value inequality on the
  segment `[0,z]`, with the *derivative bound* `|(z+1) ∂_zV| ≤ max Cs 0 · α` (the `k = 1`
  summand of the `𝒲^{4,∞}`-norm, `row19aux.abs_dVs_le`).

## Two prerequisites for `α > 0` (with no upper bound on `α`)

The existing profile identity `Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`
assumes `α ≤ 1`, which is used *only* to obtain `c(α) ≠ 0` from `Work.Spaces.c_bounds`.
Both are reproved here without the upper bound: `c α = ∫₀^{π/2} Γ K > 0` for every `α > 0`
(the integrand `3(sinθ cos²θ)^{1+α/3}` is strictly positive on `(0,π/2)`), whence
`L₁₂(F_*)(z) = 2α/(1+z)` on the whole range `z > -1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The half strip `(-1,∞) × (0,π/2)`: the set on which `Φ_s` is smooth (`SmoothQuad`), and
on which the coefficient `V(Φ̃_*)` is smooth as well.  (Contrary to the *weighted* coefficient
`((z+1)/z)·ℛ(Φ̃_*)` of row 11 there is no `1/z`-factor here, so the smoothness survives down
to `z = 0`.) -/
abbrev HalfStrip : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Positivity of `c(α)` and the profile identity `L₁₂(F_*) = 2α/(1+z)` for every `α > 0` -/

/-- `c(α) = ∫₀^{π/2} Γ(θ)K(θ) dθ` is positive for every `α > 0` — the integrand
`Γ K = 3 (sinθ cos²θ)^{1+α/3}` is strictly positive on the open interval `(0,π/2)`.
(This is the general-`α` strengthening of `Work.Coercivity.c_pos`, which assumes `α ≤ 1`.) -/
theorem c_pos_of_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.c α := by
  have hint : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ :=
    Work.Spaces.CAux.integrableOn_GamK α hα
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
    exact (Work.Spaces.gamK_bounds α θ hα hθ).1
  have hmem : ∀ θ ∈ Set.Ioo (Real.pi / 6) (Real.pi / 3),
      θ ∈ Function.support (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ hθ
    have h1 : 0 < θ := by linarith [hθ.1, Real.pi_pos]
    have h2 : θ < Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
    have hu : 0 < Real.sin θ * Real.cos θ ^ 2 := mul_pos hsin (pow_pos hcos 2)
    have hGam : 0 < Work.Spaces.Gam α θ := by
      rw [Work.Spaces.Gam]
      exact Real.rpow_pos_of_pos hu _
    have hK : 0 < Work.Spaces.K θ := by rw [Work.Spaces.K]; positivity
    simp only [Function.mem_support]
    exact ne_of_gt (mul_pos hGam hK)
  have hmeas : 0 < volume (Function.support
      (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) ∩ Work.Spaces.Iθ) := by
    have hsub : Set.Ioo (Real.pi / 6) (Real.pi / 3) ⊆
        Function.support (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
          ∩ Work.Spaces.Iθ := by
      intro θ hθ
      exact ⟨hmem θ hθ, ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩⟩
    have hvol : 0 < volume (Set.Ioo (Real.pi / 6) (Real.pi / 3)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
    exact lt_of_lt_of_le hvol (measure_mono hsub)
  have hpos := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint).mpr hmeas
  simpa [Work.Spaces.c] using hpos

/-- The angular density of `L₁₂` at the profile `F_*` is `α · F_*(s)/s`, for **every**
`α > 0` (the general-`α` version of `Work.Construction.L12dens_Fstar`). -/
theorem L12dens_Fstar_pos {α : ℝ} (hα : 0 < α) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s
      = α * (Work.FM.Fstar s / s) := by
  have hc : Work.Spaces.c α ≠ 0 := ne_of_gt (c_pos_of_pos hα)
  rw [Work.Construction.L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

/-- **The profile identity `L₁₂(F_*)(z) = 2α/(1+z)` for every `α > 0` and every `z > -1`** —
the general-`α` version of `Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`. -/
theorem L12Fstar_eq_pos {α z : ℝ} (hα : 0 < α) (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
            = α * (Work.FM.Fstar s / s) from L12dens_Fstar_pos hα s)]
  rw [MeasureTheory.integral_const_mul,
    Work.FTS.Nonlinear.FstarPkg.integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring

/-! ## Smoothness of the coefficient `V(Φ̃_*)` on the half strip -/

/-- `Θ_* = (1/(4α)) sin(2θ) L₁₂(F_*)` is `C^∞` on the half strip `(-1,∞) × (0,π/2)`: the
profile identity turns it into the elementary `sin(2θ)/(2(1+z))`. -/
theorem ThetaFstar_contDiffOn_neg_one {α : ℝ} (hα : 0 < α) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Theta α (Work.Construction.Fstar α)))
      HalfStrip := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) HalfStrip := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) HalfStrip :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) HalfStrip :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ HalfStrip, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have h1 : -1 < p.1 := Set.mem_Ioi.mp hp.1
      have : (0 : ℝ) < 1 + p.1 := by linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [L12Fstar_eq_pos hα hz]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hzne : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  ring

/-- **`V(Φ̃_*)` is `C^∞` on the half strip `(-1,∞) × (0,π/2)`** — in particular it is
continuous in `z` down to `z = 0`, which is what the Lipschitz bound needs.  (This is the
improvement of `Rv_smooth`, which only gives smoothness on the *open* quadrant `z > 0` for
the `1/z`-weighted row-11 coefficient.) -/
theorem Vs_smoothQuad {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) := by
  have hVopen : IsOpen HalfStrip := isOpen_Ioi.prod isOpen_Ioo
  have hΦ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Φs) HalfStrip :=
    hs.smooth
  have hΘ : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Theta α (Work.Construction.Fstar α))) HalfStrip :=
    ThetaFstar_contDiffOn_neg_one (α := α) hα
  have hΨ : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
      HalfStrip := by
    refine (hΦ.sub hΘ).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    rfl
  have hpth := Work.FTS.LocData.contDiffOn_pth hVopen hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) HalfStrip :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) HalfStrip :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hcosne : ∀ p ∈ HalfStrip, Real.cos p.2 ≠ 0 := by
    intro p hp
    have hθ := Set.mem_Ioo.mp hp.2
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩)
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) HalfStrip := hsin.div hcos hcosne
  show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) HalfStrip
  have hfun : Function.uncurry (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
      = fun p : ℝ × ℝ =>
          Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) p.1 p.2
            - (Real.sin p.2 / Real.cos p.2)
              * Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs p.1 p.2 := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.Vop, Real.tan_eq_sin_div_cos]
  rw [hfun]
  exact hpth.sub (htan.mul hΨ)

/-! ## The Lipschitz bound -/

theorem Vs_lipschitz {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
          - Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs 0 θ|
        ≤ max Cs 0 * α * z := by
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz
  have hsq := Vs_smoothQuad (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) (Set.Ioi (-1)) :=
    hsq.curry_z hθ
  have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) z,
      DifferentiableAt ℝ (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) x := by
    intro x hx
    have hx1 : x ∈ Set.Ioi (-1) := by
      rw [Set.mem_Ioi]; linarith [hx.1]
    exact (hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hx1)
  have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) z,
      ‖deriv (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) x‖
        ≤ max Cs 0 * α := by
    intro x hx
    have hxI : x ∈ Work.Spaces.Iz := hx.1
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hb := Work.FTS.Nonlinear.Pieces.RNP.abs_dVs_le (α := α) (Cs := Cs) (Φs := Φs)
      hα hs x hxI θ hθI
    rw [Real.norm_eq_abs]
    have hder : deriv (fun ζ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs ζ θ) x
        = Work.Spaces.pz (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) x θ := rfl
    rw [hder]
    refine le_trans ?_ hb
    rw [abs_mul, abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x + 1)]
    nlinarith [abs_nonneg (Work.Spaces.pz (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) x θ),
      hx.1]
  have hmain := (convex_Icc (0 : ℝ) z).norm_image_sub_le_of_norm_deriv_le hdiff hbdd
    (left_mem_Icc.mpr hz0) (right_mem_Icc.mpr hz0)
  simpa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hz0] using hmain

end Work.FTS.Nonlinear.Pieces.RNP.row19
