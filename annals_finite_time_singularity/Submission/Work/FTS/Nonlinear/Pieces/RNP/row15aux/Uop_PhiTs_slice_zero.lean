/-
# `𝒰(Φ̃_*)(0,θ) = 0` — the `z = 0` slice of the `Φ̃_*`-coefficient of `N₂^{**}`

This module proves `Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_slice_zero`: for a
`StarPkg`-datum `Φ_s` (the stream function of `F_*`) and every `θ ∈ Iθ`,

  `𝒰(Φ̃_*)(0,θ) = -3 Φ̃_*(0,θ) - α·0·∂_zΦ̃_*(0,θ) = 0`,

i.e. `Φ̃_*(0,θ) = Θ_*(α)(0,θ)`: the `z = 0` trace of the residual `Φ̃_* = Φ_s - Θ_*(α)`
(where `Θ_*(α) = (1/(4α)) sin 2θ · L₁₂(F_*)`) equals the trace of its singular part.

## The mathematics

Write `Ψ := Φ̃_* = PhiTs α Φs` and `h := Ψ(0,·)`.  Two facts pin `h` down.

* **The `𝒲^{4,∞}`-bound on `ℛ`.** `StarPkg.R` says `(z+1)/z · ℛ(Ψ)` is bounded on
  `[0,∞) × [0,π/2]`; since `ℛ(Ψ)` is `C^∞` up to `z = 0` (it is built from `Ψ` and its first
  derivatives, and `Ψ = Φ_s - Θ_*(α)` with both pieces smooth on `z > -1`), the bound
  `|ℛ(Ψ)(z,θ)| ≤ M z/(z+1)` forces `ℛ(Ψ)(0,θ) = 0` for `θ ∈ (0,π/2)`.  At `z = 0` the
  coefficient `ℛ` is `(2 sin θ · h + cos θ · h')/cos θ`, so `h' = -2 tan θ · h` on `(0,π/2)`,
  whence `h/cos²` is constant, i.e. `h = C cos²θ`.
* **The elliptic equation at `z = 0`.**  `bslOp α Φ_s = F_*` for `z > 0`, and letting
  `z → 0⁺` (all the ingredients are continuous on the closed quadrant in the radial direction)
  kills the two radial terms and the source `F_*(0,θ) = 0`, leaving `L₀(Φ_s(0,·)) = 0` on
  `(0,π/2)`, where `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` is the angular operator.

Since `Φ_s(0,θ) = h(θ) + Θ_*(α)(0,θ) = C cos²θ + (c/c)·sin 2θ/2` and `L₀(cos²·) = -3`,
`L₀(sin 2·) = 0`, the second fact gives `-3C = 0`, hence `C = 0`, hence `h ≡ 0` on `Iθ`.

## The `c/c` normalisation

`F_*`'s profile is `F_* = α (Γ(θ)/c(α)) 2z/(1+z)²`, and the identity `L₁₂(F_*)(z) = 2α/(1+z)`
is *proved* elsewhere under `α ≤ 1` (through `c(α) ≠ 0`); the statement proved here carries no
upper bound on `α`, so the normalisation is kept: the identity is proved in the form

  `L₁₂(F_*)(z) = (c α / c α) · 2α/(1+z)`  (`L12_Fstar_cc`),

which degenerates correctly when `c α = 0` (then `F_* ≡ 0` and both sides vanish).  This is
what makes `Θ_*(α)` explicitly smooth on `z > -1` for every `α > 0` — and it is exactly the
`z = 0` *trace* of `Θ_*(α)` that the estimate needs.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## 0. Elementary facts on the angular interval -/

/-- `cos θ ≠ 0` for `θ ∈ (0,π/2)`. -/
theorem cos_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)

/-- At `z = 0` the operator `𝒰` is `-3` times the value. -/
theorem Uop_right {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {θ : ℝ} (h : Ψ 0 θ = 0) :
    Work.Construction.Uop α Ψ 0 θ = 0 := by
  rw [Work.Construction.Uop, h]
  ring

/-! ## 1. The profile identity with the normalisation `c/c` kept -/

/-- The angular density of `L₁₂` at the profile `F_*`, in the form valid for **every** `α`:
the normalisation constant is kept in the numerator *and* the denominator, so that the
identity degenerates to `0 = 0` when `c α = 0`.  (The variant of
`Work.Construction.L12dens_Fstar` that goes through `c α ≠ 0`.) -/
theorem L12dens_Fstar_cc (α : ℝ) (s : ℝ) :
    Work.Construction.L12dens (Work.Construction.Fstar α) s
      = (Work.Spaces.c α / Work.Spaces.c α) * (α * (Work.FM.Fstar s / s)) := by
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
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
      = α * Work.Spaces.c α / Work.Spaces.c α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval]
  rw [hcint]
  ring

/-- `L₁₂(F_*)(z) = (c α / c α)·2α/(1+z)` for every `z > -1` and every `α` — the `c/c`-form of
the profile identity, with no upper bound on `α`. -/
theorem L12_Fstar_cc (α z : ℝ) (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z
      = (Work.Spaces.c α / Work.Spaces.c α) * (2 * α / (1 + z)) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [setIntegral_congr_fun (s := Set.Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
          = (Work.Spaces.c α / Work.Spaces.c α) * (α * (Work.FM.Fstar s / s))
          from L12dens_Fstar_cc α s)]
  rw [show (fun s : ℝ => (Work.Spaces.c α / Work.Spaces.c α) * (α * (Work.FM.Fstar s / s)))
      = fun s : ℝ => (Work.Spaces.c α / Work.Spaces.c α) * α * (Work.FM.Fstar s / s) from by
    funext s; ring]
  rw [integral_const_mul, Work.FTS.Nonlinear.FstarPkg.integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring

/-- The singular part of the residual is the explicit smooth function
`(c/c)·sin 2θ/(2(1+z))` on the whole range `z > -1`. -/
theorem Theta_Fstar_cc {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : -1 < z) :
    Work.Construction.Theta α (Work.Construction.Fstar α) z θ
      = (Work.Spaces.c α / Work.Spaces.c α) * (Real.sin (2 * θ) / (2 * (1 + z))) := by
  have hz0 : (1 : ℝ) + z ≠ 0 := by linarith
  have hα0 : α ≠ 0 := ne_of_gt hα
  rw [Work.Construction.Theta, Work.Construction.s2, L12_Fstar_cc α z hz]
  field_simp
  ring

/-- `Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant, for every `α > 0` (no upper bound). -/
theorem smoothQuad_Theta_Fstar_cc {α : ℝ} (hα : 0 < α) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1; linarith
      positivity
    exact hnum.div hden hne
  refine (contDiffOn_const (c := Work.Spaces.c α / Work.Spaces.c α)).mul hbase |>.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  exact Theta_Fstar_cc hα (Set.mem_Ioi.mp hp.1)

/-- `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞` on the open quadrant, for every `α > 0`. -/
theorem smoothQuad_PhiTs_cc {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
  have hTheta := smoothQuad_Theta_Fstar_cc (α := α) hα
  show Work.FTS.LocData.SmoothQuad
    (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
  exact Work.FTS.LocData.smoothQuad_sub hS.smooth hTheta

/-! ## 2. The calculus of the angular slice -/

/-- The product rule for `tan θ · u` at an interior angle. -/
theorem deriv_tan_mul {u : ℝ → ℝ} {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hu : DifferentiableAt ℝ u θ) :
    deriv (fun t : ℝ => Real.tan t * u t) θ
      = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ :=
  (((Real.hasDerivAt_tan hcos).mul hu.hasDerivAt).deriv)

/-- The unfolding of `L₀` on a function of `θ` alone. -/
theorem Lzero_theta_unfold (u : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => u θ') z θ
      = -(deriv (deriv u) θ) + deriv (fun t : ℝ => Real.tan t * u t) θ - 6 * u θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `L₀` of a function of `θ` alone, in the product-rule form
`-u'' + u/cos²θ + tan θ·u' - 6u`. -/
theorem Lzero_theta_only {u : ℝ → ℝ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hu : DifferentiableAt ℝ u θ) :
    Work.Elliptic.Lzero (fun _ θ' => u θ') z θ
      = -(deriv (deriv u) θ) + 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ
        - 6 * u θ := by
  rw [Lzero_theta_unfold, deriv_tan_mul hcos hu]
  ring

/-- The second `θ`-derivative of a `θ`-slice, in the form of the two-variable datum. -/
theorem pthIter_two_slice (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 u z θ = deriv (deriv (fun θ' => u z θ')) θ := by
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- The same identity as `Lzero_theta_only`, with the `θ`-derivatives written as the
`pth`/`pthIter` of the two-variable datum — the form in which continuity in `z` is visible. -/
theorem Lzero_slice_eq {u : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad u) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Elliptic.Lzero (fun _ θ' => u z θ') 0 θ
      = -(Work.Spaces.pthIter 2 u z θ) + 1 / Real.cos θ ^ 2 * u z θ
        + Real.tan θ * Work.Spaces.pth u z θ - 6 * u z θ := by
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Ioo hθ
  have hdiff : DifferentiableAt ℝ (fun θ' => u z θ') θ :=
    (((hsm.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ))
  rw [pthIter_two_slice u z θ]
  exact Lzero_theta_only hcos hdiff

/-- Congruence of `L₀` on a `θ`-only function under eventual equality. -/
theorem Lzero_congr_of_eventuallyEq {f g : ℝ → ℝ} {z θ : ℝ} (h : f =ᶠ[𝓝 θ] g) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = Work.Elliptic.Lzero (fun _ θ' => g θ') z θ := by
  have h3 : (fun t : ℝ => Real.tan t * f t) =ᶠ[𝓝 θ] (fun t : ℝ => Real.tan t * g t) := by
    filter_upwards [h] with t ht
    rw [ht]
  have h1 : deriv f =ᶠ[𝓝 θ] deriv g := h.deriv
  have h2 : deriv (deriv f) =ᶠ[𝓝 θ] deriv (deriv g) := h1.deriv
  rw [Lzero_theta_unfold, Lzero_theta_unfold, h2.eq_of_nhds, h3.deriv_eq, h.eq_of_nhds]

/-- The explicit computation `L₀(C cos²· + K sin 2·/2) = -3C`: the `sin 2θ` part is in the
kernel of `L₀` and `L₀(cos²·) = -3`. -/
theorem Lzero_cos_sq_add_sin {C K z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero
        (fun _ θ' => C * Real.cos θ' ^ 2 + K * Real.sin (2 * θ') / 2) z θ = -3 * C := by
  set f : ℝ → ℝ := fun θ' => C * Real.cos θ' ^ 2 + K * Real.sin (2 * θ') / 2 with hf
  have hcos2pt : ∀ t : ℝ, Real.cos (2 * t) = Real.cos t ^ 2 - Real.sin t ^ 2 := by
    intro t
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hf1 : ∀ t : ℝ, HasDerivAt f
      (-2 * C * Real.sin t * Real.cos t + K * (Real.cos t ^ 2 - Real.sin t ^ 2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => C * Real.cos s ^ 2)
        (C * (2 * Real.cos t ^ 1 * (-Real.sin t))) t :=
      ((Real.hasDerivAt_cos (x := t)).pow 2).const_mul C
    have h2 : HasDerivAt (fun s : ℝ => K * Real.sin (2 * s) / 2)
        (K * (Real.cos (2 * t) * 2) / 2) t := by
      have hin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
      exact (((Real.hasDerivAt_sin (x := 2 * t)).comp t hin).const_mul K).div_const 2
    have h3 := h1.add h2
    rw [hf]
    convert h3 using 1
    rw [hcos2pt t]
    ring
  have hf2 : HasDerivAt (fun t : ℝ => -2 * C * Real.sin t * Real.cos t
        + K * (Real.cos t ^ 2 - Real.sin t ^ 2))
      (-2 * C * (Real.cos θ ^ 2 - Real.sin θ ^ 2) - 2 * K * (2 * Real.sin θ * Real.cos θ)) θ := by
    have ha : HasDerivAt ((fun t : ℝ => -2 * C * Real.sin t) * Real.cos)
        (-2 * C * Real.cos θ * Real.cos θ + -2 * C * Real.sin θ * (-Real.sin θ)) θ :=
      (Real.hasDerivAt_sin (x := θ)).const_mul (-2 * C) |>.mul (Real.hasDerivAt_cos (x := θ))
    have hb : HasDerivAt ((fun t : ℝ => K * (Real.cos t ^ 2 - Real.sin t ^ 2)))
        (K * (2 * Real.cos θ ^ 1 * (-Real.sin θ) - 2 * Real.sin θ ^ 1 * Real.cos θ)) θ :=
      ((Real.hasDerivAt_cos (x := θ)).pow 2).sub
        ((Real.hasDerivAt_sin (x := θ)).pow 2) |>.const_mul K
    have h3 := ha.add hb
    convert h3 using 1
    ring
  have hdu : deriv f θ = -2 * C * Real.sin θ * Real.cos θ
      + K * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := (hf1 θ).deriv
  have hdd : deriv (deriv f) θ = -2 * C * (Real.cos θ ^ 2 - Real.sin θ ^ 2)
      - 2 * K * (2 * Real.sin θ * Real.cos θ) := by
    have hev : deriv f =ᶠ[𝓝 θ] (fun t : ℝ => -2 * C * Real.sin t * Real.cos t
        + K * (Real.cos t ^ 2 - Real.sin t ^ 2)) :=
      Filter.Eventually.of_forall fun t => (hf1 t).deriv
    rw [hev.deriv_eq]
    exact hf2.deriv
  have hdiff : DifferentiableAt ℝ f θ := (hf1 θ).differentiableAt
  have key : -Real.cos θ ^ 2 * deriv (deriv f) θ + f θ
      + Real.sin θ * Real.cos θ * deriv f θ - 6 * Real.cos θ ^ 2 * f θ
      = -3 * C * Real.cos θ ^ 2 := by
    rw [hdd, hdu]
    simp only [hf, Real.sin_two_mul]
    have hkey : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    have hfac : -Real.cos θ ^ 2 * (-2 * C * (Real.cos θ ^ 2 - Real.sin θ ^ 2)
            - 2 * K * (2 * Real.sin θ * Real.cos θ))
        + (C * Real.cos θ ^ 2 + K * (2 * Real.sin θ * Real.cos θ) / 2)
        + Real.sin θ * Real.cos θ * (-2 * C * Real.sin θ * Real.cos θ
            + K * (Real.cos θ ^ 2 - Real.sin θ ^ 2))
        - 6 * Real.cos θ ^ 2 * (C * Real.cos θ ^ 2 + K * (2 * Real.sin θ * Real.cos θ) / 2)
        = C * (Real.cos θ ^ 2 * (1 - 4 * (Real.cos θ ^ 2 + Real.sin θ ^ 2)))
          + K * (Real.sin θ * Real.cos θ * (1 - (Real.cos θ ^ 2 + Real.sin θ ^ 2))) := by
      ring
    rw [hfac, hkey]
    ring
  have hrw : -(deriv (deriv f) θ) + 1 / Real.cos θ ^ 2 * f θ + Real.tan θ * deriv f θ
        - 6 * f θ
      = 1 / Real.cos θ ^ 2 * (-Real.cos θ ^ 2 * deriv (deriv f) θ + f θ
          + Real.sin θ * Real.cos θ * deriv f θ - 6 * Real.cos θ ^ 2 * f θ) := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hlast : 1 / Real.cos θ ^ 2 * (-3 * C * Real.cos θ ^ 2) = -3 * C := by
    rw [show 1 / Real.cos θ ^ 2 * (-3 * C * Real.cos θ ^ 2)
        = (-3 * C * Real.cos θ ^ 2) / Real.cos θ ^ 2 by ring]
    rw [div_eq_iff (pow_ne_zero 2 hcos)]
  rw [Lzero_theta_only hcos hdiff, hrw, key, hlast]

/-! ## 3. The two limits at `z = 0⁺` -/

/-- Continuity in `z` at `z = 0` of the `z`-slice of a `SmoothQuad` function, at an interior
angle (the smoothness is available up to `z = 0` because `quadU = (-1,∞) × (0,π/2)`). -/
theorem continuousAt_slice_of_smoothQuad {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.LocData.SmoothQuad F) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousAt (fun z => F z θ) 0 :=
  (hF.curry_z hθ).continuousOn.continuousAt
    (isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0))

/-- **`ℛ(Φ̃_*)(0,θ) = 0`.**  `StarPkg.R` bounds `(z+1)/z · ℛ(Φ̃_*)` on the closed domain; since
`ℛ(Φ̃_*)` is continuous in `z` at `z = 0`, the bound `|ℛ| ≤ M·z/(z+1)` forces the value `0`. -/
theorem Rop_PhiTs_at_zero {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ = 0 := by
  intro θ hθ
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  have hbnd : ∀ z ∈ Work.Spaces.Iz, ∀ θ' ∈ Work.Spaces.Iθ,
      |(z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ'|
        ≤ max Cs 0 * α :=
    fun z hz θ' hθ' =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_WlInf_of_mem hS.R.1
        (le_trans hS.R.2 hle) hz hθ'
  have hpt : ∀ᶠ z in 𝓝[>] (0 : ℝ),
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ max Cs 0 * α * z / (z + 1) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzpos : (0 : ℝ) < z := hz
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have h := hbnd z (Set.mem_Ici.mpr hzpos.le) θ ⟨hθ.1.le, hθ.2.le⟩
    have hw : (0 : ℝ) < (z + 1) / z := div_pos hz1 hzpos
    rw [abs_mul, abs_of_pos hw] at h
    rw [le_div_iff₀ hz1]
    have h4 := mul_le_mul_of_nonneg_right h hzpos.le
    have h5 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| * (z + 1)
        = (z + 1) / z * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| * z := by
      have hz0 : z ≠ 0 := ne_of_gt hzpos
      calc |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| * (z + 1)
          = (z + 1) * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| := by ring
        _ = (z + 1) / z * z * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| := by
              rw [div_mul_cancel₀ _ hz0]
        _ = (z + 1) / z * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| * z := by
              ring
    rw [h5]
    linarith [h4]
  have hcont : ContinuousAt
      (fun z => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) 0 :=
    continuousAt_slice_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.RNP.row10aux.smoothQuad_Rop (smoothQuad_PhiTs_cc hα hS)) hθ
  have h1 : Tendsto (fun z => |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|)
      (𝓝[>] (0 : ℝ))
      (𝓝 |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ|) :=
    hcont.abs.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℝ => max Cs 0 * α * z / (z + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℝ => max Cs 0 * α * z / (z + 1)) 0 := by
      apply ContinuousAt.div
      · exact continuousAt_const.mul continuousAt_id
      · exact continuousAt_id.add continuousAt_const
      · norm_num
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h3 := le_of_tendsto_of_tendsto h1 h2 hpt
  have h4 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ| = 0 :=
    le_antisymm h3 (abs_nonneg _)
  exact abs_eq_zero.mp h4

/-- **`L₀(Φ_s(0,·)) = 0`.**  The equation `bslOp α Φ_s = F_*` holds for `z > 0`; all four
terms are continuous in `z` down to `z = 0` (the two radial terms because of their explicit
factor `z`), and `F_*(0,θ) = 0`, so the limit gives `L₀(Φ_s(0,·)) = 0` on `(0,π/2)`. -/
theorem Lzero_PhiTs_slice_zero {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Elliptic.Lzero (fun _ θ' => Φs 0 θ') 0 θ = 0 := by
  intro θ hθ
  have hsm := hS.smooth
  -- the slicewise form of the equation, for `z > 0`
  have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.Lzero (fun _ θ' => Φs z θ') 0 θ
        = Work.Construction.Fstar α z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φs z θ
          + α * (5 + α) * z * Work.Spaces.pz Φs z θ := by
    intro z hz
    have h := hS.sol.1 z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at h
    rw [show Work.Elliptic.Lzero (fun _ θ' => Φs z θ') 0 θ = Work.Elliptic.Lzero Φs z θ
      from rfl]
    linarith
  -- the right-hand side tends to `0`
  have hF : ContinuousAt (fun z : ℝ => Work.Construction.Fstar α z θ) 0 := by
    have hfun : (fun z : ℝ => Work.Construction.Fstar α z θ)
        = fun z : ℝ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α)
            * (2 * z / (1 + z) ^ 2) := by
      funext z
      simp only [Work.Construction.Fstar, Work.FM.Fstar]
    rw [hfun]
    apply ContinuousAt.mul
    · exact continuousAt_const
    · apply ContinuousAt.div
      · exact continuousAt_const.mul continuousAt_id
      · apply ContinuousAt.pow
        apply ContinuousAt.add
        · exact continuousAt_const
        · exact continuousAt_id
      · norm_num
  have hpz2 : ContinuousAt (fun z : ℝ => Work.Spaces.pzIter 2 Φs z θ) 0 := by
    have h1 : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz Φs) :=
      Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hsm
    have h2 : Work.FTS.LocData.SmoothQuad (Work.Spaces.pzIter 2 Φs) := by
      have h3 : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz (Work.Spaces.pz Φs)) :=
        Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU h1
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h3
    exact continuousAt_slice_of_smoothQuad h2 hθ
  have hpz : ContinuousAt (fun z : ℝ => Work.Spaces.pz Φs z θ) 0 :=
    continuousAt_slice_of_smoothQuad
      (Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hsm) hθ
  have hRHS : Tendsto (fun z : ℝ => Work.Construction.Fstar α z θ
      + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φs z θ
      + α * (5 + α) * z * Work.Spaces.pz Φs z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsum : ContinuousAt (fun z : ℝ => Work.Construction.Fstar α z θ
        + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φs z θ
        + α * (5 + α) * z * Work.Spaces.pz Φs z θ) 0 := by
      apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hF
        · apply ContinuousAt.mul
          · exact continuousAt_const.mul (continuousAt_id.pow 2)
          · exact hpz2
      · apply ContinuousAt.mul
        · exact continuousAt_const.mul continuousAt_id
        · exact hpz
    have hval : (fun z : ℝ => Work.Construction.Fstar α z θ
        + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φs z θ
        + α * (5 + α) * z * Work.Spaces.pz Φs z θ) 0 = 0 := by
      have hF0 : Work.Construction.Fstar α 0 θ = 0 := by
        simp only [Work.Construction.Fstar, Work.FM.Fstar]
        norm_num
      simp only [hF0]
      ring
    simpa only [hval] using hsum.tendsto.mono_left nhdsWithin_le_nhds
  -- the left-hand side tends to its value at `z = 0`
  have hLHS : Tendsto (fun z : ℝ => Work.Elliptic.Lzero (fun _ θ' => Φs z θ') 0 θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.Elliptic.Lzero (fun _ θ' => Φs 0 θ') 0 θ)) := by
    have h1 : Work.FTS.LocData.SmoothQuad (Work.Spaces.pthIter 2 Φs) := by
      have ha : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Φs) :=
        Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm
      have hb : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Spaces.pth Φs)) :=
        Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU ha
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hb
    have h2 : ContinuousAt (fun z : ℝ => Work.Spaces.pthIter 2 Φs z θ) 0 :=
      continuousAt_slice_of_smoothQuad h1 hθ
    have h3 : ContinuousAt (fun z : ℝ => Work.Spaces.pth Φs z θ) 0 :=
      continuousAt_slice_of_smoothQuad
        (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm) hθ
    have h4 : ContinuousAt (fun z : ℝ => Φs z θ) 0 :=
      continuousAt_slice_of_smoothQuad hsm hθ
    have hscr : ContinuousAt (fun z : ℝ => -(Work.Spaces.pthIter 2 Φs z θ)
        + 1 / Real.cos θ ^ 2 * Φs z θ + Real.tan θ * Work.Spaces.pth Φs z θ
        - 6 * Φs z θ) 0 := by
      apply ContinuousAt.sub
      · apply ContinuousAt.add
        · apply ContinuousAt.add
          · exact h2.neg
          · exact h4.const_mul (1 / Real.cos θ ^ 2)
        · exact h3.const_mul (Real.tan θ)
      · exact h4.const_mul 6
    have hval : (fun z : ℝ => -(Work.Spaces.pthIter 2 Φs z θ)
        + 1 / Real.cos θ ^ 2 * Φs z θ + Real.tan θ * Work.Spaces.pth Φs z θ
        - 6 * Φs z θ) 0 = Work.Elliptic.Lzero (fun _ θ' => Φs 0 θ') 0 θ :=
      (Lzero_slice_eq hsm (by norm_num) hθ).symm
    have htend : Tendsto (fun z : ℝ => -(Work.Spaces.pthIter 2 Φs z θ)
        + 1 / Real.cos θ ^ 2 * Φs z θ + Real.tan θ * Work.Spaces.pth Φs z θ
        - 6 * Φs z θ) (𝓝[>] (0 : ℝ))
        (𝓝 (Work.Elliptic.Lzero (fun _ θ' => Φs 0 θ') 0 θ)) := by
      simpa only [hval] using hscr.tendsto.mono_left nhdsWithin_le_nhds
    refine htend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : (-1 : ℝ) < z := by linarith [show (0 : ℝ) < z from hz]
    exact (Lzero_slice_eq hsm hz' hθ).symm
  exact tendsto_nhds_unique hLHS (hRHS.congr' (by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (heq z hz).symm))

/-! ## 4. The `θ`-slice at `z = 0` of `Φ̃_*` is identically zero -/

/-- The `θ`-only ODE satisfied by the `z = 0` trace of a function whose `ℛ` vanishes there. -/
theorem slice_ode_of_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hRop : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Work.Construction.Rop α Ψ 0 θ = 0) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun θ' => Ψ 0 θ') θ = -2 * Real.tan θ * Ψ 0 θ := by
  intro θ hθ
  have hcos_ne : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Ioo hθ
  have h := hRop θ hθ
  rw [Work.Construction.Rop] at h
  have hnum : 2 * Real.sin θ * Ψ 0 θ + α * Real.sin θ * 0 * Work.Spaces.pz Ψ 0 θ
      + Real.cos θ * Work.Spaces.pth Ψ 0 θ = 0 := by
    rcases div_eq_zero_iff.mp h with h1 | h2
    · exact h1
    · exact absurd h2 hcos_ne
  have h0 : α * Real.sin θ * 0 * Work.Spaces.pz Ψ 0 θ = 0 := by ring
  have h3 : Real.cos θ * Work.Spaces.pth Ψ 0 θ = -(2 * Real.sin θ * Ψ 0 θ) := by linarith
  have hpth : Work.Spaces.pth Ψ 0 θ = -2 * Real.tan θ * Ψ 0 θ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp at h3 ⊢
    linarith [h3]
  simpa only [Work.Spaces.pth] using hpth

/-- A differentiable function on `(0,π/2)` satisfying `h' = -2 tan θ · h` is `C · cos²θ`. -/
theorem slice_eq_const_mul_cos_sq {h : ℝ → ℝ}
    (hdiff : DifferentiableOn ℝ h (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv h θ = -2 * Real.tan θ * h θ) :
    ∃ C : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), h θ = C * Real.cos θ ^ 2 := by
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 :=
    fun θ hθ => cos_ne_zero_of_mem_Ioo hθ
  have hdiffF : DifferentiableOn ℝ (fun θ => h θ / Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    have hd := hdiff.differentiableAt (isOpen_Ioo.mem_nhds hθ)
    have hcos2 : DifferentiableAt ℝ (fun t : ℝ => Real.cos t ^ 2) θ :=
      ((Real.hasDerivAt_cos (x := θ)).pow 2).differentiableAt
    exact (hd.div hcos2 (pow_ne_zero 2 (hcos_ne θ hθ))).differentiableWithinAt
  have hderiv0 : Set.EqOn (deriv (fun θ => h θ / Real.cos θ ^ 2)) 0
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    show deriv (fun θ' : ℝ => h θ' / Real.cos θ' ^ 2) θ = 0
    have hd := (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hcos2 : HasDerivAt (fun t : ℝ => Real.cos t ^ 2)
        (-2 * Real.sin θ * Real.cos θ) θ := by
      have h := (Real.hasDerivAt_cos (x := θ)).pow 2
      convert h using 1
      ring
    have hdiv := hd.div hcos2 (pow_ne_zero 2 (hcos_ne θ hθ))
    have hgoal : deriv (h / fun t : ℝ => Real.cos t ^ 2) θ = 0 := by
      rw [hdiv.deriv, hode θ hθ, Real.tan_eq_sin_div_cos]
      field_simp
      ring
    exact hgoal
  obtain ⟨C, hC⟩ := IsOpen.exists_is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
    hdiffF hderiv0
  refine ⟨C, fun θ hθ => ?_⟩
  have h := hC θ hθ
  rwa [div_eq_iff (pow_ne_zero 2 (hcos_ne θ hθ))] at h

/-! ## 5. The lemma -/

theorem Uop_PhiTs_slice_zero {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ = 0 := by
  set Ψ : ℝ → ℝ → ℝ := Work.FTS.Nonlin.PhiTs α Φs with hΨ
  have hsmΨ : Work.FTS.LocData.SmoothQuad Ψ := smoothQuad_PhiTs_cc hα hS
  -- the `ℛ`-trace vanishes, hence the `θ`-trace of `Φ̃_*` is `C cos²θ`
  have hRop0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Work.Construction.Rop α Ψ 0 θ = 0 :=
    Rop_PhiTs_at_zero hα hS
  have hode := slice_ode_of_Rop hRop0
  have hdiffh : DifferentiableOn ℝ (fun θ => Ψ 0 θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsmΨ.curry_θ (by norm_num : (-1 : ℝ) < 0)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero
  obtain ⟨C, hC⟩ := slice_eq_const_mul_cos_sq hdiffh hode
  -- the angular operator on the trace of `Φ_s` vanishes
  have hLz := Lzero_PhiTs_slice_zero hα hS
  -- hence `C = 0`
  have hC0 : C = 0 := by
    have hθ0 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    have hcos0 : Real.cos (Real.pi / 4) ≠ 0 := by
      rw [Real.cos_pi_div_four]; positivity
    have hevent : (fun θ' => Φs 0 θ') =ᶠ[𝓝 (Real.pi / 4)]
        (fun θ' => C * Real.cos θ' ^ 2
          + (Work.Spaces.c α / Work.Spaces.c α) * Real.sin (2 * θ') / 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ0] with θ' hθ'
      have h1 : Ψ 0 θ' = C * Real.cos θ' ^ 2 := hC θ' hθ'
      have h2 : Work.Construction.Theta α (Work.Construction.Fstar α) 0 θ'
          = (Work.Spaces.c α / Work.Spaces.c α) * (Real.sin (2 * θ') / (2 * (1 + 0))) :=
        Theta_Fstar_cc hα (by norm_num)
      have h3 : Φs 0 θ' = Ψ 0 θ'
          + Work.Construction.Theta α (Work.Construction.Fstar α) 0 θ' := by
        rw [hΨ]
        simp only [Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil]
        ring
      rw [h3, h1, h2]
      ring
    have hdiff_f : DifferentiableAt ℝ (fun θ' => Φs 0 θ') (Real.pi / 4) :=
      ((hS.smooth.curry_θ (by norm_num : (-1 : ℝ) < 0)).differentiableOn
        Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ0)
    have h1 : Work.Elliptic.Lzero (fun _ θ' => Φs 0 θ') 0 (Real.pi / 4) = 0 := hLz _ hθ0
    have h2 : Work.Elliptic.Lzero (fun _ θ' => C * Real.cos θ' ^ 2
        + (Work.Spaces.c α / Work.Spaces.c α) * Real.sin (2 * θ') / 2) 0 (Real.pi / 4)
        = -3 * C := Lzero_cos_sq_add_sin hcos0
    have h3 : Work.Elliptic.Lzero (fun _ θ' => Φs 0 θ') 0 (Real.pi / 4)
        = Work.Elliptic.Lzero (fun _ θ' => C * Real.cos θ' ^ 2
          + (Work.Spaces.c α / Work.Spaces.c α) * Real.sin (2 * θ') / 2) 0 (Real.pi / 4) :=
      Lzero_congr_of_eventuallyEq hevent
    rw [h1] at h3
    linarith [h2, h3]
  have hzero : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Ψ 0 θ = 0 := by
    intro θ hθ
    rw [hC θ hθ, hC0]
    ring
  intro θ hθI
  have hΨ0 : Ψ 0 θ = 0 := by
    rcases eq_or_lt_of_le hθI.1 with h0 | h0
    · rw [← h0]
      have hΦ : Φs 0 0 = 0 := hS.sol.2.1 0
      have hTh : Work.Construction.Theta α (Work.Construction.Fstar α) 0 0 = 0 := by
        simp [Work.Construction.Theta, Work.Construction.s2]
      rw [hΨ]
      show Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs 0 0 = 0
      simp only [Work.Construction.PhiTil]
      rw [hΦ, hTh, sub_zero]
    rcases eq_or_lt_of_le hθI.2 with h2 | h2
    · rw [h2]
      have hΦ : Φs 0 (Real.pi / 2) = 0 := hS.sol.2.2.1 0
      have hTh : Work.Construction.Theta α (Work.Construction.Fstar α) 0 (Real.pi / 2) = 0 := by
        simp only [Work.Construction.Theta, Work.Construction.s2]
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        ring
      rw [hΨ]
      show Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs 0 (Real.pi / 2) = 0
      simp only [Work.Construction.PhiTil]
      rw [hΦ, hTh, sub_zero]
    · exact hzero θ ⟨h0, h2⟩
  rw [hΨ] at hΨ0 ⊢
  exact Uop_right hΨ0

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
