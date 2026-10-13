import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `blockMeas` — a.e.-measurability of the blocks of the `rl1` rows

The `rl1`-estimates of the N4 chapter integrate the pieces of `N` against the radial weight
`r⁻¹` and the angular weight `K`, on the domain `(0,∞) × Iθ` with the measure `dz dθ`.  Every
`lintegral`/`integral` bookkeeping along the way needs the a.e.-measurability of the integrands
with respect to the product measure

  `bmMeasure = (volume.restrict (Ioi 0)).prod (volume.restrict Iθ)`,

and that is what this file supplies: the sixteen blocks of the `rl1` rows (the datum `g` and
its three first `D`-derivatives, the angular moment `FK g`, the six elliptic coefficients
`Rop/Uop/Vop` of both stream functions `Φ̃_g` and `Φ̃_*`, and the whole `F_*`-package with its
angular moment) are all a.e.-measurable.

The measure is the planar Lebesgue measure restricted to the open quadrant `(0,∞) × (0,π/2)`
(the boundary lines are null), so continuity on the open quadrant suffices; that continuity
comes from `SmoothQuad`, which the packages `GalClass`, `StarPkg`, `EllPkgG` provide for every
block except the `Φ̃_*`-coefficients.  For those one needs `SmoothQuad (Φ̃_*)`, i.e. the
smoothness of `Θ_*(α) = (1/(4α)) sin 2θ · L₁₂(F_*)`, which holds because `F_*` is *separable*
and `L₁₂` therefore collapses to `const · 2/(1+z)`; that computation (`L12_Fstar_general`) is
the only non-formal input here, and it is done for **every** real `α` (the packages carry no
positivity hypothesis on `α`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## The measure of the block, and continuity on the open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the blocks live. -/
abbrev bmQd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The product measure of the `rl1` block: Lebesgue measure on `z > 0` times Lebesgue
measure on `Iθ = [0,π/2]`. -/
abbrev bmMeasure : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The restricted product measure agrees with the planar Lebesgue measure restricted to the
open quadrant: `Iθ` and `(0,π/2)` differ by the two endpoints. -/
theorem ae_prod_eq :
    (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
  exact MeasureTheory.Measure.set_prod_ae_eq Filter.EventuallyEq.rfl hθ

/-- **Continuity on the open quadrant gives a.e.-measurability for `bmMeasure`.** -/
theorem aesm_Qd_prod {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) bmQd) :
    AEMeasurable (Function.uncurry f) bmMeasure := by
  change AEMeasurable (Function.uncurry f)
    ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set ae_prod_eq]
  exact hf.aemeasurable ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

/-- A `SmoothQuad` block is continuous on the open quadrant, hence a.e.-measurable. -/
theorem continuousOn_Qd {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) bmQd := by
  have hsub : bmQd ⊆ Work.Spaces.quadU := by
    intro p hp
    obtain ⟨hz, hθ⟩ := hp
    have h1 : (-1 : ℝ) < p.1 := by linarith [Set.mem_Ioi.mp hz]
    exact ⟨h1, hθ⟩
  exact h.continuousOn.mono hsub

/-- A `SmoothQuad` block is a.e.-measurable for `bmMeasure`. -/
theorem aem_of_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    AEMeasurable (Function.uncurry f) bmMeasure :=
  aesm_Qd_prod (continuousOn_Qd h)

/-- Division by `sin 2θ` does not destroy a.e.-measurability on the open quadrant. -/
theorem aem_of_smoothQuad_div_s2 {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    AEMeasurable (Function.uncurry (fun z θ => f z θ / Work.Construction.s2 θ)) bmMeasure := by
  refine aesm_Qd_prod (ContinuousOn.div ?_ ?_ ?_)
  · exact continuousOn_Qd h
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  · intro p hp
    have h1 : 0 < 2 * p.2 := by linarith [hp.2.1]
    have h2 : 2 * p.2 < Real.pi := by linarith [hp.2.2, Real.pi_pos]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-! ## The three operators preserve `C^∞`-smoothness on the open quadrant -/

theorem sq_pth {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.pth f) :=
  Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU h

theorem sq_Dz {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) :=
  Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU h

theorem sq_Dth {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) :=
  Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU h

/-- `ℛ`, `𝒰` and `𝒱` preserve `C^∞`-smoothness on the open quadrant.  (`𝒰 = -3Ψ - α·D_zΨ`,
`𝒱 = ∂_θΨ - tan θ·Ψ`, and `ℛ` is the same rational expression divided by `cos θ`, which is
non-zero on the quadrant; `tan = sin/cos`.) -/
theorem smoothQuad_ops {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) ∧
    Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) ∧
    Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := by
  have hpz : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz Ψ) :=
    Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU h
  have hpth : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) := sq_pth h
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.Spaces.quadU :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.Spaces.quadU :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hne : ∀ p ∈ Work.Spaces.quadU, Real.cos p.2 ≠ 0 := by
    intro p hp
    have h2 : p.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [(Set.mem_Ioo.mp hp.2).1, Real.pi_pos],
        by linarith [(Set.mem_Ioo.mp hp.2).2]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h2)
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.Spaces.quadU := by
    rw [show (fun p : ℝ × ℝ => Real.tan p.2) = fun p => Real.sin p.2 / Real.cos p.2 from
      funext fun p => Real.tan_eq_sin_div_cos p.2]
    exact hsin.div hcos hne
  -- `𝒰`
  have hUaux : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -3 * Function.uncurry Ψ p
        - α * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p) Work.Spaces.quadU :=
    (contDiffOn_const.mul h).sub ((contDiffOn_const.mul contDiffOn_fst).mul hpz)
  have hU : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) :=
    hUaux.congr (fun p _ => rfl)
  -- `𝒱`
  have hVaux : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.pth Ψ) p
        - Real.tan p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    hpth.sub (htan.mul h)
  have hV : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) :=
    hVaux.congr (fun p _ => rfl)
  -- `ℛ`
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    (contDiffOn_const.mul hsin).mul h
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Spaces.quadU :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.Spaces.quadU :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.Spaces.quadU :=
    (h1.add h2).add h3
  have hRaux : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) / Real.cos p.2)
      Work.Spaces.quadU :=
    hnum.div hcos hne
  have hR : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) :=
    hRaux.congr (fun p _ => rfl)
  exact ⟨hR, hU, hV⟩

/-! ## The angular density of `L₁₂(F_*)`: the profile is separable

`F_*(z,θ) = α (Γ(θ)/c(α)) · F_{*,rad}(z)` is a function of `θ` times a function of `z`, so the
angular integration in `L₁₂dens` factors out and leaves a *constant* `L12FstarConst α` times
`F_{*,rad}(s)/s` — with no hypothesis on `α` (when `c(α) = 0` both sides are `0`). -/

/-- The constant `α ∫_θ K θ Γ(θ)/c(α)` into which the angular integration of the `F_*`-profile
collapses. -/
noncomputable def L12FstarConst (α : ℝ) : ℝ :=
  ∫ θ in Set.Icc 0 (π / 2),
    Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))

theorem L12dens_Fstar_general (α s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
      = L12FstarConst α * (Work.FM.Fstar s / s) := by
  rw [Work.FM.L12dens]
  have hpt : ∀ θ : ℝ, Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
      = (Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Work.Construction.Fstar]
    ring
  rw [show (∫ θ in Set.Icc 0 (π / 2), Work.Spaces.K θ * Work.Construction.Fstar α s θ / s)
      = ∫ θ in Set.Icc 0 (π / 2),
          (Work.Spaces.K θ * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)))
            * (Work.FM.Fstar s / s) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)]
  rw [L12FstarConst]
  exact integral_mul_const _ _

/-- `L₁₂(F_*)(z) = L12FstarConst α · 2/(1+z)` for every `z > -1` and **every** real `α`.
(The existing `L12_Fstar_eq_of_gt_neg_one` needs `0 < α ≤ 1`; this version does not, which is
what makes the whole `Φ̃_*`-block measurable without any hypothesis on `α`.) -/
theorem L12_Fstar_general {α : ℝ} {z : ℝ} (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z
      = L12FstarConst α * (2 / (1 + z)) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [show (∫ s in Set.Ioi z, Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s)
      = ∫ s in Set.Ioi z, L12FstarConst α * (Work.FM.Fstar s / s) from
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_Fstar_general α s)]
  rw [show (∫ s in Set.Ioi z, L12FstarConst α * (Work.FM.Fstar s / s))
      = L12FstarConst α * (∫ s in Set.Ioi z, Work.FM.Fstar s / s) from
    integral_const_mul _ _]
  rw [Work.FTS.Nonlinear.FstarPkg.integral_Ioi_Fstar_div_of_gt_neg_one z hz]

/-- **The singular part `Θ_*(α) = (1/(4α)) sin 2θ · L₁₂(F_*)` is `C^∞` on the open quadrant,
for every real `α`** (in particular at `α = 0` and for `α ≤ 0`, where
`L12_Fstar_eq_of_gt_neg_one` does not apply). -/
theorem thetaStarSmoothQuad {α : ℝ} :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (1 / (4 * α)) * Real.sin (2 * p.2)
        * (L12FstarConst α * (2 / (1 + p.1)))) Work.Spaces.quadU := by
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 / (1 + p.1)) Work.Spaces.quadU := by
      refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_fst) ?_
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1
        linarith
      positivity
    have hconst : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun _ : ℝ × ℝ => L12FstarConst α) Work.Spaces.quadU := contDiffOn_const
    exact (contDiffOn_const.mul hsin).mul (hconst.mul hden)
  refine hsm.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [L12_Fstar_general hz]

/-! ## The angular moment `FK f` -/

/-- The uncurried function `(z,θ) ↦ ∫_θ' K θ' f(z,θ') dθ'` is a.e.-measurable as soon as
`f` is continuous on the open quadrant: the θ-integral is a parametrised Bochner integral of
an a.e.-strongly-measurable function, and the result is constant in the second variable. -/
theorem fk_aemeasurable {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) bmQd) :
    AEMeasurable (Function.uncurry (fun z θ => Work.Construction.FK f z)) bmMeasure := by
  have hKcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
    rw [show Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from rfl]
    fun_prop
  have hprod : AEStronglyMeasurable
      (Function.uncurry (fun z θ => f z θ * Work.Spaces.K θ)) bmMeasure := by
    change AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ * Work.Spaces.K θ))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set ae_prod_eq]
    exact (hf.mul hKcont.continuousOn).aestronglyMeasurable
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)
  have h1 : AEStronglyMeasurable
      (fun z => ∫ θ, Function.uncurry (fun z θ => f z θ * Work.Spaces.K θ) (z, θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hprod.integral_prod_right'
  have h2 : (fun z => ∫ θ, Function.uncurry (fun z θ => f z θ * Work.Spaces.K θ) (z, θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) = fun z => Work.Construction.FK f z := by
    funext z
    rw [Work.Construction.FK]
    rfl
  have h3 : AEMeasurable (fun z => Work.Construction.FK f z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (h1.congr (Filter.EventuallyEq.of_eq h2)).aemeasurable
  exact (h3.aestronglyMeasurable.comp_fst).aemeasurable

/-! ## The target -/

theorem blockMeas {α Ce Cs : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    AEMeasurable (Function.uncurry (fun z θ => g z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dth g))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Spaces.pth g))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dz g))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ => Work.Construction.FK g z))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Construction.Fstar α))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dth (Work.Construction.Fstar α)))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α)))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    AEMeasurable (Function.uncurry (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hstar : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.SmoothQuad_Fstar α
  have hTheta : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) := thetaStarSmoothQuad
  have hPhiTs : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
    change Work.FTS.LocData.SmoothQuad
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact Work.FTS.LocData.smoothQuad_sub hs.smooth hTheta
  obtain ⟨hRop_s, hUop_s, hVop_s⟩ :=
    smoothQuad_ops (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) hPhiTs
  have hRop_g : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1.1
  have hUop_g : Work.FTS.LocData.SmoothQuad
      (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        / Work.Construction.s2 θ) := hell.U.1.1
  have hVop_g : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.V.1.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aem_of_smoothQuad hg
  · exact aem_of_smoothQuad (sq_Dth hg)
  · exact aem_of_smoothQuad (sq_pth hg)
  · exact aem_of_smoothQuad (sq_Dz hg)
  · exact fk_aemeasurable (continuousOn_Qd hg)
  · exact aem_of_smoothQuad_div_s2 hRop_g
  · exact aem_of_smoothQuad hUop_g
  · exact aem_of_smoothQuad hVop_g
  · exact aem_of_smoothQuad hRop_s
  · exact aem_of_smoothQuad hUop_s
  · exact aem_of_smoothQuad hVop_s
  · exact aem_of_smoothQuad hstar
  · exact aem_of_smoothQuad (sq_Dth hstar)
  · exact aem_of_smoothQuad (sq_pth hstar)
  · exact aem_of_smoothQuad (sq_Dz hstar)
  · exact fk_aemeasurable (continuousOn_Qd hstar)

end Work.FTS.Nonlinear.Pieces.rl1Tools
