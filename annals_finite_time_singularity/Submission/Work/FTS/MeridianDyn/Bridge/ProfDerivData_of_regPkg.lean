import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Stability.L12Add
import Submission.Work.R1G.gDerivDataQd_phi_zero
import Submission.Work.FM.Core6
import Submission.Work.R1G.L12densFtot_add
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

open scoped Real Topology

/-! ## The `τ`-slice of the joint regularity of `RegPkg` -/

/-- The `τ`-slice of the joint `C^∞` regularity of `RegPkg.smooth` is `C^∞` on the open quadrant:
the slice of `(z,θ,τ') ↦ g z θ τ'` at `τ' = τ` is the composite of `g` with the smooth embedding
`(z,θ) ↦ (z,θ,τ)`, whose image at a point of the open quadrant lies in the open slab on which
`RegPkg.smooth` is asserted. -/
theorem smoothOpen_slice_of_regPkg {α : ℝ} {g : Work.FTS.MeridianDyn.Fam}
    (hreg : Work.FTS.Galerkin.RegPkg α g) {τ : ℝ} (hτ : 0 < τ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g τ) := by
  have hmap : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun q : ℝ × ℝ => ((q.1, q.2, τ) : ℝ × ℝ × ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by fun_prop
  have hmaps : Set.MapsTo (fun q : ℝ × ℝ => ((q.1, q.2, τ) : ℝ × ℝ × ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Ioi (-1 : ℝ)) := by
    intro q hq
    dsimp only
    exact ⟨hq.1, hq.2, by simp only [Set.mem_Ioi]; linarith⟩
  have hcomp := hreg.smooth.comp hmap hmaps
  show ContDiffOn ℝ Work.Stability.smoothOrder (fun q : ℝ × ℝ => g q.1 q.2 τ)
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
  exact hcomp

/-! ## The static derivation data of the `St2` chain, from the regularity package -/

/-- **The derivation data of the meridian bridge, from the regularity package.**  All seven fields
of `Work.FTS.MeridianDyn.ProfDerivData` are read off from the regularity of the family (`RegPkg`,
whose `smooth` field supplies the joint interior `C^∞` of `g`), the `C²`-regularity of `Φ` on the
open quadrant, and the two analytic facts about the `L₁₂`-density of the full profile `F_* + g`
(integrability on `(0,∞)` and continuity at `z > 0`):

* `h2`, `h3` — the `Φ = Φ̃ + Θ` decomposition is the definitional `ΦTil = Φ − Θ`, differentiated
  with `deriv_sub`; the `z`-slice of `Θ = (1/(4α)) sin(2θ) L₁₂(F)` is differentiable by
  `Work.FM.hasDerivAt_L12` (whose two hypotheses are exactly `hL12i`, `hL12c`);
* `h5`, `h6` — the two derivative evaluations of `Θ`, the Construction area's `Dz_Theta_eq` and
  `pth_Theta_eq`;
* `hDz`, `hpth` — additivity of `∂_z`, `∂_θ` over `F_* + g`
  (`Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split`);
* `hL` — the `L₁₂`-splitting over `F_* + g` on `z ≥ 0`: the angular slices of both
  summands are integrable (`Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn` for `g`,
  `Work.Stability.integrableOn_slice_Fstar` for `F_*`), so the densities add pointwise on
  `s > 0`, and the density of `F_*` is integrable
  (`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`), which lets the tail
  integral split (`Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable`). -/
theorem ProfDerivData_of_regPkg {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φ g : Work.FTS.MeridianDyn.Fam}
    (hreg : Work.FTS.Galerkin.RegPkg α g)
    (hΦ : ∀ τ : ℝ, 0 < τ → ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ)
      Work.Construction.Qd)
    (hL12i : ∀ τ : ℝ, 0 < τ → MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau α g τ)) (Set.Ioi 0))
    (hL12c : ∀ τ z : ℝ, 0 < τ → 0 < z → ContinuousAt
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau α g τ)) z) :
    Work.FTS.MeridianDyn.ProfDerivData α Φ g := by
  have hQd_open : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- the `z`-derivative of the singular part `Θ` (used by `h2`)
  have hThetaZ : ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      DifferentiableAt ℝ
        (fun z' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z := by
    intro z θ τ hq hτ
    have hz : 0 < z := hq.1
    have hder : HasDerivAt
        (fun ρ : ℝ => Work.FM.L12 Work.Spaces.K (Work.Construction.Ftau α g τ) ρ)
        (-(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau α g τ) z)) z :=
      Work.FM.hasDerivAt_L12 (a := 0) (hL12i τ hτ) (hL12c τ z hτ hz) (by linarith)
    have h2 := hder.differentiableAt.const_mul ((1 / (4 * α)) * Work.Construction.s2 θ)
    simpa only [Work.Construction.Theta, Work.Construction.L12] using h2
  -- the `θ`-derivative of the singular part `Θ` (used by `h3`)
  have hThetaT : ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      DifferentiableAt ℝ
        (fun θ' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ := by
    intro z θ τ _ _
    have hfun : (fun θ' : ℝ => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ')
        = fun θ' : ℝ => ((1 / (4 * α)) * Work.Construction.L12 (Work.Construction.Ftau α g τ) z)
            * Real.sin (2 * θ') := by
      funext θ'; simp only [Work.Construction.Theta, Work.Construction.s2]; ring
    rw [hfun]
    fun_prop
  -- the slice differentiability of `Φ` on the open quadrant (used by `h2`, `h3`)
  have hPhiz : ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      DifferentiableAt ℝ (fun z' => Φ z' θ τ) z := by
    intro z θ τ hq hτ
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, θ) :=
      ((hΦ τ hτ).contDiffAt (hQd_open.mem_nhds hq)).differentiableAt (by norm_num)
    exact Work.Spaces.differentiableAt_curry_left (G := fun z' θ' => Φ z' θ' τ) hd
  have hPhit : ∀ z θ τ : ℝ, (z, θ) ∈ Work.Construction.Qd → 0 < τ →
      DifferentiableAt ℝ (fun θ' => Φ z θ' τ) θ := by
    intro z θ τ hq hτ
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, θ) :=
      ((hΦ τ hτ).contDiffAt (hQd_open.mem_nhds hq)).differentiableAt (by norm_num)
    exact Work.Spaces.differentiableAt_curry_right (G := fun z' θ' => Φ z' θ' τ) hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `h2`: the `Φ = Φ̃ + Θ` decomposition, `z`-part
    intro z θ τ hq hτ
    have hsub : deriv (fun z' => Φ z' θ τ
          - Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z
        = deriv (fun z' => Φ z' θ τ) z
          - deriv (fun z' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z' θ) z :=
      deriv_sub (hPhiz z θ τ hq hτ) (hThetaZ z θ τ hq hτ)
    simp only [Work.Spaces.pz, Work.Construction.PhiTil, Work.FTS.Galerkin.slice]
    rw [hsub]
    ring
  · -- `h3`: the `Φ = Φ̃ + Θ` decomposition, `θ`-part
    intro z θ τ hq hτ
    have hsub : deriv (fun θ' => Φ z θ' τ
          - Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ
        = deriv (fun θ' => Φ z θ' τ) θ
          - deriv (fun θ' => Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ') θ :=
      deriv_sub (hPhit z θ τ hq hτ) (hThetaT z θ τ hq hτ)
    simp only [Work.Spaces.pth, Work.Construction.PhiTil, Work.FTS.Galerkin.slice]
    rw [hsub]
    ring
  · -- `h5`: the derivative evaluation of `Θ`, `z`-part
    intro z θ τ hq hτ
    have hz : 0 < z := hq.1
    simpa only [Work.Spaces.Dz] using
      (Work.Construction.Dz_Theta_eq (α := α) (z := z) (θ := θ)
        (F := Work.Construction.Ftau α g τ) hα (hL12i τ hτ) (hL12c τ z hτ hz) hz)
  · -- `h6`: the derivative evaluation of `Θ`, `θ`-part
    intro z θ τ _ _
    exact Work.Construction.pth_Theta_eq (α := α) hα z θ
  · -- `hDz`: the `D_z`-splitting over `F = F_* + g`
    exact fun z θ τ hq hτ =>
      (Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split hreg).1 z θ τ hq hτ
  · -- `hpth`: the `∂_θ`-splitting over `F = F_* + g`
    exact fun z θ τ hq hτ =>
      (Work.FTS.MeridianDyn.Bridge.Pieces.Dzg_pthg_split hreg).2 z θ τ hq hτ
  · -- `hL`: the `L₁₂`-splitting over `F = F_* + g`
    intro z τ hz hτ
    have hsmooth : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g τ) :=
      smoothOpen_slice_of_regPkg hreg hτ
    have hmem : Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice g τ) := hreg.mem4 τ hτ.le
    have hb : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.FTS.Galerkin.slice g τ s θ / s) Work.Spaces.Iθ :=
      Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn hsmooth hmem
    have ha : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α s θ / s) Work.Spaces.Iθ :=
      fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s
    have hSum : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K
          (fun z θ => Work.Construction.Fstar α z θ
            + Work.FTS.Galerkin.slice g τ z θ)) (Set.Ioi 0) :=
      hL12i τ hτ
    have hA : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi 0) :=
      Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 0 le_rfl
    have hsplit := Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable (α := α)
      (a := Work.Construction.Fstar α) (b := Work.FTS.Galerkin.slice g τ) ha hb hSum hA z hz
    rw [show Work.Construction.L12 (Work.Construction.Ftau α g τ) z
        = Work.Construction.L12
            (fun z θ => Work.Construction.Fstar α z θ
              + Work.FTS.Galerkin.slice g τ z θ) z from rfl, hsplit]

end Work.FTS.MeridianDyn.Bridge
