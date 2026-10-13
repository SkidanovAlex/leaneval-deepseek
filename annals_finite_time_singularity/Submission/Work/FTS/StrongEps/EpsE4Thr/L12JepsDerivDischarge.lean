/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/L12JepsDerivDischarge.lean` — the `L₁₂`-zero-mode chain
rule with its regularity hypotheses discharged

`EpsE4Thr.L12JepsDeriv` (the repaired brick) carries, besides the pointwise chain-rule data, the
two integrability/measurability hypotheses

* `hintVal : ∀ s ∈ Icc 0 T, IntegrableOn (fun r => L12dens K (J_ε (slice g s)) r) (Ioi 0)`,
* `hmeasDer : ∀ s ∈ Icc 0 T, AEStronglyMeasurable (fun r => L12dens K (J_ε (epsRHSP … g s)) r)
  (volume.restrict (Ioi 0))`,

needed because `L₁₂ (·) (0) = ∫_{Ioi 0} L12dens K ·` is a *total* Bochner integral (see the
refutation in `EpsE4Thr/L12_Jeps_deriv.lean`).

This module discharges both, in the regime in which the brick is consumed, from the regularity of
the *mollified* slices: `SmoothOpen` together with `HkMem α 4` implies the integrability of the
`L₁₂`-density on `(0,∞)` — that is the proved
`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem` — and hence also its a.e. strong
measurability.  So the only hypotheses left are the ones a caller of the energy/barrier route
genuinely has.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsDeriv
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **`hintVal` of `L12JepsDeriv`, discharged.**  For a family whose mollified slices are
`C^∞` on the open quadrant and of honest `ℋ⁴`, the `L₁₂`-density of every mollified slice is
integrable on `(0,∞)`. -/
theorem integrableOn_L12dens_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε T : ℝ} (hε : 0 < ε) {g : Fam}
    (hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
      (Work.FTS.StrongEps.Jeps ρ ε (slice g s))) :
    ∀ s ∈ Set.Icc 0 T, IntegrableOn
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) r) (Set.Ioi 0) := by
  intro s hs
  exact Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsm s hs)) (hmem s hs)

/-- **`L12JepsDeriv` with `hintVal` and `hmeasDer` discharged** from the regularity of the
mollified slices of the family and of the right-hand side. -/
theorem hasDerivWithinAt_L12_Jeps_slice {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hε : 0 < ε) (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hsmR : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0)
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
      (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
    (hmemR : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
      (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)))
    (hint : ∀ r θ : ℝ, 0 < r → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc 0 T,
      Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        (slice g s) (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) volume)
    (hbdU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ ε Φs E g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hsliceU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |slice g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hdom : ∃ G : ℝ → ℝ, IntegrableOn G (Set.Ioi 0) ∧
      ∀ r ∈ Set.Ioi 0, ∀ s ∈ Set.Icc 0 T,
        |Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)) r| ≤ G r)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivWithinAt (fun s => Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0)
      (Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g τ)) 0)
      (Set.Icc 0 T) τ :=
  L12JepsDeriv (α := α) (T := T) (Φs := Φs) (E := E) (g₀ := g₀) (g := g)
    hρ hε hsol hint hbdU hsliceU
    (integrableOn_L12dens_Jeps_slice (α := α) hρ hε hsm hmem)
    (fun s hs => (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsmR s hs)) (hmemR s hs)).aestronglyMeasurable)
    hdom hτ

end Work.FTS.StrongEps.EpsE4Thr
