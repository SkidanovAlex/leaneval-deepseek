/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/SlotDerivAll.lean` — the slot derivative of the
projected mollified family *at every interior fake time*

`EpsE4Thr.hasDerivWithinAt_mixed_JfamP_final` gives the slot chain rule

  `∂_τ (mixed j i (slice (JfamP ρ ε g) τ) z θ) = mixed j i (Pz (J_ε (epsRHSP τ))) z θ`

at one interior fake time `τ`.  Two consumers need it *simultaneously at every* `s ∈ (0,T)`:

* the Volterra bound of the `wip`-product rule (`abs_le_of_hasDerivAt_Ioo`: the fundamental
  theorem of calculus along the flow), and
* the a.e. `hderiv` hypothesis of the `wip`-product rules, which carries a *variable* derivative
  family `s ↦ mixed j i (Pz (J_ε (epsRHSP s)))` (the repair of the constant-`udot` defect of
  `EpsE4Thr.hasDerivAt_wip_of_slot`; see `WipSlotDerivVar.lean`).

Because every hypothesis of `hasDerivWithinAt_mixed_JfamP_final` other than `hτ` is quantified over
`∀ s ∈ Icc 0 T` already, the upgrade is a plain re-instantiation at each interior point, followed
by the conversion of the within-derivative on the *neighbourhood* `Icc 0 T ∈ 𝓝 s` into a genuine
`HasDerivAt`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDerivFinal
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipSlotIntegrable

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

/-- **The slot derivative of the projected mollified family at every interior fake time.** -/
theorem hasDerivAt_mixed_JfamP_all {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {j i : ℕ}
    (hε : 0 < ε) (hji : j + i ≤ 4) (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hsmR : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0)
    (hsmF : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hsmFR : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ ε Φs E g s))
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
    (hmemR : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (slice g s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmeasR : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l
        (epsRHSP α ρ ε Φs E g s) z θ) (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ K → |Work.Spaces.mixed k l (slice g s) q.1 q.2| ≤ C)
    (hbddR : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ K → |Work.Spaces.mixed k l (epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C)
    (hcontR : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → ContinuousOn (fun s : ℝ =>
      Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) z θ) (Set.Icc 0 T))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : ∀ r θ' : ℝ, 0 < r → θ' ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc 0 T,
      Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        (slice g s) (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)) volume)
    (hbdU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ ε Φs E g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hsliceU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |slice g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hdom : ∃ G : ℝ → ℝ, IntegrableOn G (Set.Ioi 0) ∧
      ∀ r ∈ Set.Ioi 0, ∀ s ∈ Set.Icc 0 T,
        |Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)) r| ≤ G r)
    (hintJeps : ∀ s ∈ Set.Icc 0 T, Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p * Work.Spaces.mixed j i (slice g s)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) volume)
    (hbdJeps : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
      |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt
      (fun t => Work.Spaces.mixed j i (slice (JfamP ρ ε g) t) z θ)
      (Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g s))) z θ) s := by
  intro s hs
  exact (hasDerivWithinAt_mixed_JfamP_final (τ := s) (j := j) (i := i) hρ hε hji hsol
    hsm hsmR hsmF hsmFR hmem hmemR hmeas hmeasR hbdd hbddR hcontR hz hθ hs hint hbdU hsliceU
    hdom hintJeps hbdJeps).hasDerivAt (Icc_mem_nhds hs.1 hs.2)

/-- **The a.e. form of the slot derivative along the projected mollified family**, in the exact
shape (a.e. in the space variable, for every interior fake time) that the `wip`-product rules and
the Volterra bound consume. -/
theorem ae_hasDerivAt_mixed_JfamP {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {j i : ℕ}
    (hε : 0 < ε) (hji : j + i ≤ 4) (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hsmR : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0)
    (hsmF : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hsmFR : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ ε Φs E g s))
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
    (hmemR : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (slice g s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmeasR : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l
        (epsRHSP α ρ ε Φs E g s) z θ) (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ K → |Work.Spaces.mixed k l (slice g s) q.1 q.2| ≤ C)
    (hbddR : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ K → |Work.Spaces.mixed k l (epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C)
    (hcontR : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → ContinuousOn (fun s : ℝ =>
      Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) z θ) (Set.Icc 0 T))
    (hint : ∀ r θ' : ℝ, 0 < r → θ' ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc 0 T,
      Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        (slice g s) (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)) volume)
    (hbdU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ ε Φs E g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hsliceU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |slice g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hdom : ∃ G : ℝ → ℝ, IntegrableOn G (Set.Ioi 0) ∧
      ∀ r ∈ Set.Ioi 0, ∀ s ∈ Set.Icc 0 T,
        |Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)) r| ≤ G r)
    (hintJeps : ∀ (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc 0 T,
      Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        Work.Spaces.mixed j i (slice g s) (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) volume)
    (hbdJeps : ∀ (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s)
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt
        (fun t => Work.Spaces.mixed j i (slice (JfamP ρ ε g) t) p.1 p.2)
        (Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
          (epsRHSP α ρ ε Φs E g s))) p.1 p.2) s := by
  filter_upwards [ae_mem_openQuadrant_fts] with p hp
  exact hasDerivAt_mixed_JfamP_all (j := j) (i := i) hρ hε hji hsol hsm hsmR hsmF hsmFR hmem
    hmemR hmeas hmeasR hbdd hbddR hcontR hp.1 hp.2 hint hbdU hsliceU hdom
    (hintJeps p.1 p.2 hp) (hbdJeps p.1 p.2 hp)

end Work.FTS.StrongEps.EpsE4Thr
