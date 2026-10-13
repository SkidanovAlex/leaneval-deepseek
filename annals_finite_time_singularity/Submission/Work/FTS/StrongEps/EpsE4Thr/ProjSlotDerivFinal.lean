/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/ProjSlotDerivFinal.lean` — end of the chain: the
projected slot derivative with every regularity input discharged

This composes the two halves of the honest-derivative chapter:

* `EpsE4Thr.hasDerivWithinAt_L12_Jeps_slice` (`L12JepsDerivDischarge.lean`) — the fake-time
  derivative of the `L₁₂`-zero mode `L₁₂ (J_ε (slice g ·)) (0)`, from the regularity of the
  mollified slices (`SmoothOpen` + `HkMem α 4`) and the pointwise chain-rule/domination data;
* `EpsE4Thr.hasDerivWithinAt_mixed_JfamP_full` (`ProjSlotDerivFull.lean`) — the projection algebra
  turning that into the derivative of a slot of the **projected mollified** family
  `x(τ) = slice (JfamP ρ ε g) τ = Pz (J_ε (slice g τ))`.

The conclusion is the identity that both halves of `AprioriP` consume:

  `∂_τ (mixed j i (x τ) z θ) = mixed j i (Pz (J_ε (epsRHSP τ))) z θ`   (`j + i ≤ 4`).

The only remaining non-elementary input is `hdom` (an `L¹(Ioi 0)` envelope for the `L₁₂`-densities
of the right-hand side, uniform in the fake time), whose construction is described in
`NOTES_EpsE4Thr_session3.md` §3.0.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsDerivDischarge
import Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDerivFull

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

/-- **The slot derivative of the projected mollified family, fully discharged.** -/
theorem hasDerivWithinAt_mixed_JfamP_final {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ} {j i : ℕ}
    (hε : 0 < ε) (hji : j + i ≤ 4) (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hsmR : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0)
    (hsmF : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hsmFR : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ ε Φs E g s))
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
      (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
    (hmemR : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
      (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)))
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
    (hτ : τ ∈ Set.Ioo 0 T)
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
    HasDerivWithinAt (fun s => Work.Spaces.mixed j i (slice (JfamP ρ ε g) s) z θ)
      (Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ))) z θ) (Set.Icc 0 T) τ :=
  hasDerivWithinAt_mixed_JfamP_full (τ := τ) (j := j) (i := i) (g₀ := g₀) hρ hε hji hsol
    hsmF hsmFR hmeas hmeasR hbdd hbddR hcontR hz hθ hτ hintJeps hbdJeps
    (hasDerivWithinAt_L12_Jeps_slice (α := α) (T := T) (Φs := Φs) (E := E) (g₀ := g₀) (g := g)
      hρ hε hsol hsm hsmR hmem hmemR hint hbdU hsliceU hdom hτ)

end Work.FTS.StrongEps.EpsE4Thr
