/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/ProjSlotDerivFull.lean` — the projected slot derivative,
fully assembled

This is the end of the chain that produces the fake-time derivative of a slot of the **projected
mollified** family `x(τ) = slice (JfamP ρ ε g) τ = Pz (J_ε (slice g τ))`:

  `∂_τ (mixed j i (x τ) z θ) = mixed j i (Pz (J_ε (epsRHSP … τ))) z θ`   (`j + i ≤ 4`),

with **every** input discharged except the single analytic brick `hL12`
(`EpsE4Thr.L12_Jeps_deriv`: the fake-time derivative of the `L₁₂`-zero mode) and the standard
domination data:

* the raw slot chain rule `mixed_slice_deriv_at` (proved) — from the Volterra identity
  `epsSol_eq_integralP` + the slot exchange `EpsSlotAux.mixed_intervalIntegralEq` + the FTC;
* the mollifier differentiation `Jeps_family_deriv` (proved);
* the algebra of the projection `mixed_Pz_Jeps_eq` / `hasDerivWithinAt_mixed_JfamP` (proved).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.MixedSliceDerivAt
import Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDerivRaw

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

/-- **The slot derivative of the projected mollified family, fully assembled.**  The only
non-elementary inputs are the slot domination data (`hbdd`/`hbddR` on compact subsets of the open
quadrant, `hbddR` also on the kernel image), the continuity of the RHS slot in the fake time
(`hcontR`), the two integrability/boundedness inputs of the mollifier differentiation
(`hint`/`hbd`), and the `L₁₂`-zero-mode derivative `hL12`. -/
theorem hasDerivWithinAt_mixed_JfamP_full {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ} {j i : ℕ}
    (hε : 0 < ε) (hji : j + i ≤ 4)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsm : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hsmR : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ ε Φs E g s))
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
    (hint : ∀ s ∈ Set.Icc 0 T, Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p * Work.Spaces.mixed j i (slice g s)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) volume)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
      |Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hL12 : HasDerivWithinAt
      (fun s => Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0)
      (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ)) 0) (Set.Icc 0 T) τ) :
    HasDerivWithinAt (fun s => Work.Spaces.mixed j i (slice (JfamP ρ ε g) s) z θ)
      (Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ))) z θ) (Set.Icc 0 T) τ :=
  hasDerivWithinAt_mixed_JfamP_raw (τ := τ) (j := j) (i := i) (g₀ := g₀) hρ hε
    (fun s hs n => (Work.FTS.EllipticEst.smoothOpen_iff_forall (slice g s)).mp (hsm s hs) n)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (epsRHSP α ρ ε Φs E g τ)).mp
      (hsmR τ ⟨hτ.1.le, hτ.2.le⟩))
    hz hθ hji hτ
    (fun s hs y φ hy hφ => mixed_slice_deriv_at (j := j) (i := i) hρ hε hsol hji
      hsm hsmR hmeas hmeasR hbdd hbddR (fun z' θ' hz' hθ' =>
        hcontR z' θ' hz' hθ') hs y φ hy hφ)
    hint hbd hL12

end Work.FTS.StrongEps.EpsE4Thr
