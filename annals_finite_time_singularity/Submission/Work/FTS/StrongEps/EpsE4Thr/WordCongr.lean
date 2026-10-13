/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/WordCongr.lean` — congruence of `H1IP` and of the
energy derivative on the open quadrant

Both halves of `AprioriP` reduce their energy identities to slot-level facts, and the slot-level
facts are stated for the *canonical* slot words `mixed j i = D_z^j D_θ^i`, while `EnergyStep`'s
recursion shifts its family by `D_θ` and `D_z` (so the words it produces are arbitrary
compositions, cf. `WordEnergy.lean`).  Comparing the two requires rewriting a slot profile which
only agrees with another on the **open quadrant** `Q0 = (0,∞) × (0,π/2)`.

This module provides the congruence lemmas that make that rewriting possible:

* `wip_congr_Q0_fst` — `wip` in its *first* argument (the upstream
  `CoercivityStep.Base.wip_congr_Qd`);
* `wip_congr_Q0_snd` — `wip` in its *second* argument, from the symmetry of `wip`;
* `wip_congr_Q0_both` — `wip` in both arguments at once;
* `H1IP_congr_Q0` — `H1IP α f g = H1IP α f' g'` whenever `f = f'` and `g = g'` on `Q0`;
* `EnergyDeriv_congr` — `EnergyDeriv` is insensitive to replacing the family and its derivative by
  pointwise-`Q0`-equal ones near `τ`.

(The proof of `H1IP_congr_Q0` is written out here rather than imported from
`StrongEps.IP6_Jeps_comm`, because the latter redeclares `Work.FTS.StrongEps.smoothOpen_Jeps` and
can therefore not be imported alongside the `JepsSmoothOpen` cone.)

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongPersist.EnergyIter
import Submission.Work.FTS.CoercivityStep.Base.H1IP_congr_qd
import Submission.Work.FTS.CoercivityStep.Base.H1IP_symm

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

/-- **`wip` only sees its two profiles on the open quadrant** (first argument). -/
theorem wip_congr_Q0_fst {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → A z θ = A' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B :=
  Work.FTS.CoercivityStep.Base.wip_congr_Qd h

/-- **`wip` only sees its two profiles on the open quadrant** (second argument), from the symmetry
of `wip`. -/
theorem wip_congr_Q0_snd {ρ A B B' : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → B z θ = B' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A B' := by
  rw [Work.FTS.CoercivityStep.Base.wip_comm ρ A B,
    Work.FTS.CoercivityStep.Base.wip_comm ρ A B']
  exact Work.FTS.CoercivityStep.Base.wip_congr_Qd
    (ρ := ρ) (A := B) (A' := B') (B := A) h

/-- **`wip` only sees its two profiles on the open quadrant** (both arguments). -/
theorem wip_congr_Q0_both {ρ A A' B B' : ℝ → ℝ → ℝ}
    (hA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → A z θ = A' z θ)
    (hB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → B z θ = B' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B' := by
  rw [wip_congr_Q0_fst (ρ := ρ) hA, wip_congr_Q0_snd (ρ := ρ) (A := A') hB]

/-- **`H1IP` only sees its two profiles on the open quadrant** (both arguments at once). -/
theorem H1IP_congr_Q0 (α : ℝ) {f f' g g' : ℝ → ℝ → ℝ}
    (hf : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → f z θ = f' z θ)
    (hg : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → g z θ = g' z θ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α f' g' := by
  have hDz := Work.FTS.CoercivityStep.Base.Dz_congr_Qd hf
  have hDz' := Work.FTS.CoercivityStep.Base.Dz_congr_Qd hg
  have hDth := Work.FTS.CoercivityStep.Base.Dth_congr_Qd hf
  have hDth' := Work.FTS.CoercivityStep.Base.Dth_congr_Qd hg
  simp only [Work.Coercivity.H1IP]
  have h1 := wip_congr_Q0_both
    (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) hDz hDz'
  have h2 := wip_congr_Q0_both
    (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) hf hg
  have h3 := wip_congr_Q0_both (ρ := fun z _ => Work.Spaces.w z ^ 2) hf hg
  have h4 := wip_congr_Q0_both
    (ρ := fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) hDth hDth'
  rw [h1, h2, h3, h4]

/-- **`EnergyDeriv` is a pointwise-on-`Q0` statement near `τ`.** -/
theorem EnergyDeriv_congr {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {u u' : ℝ → Fn} {udot udot' : Fn}
    {τ : ℝ} (h : Work.FTS.StrongPersist.EnergyDeriv IP u udot τ)
    (h1 : ∀ᶠ s in 𝓝 τ, IP (u s) (u s) = IP (u' s) (u' s))
    (h2 : IP udot (u τ) = IP udot' (u' τ)) :
    Work.FTS.StrongPersist.EnergyDeriv IP u' udot' τ := by
  have hfun : (fun s => IP (u' s) (u' s)) =ᶠ[𝓝 τ] (fun s => IP (u s) (u s)) :=
    h1.mono fun s hs => hs.symm
  have hval : 2 * IP udot' (u' τ) = 2 * IP udot (u τ) := by rw [← h2]
  show HasDerivAt (fun s => IP (u' s) (u' s)) (2 * IP udot' (u' τ)) τ
  rw [hval]
  exact h.congr_of_eventuallyEq hfun

end Work.FTS.StrongEps.EpsE4Thr
