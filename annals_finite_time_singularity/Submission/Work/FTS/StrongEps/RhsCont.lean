/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/RhsCont.lean` — the fake-time continuity of the scheme's
# right-hand side along a regular solution

Two bricks of `E5` take, as a hypothesis, the **continuity in the fake time** of the right-hand
side at a point of the quadrant:

* `EpsLimVolterraP` (`EpsLimVolterra.lean`): `hcont` at each approximant (it is what makes the
  fundamental theorem of calculus available for the dominated-convergence passage to the limit);
* `EpsProfileLip_of_epsWP_corr` / `EpsSlotLip` / `EpsSW`: the same `hcont`, consumed to produce the
  τ-Lipschitz property of the approximants' slots;
* at the limit, `hcontR` — the continuity of `s ↦ rhsFun α Φs E g s p`.

This module shows that this hypothesis is **not an extra assumption**: it is a consequence of the
*joint* `C¹`-regularity of the family in `(z,θ,τ)`, which is exactly the first conjunct of
`EpsRegP` (the regularity class of the `P₀`-scheme's solutions, produced by the local step
`LocalStepP` and preserved by the restart gluing `RegGlueP`) and of `EpsLimPkg.c1` at the limit.

The mechanism is elementary: on the open quadrant the τ-partial derivative is the honest
derivative (`Icc_mem_nhds`), the joint `C¹` gives the continuity of the *within*-derivative
(`ContDiffOn.continuousOn_derivWithin` on the interval `Icc 0 T`, which is uniquely
differentiable), and the equation pins the value of that derivative.  The whole content is the
restriction of the joint regularity to a τ-slice, which is `ContDiffOn.comp` with the affine map
`s ↦ ((z,θ), s)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsStructP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The general brick -/

/-- **The fake-time continuity of an equation's right-hand side, from joint `C¹`.**

Let `F` be a family which is jointly `C¹` on the open quadrant times `Icc 0 T`, and which solves
`∂_τ F z θ = R z θ τ` (within `Icc 0 T`) at every point of the open quadrant.  Then for every
`(z,θ)` of the open quadrant the function `τ ↦ R z θ τ` is continuous on `Icc 0 T`.

Proof: the τ-slice `s ↦ F z θ s` is `C¹` on `Icc 0 T` (restriction of the joint regularity), its
within-derivative is continuous there (`ContDiffOn.continuousOn_derivWithin`), and at every
`τ ∈ Icc 0 T` that within-derivative is `R z θ τ` (uniqueness of the within-derivative, the point
being in the interval). -/
theorem continuousOn_rhs_of_contDiffOn_one {F : Fam} {R : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hreg : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (heq : ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (fun s => F z θ s) (R z θ τ) (Set.Icc 0 T) τ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      ContinuousOn (fun τ => R z θ τ) (Set.Icc 0 T) := by
  intro z θ hz hθ
  have hsU : UniqueDiffOn ℝ (Set.Icc 0 T) := uniqueDiffOn_Icc hT
  -- the τ-slice is `C¹` on the interval
  have hslice : ContDiffOn ℝ 1 (fun s : ℝ => F z θ s) (Set.Icc 0 T) := by
    have h1 : ContDiff ℝ 1 (fun _ : ℝ => (z : ℝ)) := contDiff_const
    have h2 : ContDiff ℝ 1 (fun _ : ℝ => (θ : ℝ)) := contDiff_const
    have h3 : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
    have hlin : ContDiff ℝ 1 (fun s : ℝ => (z, (θ, s))) := h1.prodMk (h2.prodMk h3)
    have hcomp : ContDiffOn ℝ 1
        ((fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) ∘ (fun s : ℝ => (z, (θ, s))))
        (Set.Icc 0 T) :=
      hreg.comp hlin.contDiffOn (fun s hs => ⟨hz, hθ, hs⟩)
    exact hcomp.congr (fun s _ => rfl)
  refine (hslice.continuousOn_derivWithin hsU le_rfl).congr (fun τ hτ => ?_)
  exact ((heq z θ τ hz hθ hτ).derivWithin (hsU.uniqueDiffWithinAt hτ)).symm

/-! ## The two instances on the proof path -/

/-- **`hcont` of `EpsLimVolterraP` for a regular `P₀`-solution**: the continuity in the fake time
of the projected scheme's right-hand side.  The inputs are the joint `C¹` of `EpsRegP` and the
scheme's equation `IsEpsSolP`. -/
theorem continuousOn_epsRHSP_of_regP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E_ : Fn → Fn}
    {g₀ : Fn} {g : Fam}
    (hT : 0 < T) (hsol : IsEpsSolP α ρ ε T Φs E_ g₀ g)
    (hreg : EpsRegP α ρ ε T g) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ ε Φs E_ g s p.1 p.2) (Set.Icc 0 T) := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have h := continuousOn_rhs_of_contDiffOn_one (F := g)
    (R := fun z θ τ => epsRHSP α ρ ε Φs E_ g τ z θ) hT hreg.1
    (fun z θ τ hz hθ hτ => hsol.2 z θ τ hz hθ hτ)
  exact h p.1 p.2 hz ⟨hθ0, hθ1⟩

/-- **`hcontR` at the limit**: the continuity in the fake time of `rhsFun` at a limit family, from
the joint `C¹` of the family on the closed τ-interval and the limiting equation `eqT`. -/
theorem continuousOn_rhsFun_of_joint {α T : ℝ} {Φs : Fn} {E_ : Fn → Fn} {g : Fam}
    (hT : 0 < T)
    (hreg : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (heqT : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivWithinAt (fun s : ℝ => g z θ s) (rhsFun α Φs E_ g τ z θ) (Set.Icc 0 T) τ) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => rhsFun α Φs E_ g s p.1 p.2) (Set.Icc 0 T) := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have h := continuousOn_rhs_of_contDiffOn_one (F := g)
    (R := fun z θ τ => rhsFun α Φs E_ g τ z θ) hT hreg
    (fun z θ τ hz hθ hτ => heqT τ hτ.1 hτ.2 z θ ⟨hz, hθ⟩)
  exact h p.1 p.2 hz ⟨hθ0, hθ1⟩

end Work.FTS.StrongEps
