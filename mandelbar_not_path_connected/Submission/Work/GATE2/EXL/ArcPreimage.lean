/-
# GATE2 / EXL — the equipotential arc lifts into the far-left half plane (case (ii), step 1)

This is step (N-esc) ⟹ "the arc is in the domain of `Ψ⁻¹`" of
`NOTES_LEAD_mandelbar_gaps3.md` §2.2 (b).

In case (ii) the real axis misses both ray lifts, so the exit loop of the design is built on the
**equipotential arc** `θ ↦ rayPt θ (exp p)` at a small potential `p` (through the deep equator tail
in `pairSideNear P0 ∩ pairSideNear (Q n)`), which must be lifted back to the `Ψ`-plane through
`Ψ⁻¹` — legal only where `Ψ` is injective, i.e. on the far-left half plane `{Re < -R}`
(`RayCylLift.hinj`).

The lift is produced pointwise by `ParabolicFlower.cover`: every point within `Rc` of `z₁` is either
in the petal `Pa` or is the `Ψ`-image of a point of `{Re < -R}`.  The petal case is excluded because
`Pa ⊆ K c` (`Work.ELRig.Pa_subset_K`) has potential `0`, while the arc has potential `p > 0`; and
the arc lies within `Rc` of `z₁` by the nest shrinking `shrinks_esc` (`hsmall`).

So: the only inputs are the nest shrinking at the level `n`, the two side-memberships of the arc,
and the cover statement.
-/
import Submission.Work.GATE2.Inputs
import Submission.Work.ELRig.Pa_subset_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The equipotential arc at a small potential lifts into `{Re < -R}`.**  For the arc
`θ ↦ rayPt d.hN θ (exp p)`, `θ ∈ [θ₀, α₁)`, if the arc lies in both near sides `pairSideNear P0`,
`pairSideNear Q` and the nest region at potential `< g` lies within `Rc` of `z₁` (`shrinks_esc`),
then every point of the arc is a `Ψ`-image of the far-left half plane. -/
theorem arc_mem_preimage {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (Q : Work.EL.CoPair d.hN)
    {R θ₀ p g Rc : ℝ} (hp : 0 < p) (hpg : p < g)
    (hsmall : ∀ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 → z ∈ Work.EL.pairSideNear Q →
      Work.EL.pot d.hN z < g → ‖z - d.z₁‖ < Rc)
    (hcover : ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < Rc →
      z ∈ fl.Pa ∨ ∃ w : ℂ, w.re < -R ∧ fl.Ψ w = z)
    (hz1 : Work.EL.pot d.hN d.z₁ = 0)
    (hside₁ : ∀ θ ∈ Set.Ico θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ Work.EL.pairSideNear nest.P0)
    (hside₂ : ∀ θ ∈ Set.Ico θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ Work.EL.pairSideNear Q) :
    ∀ θ ∈ Set.Ico θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ fl.Ψ '' {w : ℂ | w.re < -R} := by
  intro θ hθ
  set z : ℂ := Work.EL.rayPt d.hN θ (Real.exp p) with hz
  have hexp1 : (1 : ℝ) < Real.exp p := by
    rw [Real.one_lt_exp_iff]; exact hp
  have hpot : Work.EL.pot d.hN z = p := by
    rw [hz, Work.EL.pot_rayPt d.hN hexp1, Real.log_exp]
  have hne : z ≠ d.z₁ := by
    intro hcon
    have h0 : Work.EL.pot d.hN z = 0 := by rw [hcon]; exact hz1
    rw [hpot] at h0
    linarith
  have hdist : ‖z - d.z₁‖ < Rc :=
    hsmall z (hside₁ θ hθ) (hside₂ θ hθ) (by rw [hpot]; exact hpg)
  rcases hcover z hne hdist with hmem | ⟨w, hw, hΨ⟩
  · have h0 : Work.EL.pot d.hN z = 0 :=
      Work.EL.pot_of_mem d.hN (Work.ELRig.Pa_subset_K fl hmem)
    rw [hpot] at h0
    linarith
  · exact ⟨w, hw, hΨ⟩

end Work.GATE2.EXL
