/-
# A1 — the nest-angle lemma of §2.2, in the form consumed by GATE

`Work.GATE.Nest.ray_angle_of_near_sides` is `A1` up to the angular *nesting* of the level-`n`
pair of the `z₁`-nest: a point of the nest region off the filled Julia set has its dynamical ray
in the near arcs of both the `α`-pair and the nest pair, hence (the near arcs being
`[α₂, α₁ + 1]` and `[βₙ, β'ₙ]` with `βₙ < α₁ < α₂ < β'ₙ`) its angle lies in
`[βₙ, α₁] ∪ [α₂, β'ₙ]`.

Here the nest data is instantiated by the *angle facts of the certificate*: for the level-`n`
pair `Qp n = (β'ₙ, βₙ + 1)` of `Work.ELNest`, `βₙ ∈ (β₀, α₁)` and `β'ₙ ∈ (α₂, β'₀)`
(`Work.ELNest.bAng_range`), so that for every `δ > 0` and `n` large enough the windows
`(α₁ - δ, α₁]` and `[α₂, α₂ + δ)` contain the conclusion.  This is the form `A1` has in
`Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §2.2.
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Nest.ray_angle_of_near_sides

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE.Nest

/-- **A1, in the `δ`-window form of §2.2.**  If the level-`n` pair of the nest `Q` has its two
angles `β + 1` (near `α₁ + 1`) and `β'` (near `α₂`) inside the `δ`-windows of `α₁` and `α₂`
hypotheses `α₁ - δ < β` and `β' < α₂ + δ`), then every point of the nest region off `K c` has a
dynamical ray whose angle lies in `(α₁ - δ, α₁] ∪ [α₂, α₂ + δ)`: the *near side* angle lemma of
the equatorial-rigidity design. -/
theorem nest_angle_window {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P0 Q : Work.EL.CoPair hN) {β β' δ : ℝ}
    (hP0a : P0.a = Work.EL.alpha1) (hP0b : P0.b = Work.EL.alpha2)
    (hQa : Q.a = β') (hQb : Q.b = β + 1)
    (hβ : 0 < β) (hβ₁ : β < Work.EL.alpha1) (h₁₂ : Work.EL.alpha1 < Work.EL.alpha2)
    (h₂β' : Work.EL.alpha2 < β') (hβ'1 : β' < 1)
    (hPs : Work.EL.PairSides hN P0) (hQs : Work.EL.PairSides hN Q)
    (hcover : ∀ z ∉ Work.EL.K c, ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ)
    {z : ℂ} (hzK : z ∉ Work.EL.K c)
    (hzP : z ∈ Work.EL.pairSideNear P0) (hzQ : z ∈ Work.EL.pairSideNear Q)
    (hδ₁ : Work.EL.alpha1 - δ < β) (hδ₂ : β' < Work.EL.alpha2 + δ) :
    ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ ∧
      ((Work.EL.alpha1 - δ < ϑ ∧ ϑ ≤ Work.EL.alpha1) ∨
        (Work.EL.alpha2 ≤ ϑ ∧ ϑ < Work.EL.alpha2 + δ)) := by
  obtain ⟨ϑ, hϑ, h⟩ :=
    ray_angle_of_near_sides (hN := hN) (P0 := P0) (Q := Q) (β := β) (β' := β')
      hP0a hP0b hQa hQb hβ hβ₁ h₁₂ h₂β' hβ'1 hPs hQs hcover hzK hzP hzQ
  refine ⟨ϑ, hϑ, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by linarith, h2⟩
  · exact Or.inr ⟨h1, by linarith⟩

end Work.GATE.Nest
