import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.ZassenhausSuzuki.frel_torus_inv
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Suzuki reflection map `∼` of the root group, in the group picture

This module fixes the vocabulary of the Baumeister–Grüninger §5.13–5.14 computation of
`Fix θ = 𝔽₂` (see `Submission/Work/ZassenhausSuzuki/szClassNumber_fixTheta.lean`).

* `szCanon hsplit` — a chosen instance of the canonical structure maps
  (`Work.ZassenhausPSL2.Canon`: `t * x * t = g x * h x * t * f x` for `x ∈ Q#`).
* `szTilde hsplit` — **BG's reflection map** `∼ : Q → Q`.  In the source (BG 3.1 (j))
  `∼ a = τ (-(τ⁻¹ a))` where `τ = t` acts on the points `X ∖ {0,∞} = Q` and `-` is the group
  inverse ("negation") of `Q`; the Weyl involution acts on those points by `x ↦ g x`
  (`Work.RankOneUniqueness.ChkTSmul` gives `t • qPt x = qPt (f (x⁻¹))⁻¹` and
  `canon_relations` H1 gives `f (x⁻¹) = (g x)⁻¹`).  Hence `∼ a = g (g a)⁻¹`; the value at
  `a = 1` is set to `1` by convention.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **The canonical structure maps of the configuration**: a chosen instance of
`Work.ZassenhausPSL2.Canon` (existence: `Work.ZassenhausPSL2.canon_exists`); recall
`t * x * t = (g x) * (h x) * t * (f x)` for `x ∈ Q#`. -/
noncomputable def szCanon {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) : Work.ZassenhausPSL2.Canon H Q t :=
  Classical.choice (Work.ZassenhausPSL2.canon_exists hsplit)

/-- **The Suzuki reflection map** `∼` on the root group: `∼ x = g (g x)⁻¹` (BG 3.1 (j));
the value at `x = 1` is `1` by convention (the natural extension). -/
noncomputable def szTilde {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) : Q → Q := by
  classical
  exact fun x => if (x : G) = 1 then 1 else (szCanon hsplit).g ((szCanon hsplit).g x)⁻¹

end Work.ZassenhausSuzuki
