import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.ThreePoints.P3NeBot.p3_appI_one
import Submission.Work.ThreePoints.P3NeBot.oddResidual_basic
import Submission.Work.ThreePoints.P3NeBot.p3b_glue
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3NeBot

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! The lemma exactly as it was requested (recorded verbatim; the two hypotheses `orderOf t = 2`
and `t ∉ H` were written there as anonymous binders — which is not valid Lean syntax, so the
declaration below writes them as `(_ : orderOf t = 2)` and `(_ : t ∉ H)`, an alpha-equivalent
statement):

```lean
/-- Peterfalvi I Ch. II §4 Prop. 3, part 1), conclusion (b): with `X ≠ ⊥`, `X ≤ V = C_D(t)`,
`N_K(X) ≠ 1` and `F = O^{2'}(C_G(X))`, `N_H(X) = S ⋊ N_D(X)` for a Sylow 2-subgroup `S` of
`F ⊓ H`: there is `S` with `S ≤ F ⊓ H`, `¬ 2 ∣ (S.subgroupOf (F ⊓ H)).index`,
`H ⊓ N_G(X) ≤ N_G(S)`, `S ⊓ D = ⊥` and `S ⊔ (D ⊓ N_G(X)) = H ⊓ N_G(X)`.
The source derives it from the structure of `F/Z(F)` (with `F/O_{2'}(F)` a model, obtained from
(B1), available here as `Submission.Blueprint.ThmBBelow (Nat.card G)` inside `hS`; the size
estimate `|F| < |G|` is the lemma `card_F_lt_of_ne_bot` in
`Submission/Work/ThreePoints/_design/P3Induction.lean`).
Do not import any module whose closure still contains `hole`. -/
theorem p3_b {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (orderOf t = 2)
    (t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Work.ThreePoints.p3F X ⊓ H ∧
      ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G) := by hole
```
-/

/-- Peterfalvi I Ch. II §4 Prop. 3, part 1), conclusion (b): with `X ≠ ⊥`, `X ≤ V = C_D(t)`,
`N_K(X) ≠ 1` and `F = O^{2'}(C_G(X))`, `N_H(X) = S ⋊ N_D(X)` for a Sylow 2-subgroup `S` of
`F ⊓ H`: there is `S` with `S ≤ F ⊓ H`, `¬ 2 ∣ (S.subgroupOf (F ⊓ H)).index`,
`H ⊓ N_G(X) ≤ N_G(S)`, `S ⊓ D = ⊥` and `S ⊔ (D ⊓ N_G(X)) = H ⊓ N_G(X)`.
The source derives it from the structure of `F/Z(F)` (with `F/O_{2'}(F)` a model, obtained from
(B1), available here as `Submission.Blueprint.ThmBBelow (Nat.card G)` inside `hS`; the size
estimate `|F| < |G|` is the lemma `card_F_lt_of_ne_bot` in
`Submission/Work/ThreePoints/_design/P3Induction.lean`).
Do not import any module whose closure still contains `hole`. -/
theorem p3_b {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (_ : orderOf t = 2)
    (_ : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Work.ThreePoints.p3F X ⊓ H ∧
      ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G) := by
  exact p3_b_proof hFT hC hA hZJ hBrSz hMod hS hH (by assumption) (by assumption) hX0 hX hNX

end Work.ThreePoints.P3NeBot
