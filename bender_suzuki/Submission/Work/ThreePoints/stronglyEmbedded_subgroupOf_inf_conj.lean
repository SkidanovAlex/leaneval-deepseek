/-
# Peterfalvi I Ch. II §4 Prop. 1 (b): `F ⊓ M` is strongly embedded in `F`

`H` is a strongly embedded subgroup of a finite group `G` in situation (B0)–(B2)
(`Submission.Blueprint.Situation`), `Ω = G ⧸ H` is the set of conjugates of `H`, and for a subgroup
`X` fixing at least three points of `Ω` and a group `F` with `Inv C_G(X) ⊆ F ⊆ N_G(X)` we show
that `F ⊓ M` is strongly embedded in `F` for every fixed point `M = H^g ⊇ X` of `X`
(Peterfalvi I Ch. II §4 Proposition 1 (b), p. 168).

The proof is the source's:

* `Work.ThreePoints.prop1a_of_involution_normalizing` (Ch. II §4 Prop. 1 (a), one application of
  Theorem C `hC`): an involution `u ∈ M` normalising `X` centralises `X`;
* `Work.ThreePoints.exists_involution_normalizer_of_brsz` (the heart of Prop. 1 (a), proved by
  induction on `|X|` using Ch. I §4 Prop. 2 inside `F₁ = C_G(O^p(X))·P`): such an involution
  exists given the Brauer–Suzuki theorem; and `Work.ThreePoints.brauerSuzukiProp_from_cases`
  (area `BrauerSuzuki`, assembled from Dade's and Glauberman's cases) *is* that theorem here, so
  no black box remains;
* `Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj_of_even_card`
  (`Submission/Work/ThreePoints/prop1b_assembly.lean`) — the source's "by Ch. I §2 Lemma 2, (a)
  implies (b)" step: Prop. 1 (a) for every fixed point of `X` gives `|F ⊓ M|` even and `F ⊓ M ≠ F`
  proper, and Ch. I §1 (6) (`IsStronglyEmbedded.subgroupOf_inf`, in `Work.ThreePoints.Omega`)
  then gives the strong embedding.
-/
import Mathlib
import Submission.Work.ThreePoints.prop1b_assembly
import Submission.Work.ThreePoints.prop1a_even_card_centralizer
import Submission.Work.ThreePoints.exists_involution_normalizer_of_brsz
import Submission.Work.ThreePoints.three_involutions_even

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-- Peterfalvi I Ch. II §4 Prop. 1 (b): under (B0)–(B2), if `X` fixes at least three points of
`Ω = G ⧸ H` and `Inv C_G(X) ⊆ F ⊆ N_G(X)`, then for every fixed point `M = H^g ⊇ X` of `X` the
subgroup `F ⊓ M` is strongly embedded in `F` (so `M ↦ F ⊓ M` is a bijection from `Ω_X` onto a
class of proper Bender subgroups of `F`). -/
theorem stronglyEmbedded_subgroupOf_inf_conj {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X F : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hFX : Submission.Blueprint.involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F)
    (hFN : F ≤ Subgroup.normalizer (X : Set G)) {g : G} (hg : X ≤ Submission.Blueprint.conj g H) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ Submission.Blueprint.conj g H).subgroupOf F) :=
  stronglyEmbedded_subgroupOf_inf_conj_of_even_card hH hX3 hFX hg
    (fun hX3' hM' hXM' =>
      prop1a_of_involution_normalizing hC hS hH hX3' hM' hXM'
        (exists_involution_normalizer_of_brsz hFT hC hA brauerSuzukiProp_from_cases hS
          hH hX3' hM' hXM'))

end Work.ThreePoints
