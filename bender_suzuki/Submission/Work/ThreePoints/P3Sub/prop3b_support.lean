import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.P3Sub.prop2c
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Support lemmas for `prop3b_normal_sylow`

Peterfalvi I Ch. II §4 Prop. 1 (a), (b) with `F = p3F X = O^{2'}(C_G(X))`, in the form the
transfer step of Prop. 3 (b) needs: `|M ⊓ C_G(X)|` is even for every fixed point `M = H^g` of
`X`, and `F ⊓ M` is strongly embedded in `F`.

Both are instances of the general Prop. 1 (a), (b) from `Work.ThreePoints.Prop1aBrSz`, with
Ch. I §4 Prop. 2 supplied by `Work.ThreePoints.P3Sub.ch1_s4_prop2_of_brsz`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- Peterfalvi I Ch. II §4 Prop. 1 (a): for `X ≤ H` fixing at least three points of `Ω = G ⧸ H`
and a fixed point `M = H^g ⊇ X`, the centraliser `C_M(X)` has even order. -/
theorem even_card_inf_centralizer_of_fixes_three
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (fixedPts H X).ncard)
    (hM : ∃ g : G, M = conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC
    (P3Sub.ch1_s4_prop2_of_brsz hBrSz) hS hH hX3 hM hXM

/-- Peterfalvi I Ch. II §4 Prop. 1 (b): `F ⊓ M` is strongly embedded in `F` for every fixed point
`M = H^g ⊇ X` of `X`, when `Inv C_G(X) ⊆ F`; here `F = p3F X = O^{2'}(C_G(X))`. -/
theorem stronglyEmbedded_p3F_inf_conj
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (fixedPts H X).ncard)
    (hM : ∃ g : G, M = conj g H) (hXM : X ≤ M) :
    IsStronglyEmbedded ((p3F X ⊓ M).subgroupOf (p3F X)) :=
  Prop1aBrSz.stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at (F := p3F X)
    hH hX3 (fun u hu => mem_p3F_of_involution hu.1 hu.2) hXM hM
    (fun M' hM' hXM' => even_card_inf_centralizer_of_fixes_three hFT hC hBrSz hS hH hX3 hM' hXM')

/-- The two-point stabiliser `p3F X ⊓ H` is strongly embedded in `p3F X`, for `X ≤ V`. -/
theorem stronglyEmbedded_p3F_inf_H
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t) :
    IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X)) :=
  stronglyEmbedded_p3F_inf_conj hFT hC hBrSz hS hH
    (three_le_ncard_fixedPts_of_le_centD hH ht htH hX) ⟨1, (conj_one H).symm⟩
    ((le_of_le_centD hX).1)

end Work.ThreePoints
