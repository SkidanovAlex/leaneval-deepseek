import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV12.oddPart_inf_centralizer_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.cQNormalizerIsPGroupTwo`

In the standing context of Peterfalvi II Ch. V §3 ((B0)–(B2) — `Situation` — plus the split
rank-one datum `H = Q ⋊ D`, `D = H ⊓ H^t`) let `X ≤ V = C_D(t)`, `X ≠ ⊥`, be normalised by a
non-trivial element `k ∈ K = J(D,t) = {x ∈ D | x^t = x⁻¹}`.  Then the part of `Q` normalising `X`
is a 2-group:

  `IsPGroup 2 ↥(Q ⊓ N_G(X))`.

The proof is the counting half of Ch. II §4 Prop. 3.  The P3 clause of `ChIIFourProp` gives a
2-subgroup `S ≤ H` with

  `S ⊓ D = ⊥`,  `S ⊔ (D ⊓ N_G(X)) = H ⊓ N_G(X)`,  `H ⊓ N_G(X) ≤ N_G(S)`

(and `S ⊓ D = ⊥`, where `D = twoPoint H t`).  Both `A := Q ⊓ N_G(X)` and `T := D ⊓ N_G(X)` are
subgroups of `U := H ⊓ N_G(X) = S ⊔ T` with `A ⊓ T = ⊥` (because `Q ⊓ D = ⊥`), and `T`
normalises both `S` (from `H ⊓ N_G(X) ≤ N_G(S)`) and `A` (it lies in `D ≤ H ≤ N_G(Q)` and in
`N_G(X) ≤ N_G(N_G(X))`).  The product formula `|S ⊔ T| · |S ⊓ T| = |S| · |T|` of
`Work.PGroup.card_sup_mul_card_inf_of_le_normalizer` then yields `|A| ∣ |S|` — assembled as
`Work.ThmF.ChV12.card_dvd_pow_two_of_sup_inf` — and `S` is a 2-group, so `|A| ∣ 2ⁿ` and `A` is a
2-group.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.Prove

theorem cQNormalizerIsPGroupTwo {G : Type} [Group G] [Finite G] {H Q X : Subgroup G} {t : G}
    (hSit : Submission.Blueprint.Situation G) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hX : X ≤ Submission.Blueprint.centD H t) (hX0 : X ≠ ⊥)
    (hk : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    IsPGroup 2 ↥(Q ⊓ Subgroup.normalizer (X : Set G)) := by
  -- Ch. II §4 Prop. 3 (the P3 clause of `ChIIFourProp`), applied to `X` and `k ∈ K#`.
  have hP3 := (hC4 G hSit H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.2.2.1
  obtain ⟨S, hSp, _hSFH, _hIdx, hSnorm, hSD, hSsup⟩ := (hP3 X hX0 hX hk).2.1
  -- `D = H ⊓ H^t` is contained in `H`.
  have hD_le_H : twoPoint H t ≤ H := fun x hx => (Subgroup.mem_inf.mp hx).1
  -- `T = D ⊓ N_G(X)` is contained in `H ⊓ N_G(X)`, hence normalises `S`.
  have hT_le_U : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
      H ⊓ Subgroup.normalizer (X : Set G) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hD_le_H hx1, hx2⟩
  have hTS : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (S : Set G) := le_trans hT_le_U hSnorm
  -- `S ⊓ T = ⊥`.
  have hST : S ⊓ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = ⊥ := by
    rw [← inf_assoc, hSD, bot_inf_eq]
  -- `A ⊓ T = ⊥` because `A ≤ Q` and `T ≤ D` with `Q ⊓ D = ⊥`.
  have hAT : (Q ⊓ Subgroup.normalizer (X : Set G)) ⊓
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxA, hxT⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxQ, -⟩ := Subgroup.mem_inf.mp hxA
    obtain ⟨hxD, -⟩ := Subgroup.mem_inf.mp hxT
    exact (le_of_eq hsplit.inf_eq) (Subgroup.mem_inf.mpr ⟨hxQ, hxD⟩)
  -- `T` normalises `A = Q ⊓ N_G(X)`: it lies in `N_G(Q)` and in `N_G(X) ≤ N_G(N_G(X))`.
  have hTA : (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.normalizer (X : Set G)) : Set G) := by
    have h1 : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (Q : Set G) := fun g hg =>
      hsplit.normal (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
    have h2 : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer ((Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  -- `A ≤ U` because `Q ≤ H`.
  have hAU : Q ⊓ Subgroup.normalizer (X : Set G) ≤
      H ⊓ Subgroup.normalizer (X : Set G) := by
    intro x hx
    obtain ⟨hxQ, hxX⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hsplit.le hxQ, hxX⟩
  -- The counting lemma: `|Q ⊓ N_G(X)| ∣ 2ⁿ`.
  obtain ⟨n, hn⟩ := Work.ThmF.ChV12.card_dvd_pow_two_of_sup_inf (S := S)
    (T := twoPoint H t ⊓ Subgroup.normalizer (X : Set G))
    (A := Q ⊓ Subgroup.normalizer (X : Set G))
    (U := H ⊓ Subgroup.normalizer (X : Set G)) hSsup hST hTS hAT hTA hAU hSp
  exact IsPGroup.of_card_dvd_pow hn

end Work.ThmF.Prove
