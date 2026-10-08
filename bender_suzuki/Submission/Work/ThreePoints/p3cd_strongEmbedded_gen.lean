import Mathlib
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.P3NeBot.p3_b_aux
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.DoubleTransitivity.Sec4.prop2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.p3cd_strongEmbedded_gen`

Peterfalvi I Ch. II §4 **Prop. 1 (b)** at `F = F₁ = O^{2'}(C_G(X))`: with `X ≠ 1`,
`X ≤ V = C_D(t)` (`D = H ⊓ H^t`, `H` strongly embedded, `t ∉ H` an involution) and
`N_K(X) ≠ 1` (`K = J(D,t)`), the subgroup `F ⊓ M` is strongly embedded in `F` for **every**
conjugate `M = H^g` of `H` containing `X` (the special case `M = H` is
`Work.ThreePoints.p3cd_strongEmbedded`).

The argument is the source's, in two steps.

* The evenness input of Prop. 1 (b) — `|M ⊓ C_G(X)|` even for every conjugate `M ⊇ X` — is
  Ch. II §4 Prop. 1 (a), i.e.
  `Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz`, applied with the
  Ch. I §4 Prop. 2 input (`hS4`).  In the sibling file `Work.ThreePoints.p3cd_strongEmbedded`
  that input is `p3cd_s4prop2`; here it is built directly from
  `Work.DoubleTransitivity.Sec4.prop2`, the unconditional Ch. I §4 Prop. 2 in the form
  `MaxFixesThreeIn p K Q → Even |N_G(Q) ⊓ K|` (Peterfalvi I §4 Lemma 1/Lemma 2 + Prop. 1/Prop. 2
  and Ch. I §3 Prop. 1, with `hBrSz` as its only external input).
* Prop. 1 (b) itself, once evenness is known at all the conjugates of `H` containing `X`, is
  `Work.ThreePoints.Prop1aBrSz.stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at`
  (Ch. I §2 Lemma 2: evenness at the fixed points of `X` plus a single class of proper Bender
  subgroups).

The remaining hypotheses the request supplies (`hA`, `hZJ`, `hMod`, `hX0`, `hNX`) enter only via
the parts of the source's Ch. II §4 Prop. 3 that are not used here; `X ≠ ⊥` together with
`N_K(X) ≠ 1` are the paper's standing hypotheses which ensure that `F = O^{2'}(C_G(X))` is a
proper subgroup of 2-rank `≥ 2` (so that its Bender subgroups are the proper ones).
-/

namespace Work.ThreePoints

open Submission.Blueprint

/-- Every involution of `C_G(X)` lies in `F = O^{2'}(C_G(X))`: an involution generates a
`2`-subgroup, and the quotient of `C_G(X)` by `O^{2'}` has odd order. -/
theorem involutions_subset_p3F {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ p3F X := by
  rintro u ⟨hu, hu2⟩
  change u ∈ p3F X
  rw [mem_p3F]
  refine ⟨⟨u, hu⟩, ?_, rfl⟩
  exact involution_mem_oddResidual
    (x := (⟨u, hu⟩ : ↥(Subgroup.centralizer (X : Set G))))
    (Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2))

theorem p3cd_strongEmbedded_gen {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∀ M : Subgroup G, X ≤ M → (∃ g : G, M = Submission.Blueprint.conj g H) →
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded
        ((Work.ThreePoints.p3F X ⊓ M).subgroupOf (Work.ThreePoints.p3F X)) := by
  -- **Peterfalvi I Ch. I §4 Prop. 2**, in the form consumed by Ch. II §4 Prop. 1 (a)
  -- (the `hS4` input of `even_card_centralizer_of_fixes_three_brsz`).
  have hS4 : ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
    intro F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax
    -- `Q` is maximal among the `p`-subgroups of `F` with at least three fixed points
    have hMaxIn : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
      ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => (hQmax R hQR hRK hRp hR3) ▸ le_rfl⟩
    obtain ⟨-, hEven⟩ := Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hMaxIn
    -- `|N_K(Q)| = |K ⊓ N_F(Q)|`
    have hEven' : Even (Nat.card ↥(K ⊓ Subgroup.normalizer (Q : Set F) : Subgroup F)) := by
      simpa only [inf_comm] using hEven
    rw [Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hQK]
    exact hEven'
  -- `X ≤ C_D(t)` fixes at least three points of `Ω = G ⧸ H`
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  intro M hXM hM
  -- **Peterfalvi I Ch. II §4 Prop. 1 (b)** at `F = O^{2'}(C_G(X))`
  refine Work.ThreePoints.Prop1aBrSz.stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at
    (F := Work.ThreePoints.p3F X) (M := M) hH hX3 (involutions_subset_p3F X) hXM hM ?_
  -- the evenness of Ch. II §4 Prop. 1 (a) at every fixed point of `X`
  intro M' hM' hXM'
  exact Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC hS4 hS
    hH hX3 hM' hXM'

end Work.ThreePoints
