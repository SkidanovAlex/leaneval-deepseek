import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.L5twoTransitive
import Submission.Work.ThmF.ChV12.L5oddKsub
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.isStronglyEmbeddedOfBruhat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5splitRankOne` — `X = ⟨Q₀,K,t⟩` is a split rank-one group

Peterfalvi II, Ch. V §2, Lemma 5: let `(H,Q,t,s)` satisfy `Hyp5` and let
`X = X5 H t = ⟨Q₀, K, t⟩`.  Then, inside `X`, the subgroup
`B = bor H t = Q₀sub H ⊔ Ksub H t` is a strongly embedded subgroup, `X` acts 2-transitively
on `X ⧸ B`, `tX = t` is an involution outside `B` and `Q₀sub H` is a normal complement of the
two-point stabiliser `B ⊓ B^{tX} = Ksub H t` in `B`:

  `IsSplitRankOne B Q₀sub tX`.

This is the abstract group-theoretic core of Lemma 5; the identification of `X` with a concrete
`PSL(2,2ⁿ)` (and its simplicity) is built on top of it (`L5simpleX5`, `L5zassenhaus`, …).

The proof assembles facts that are proved in the sibling modules:

* `Work.ThmF.L5.X5_eq_borel` (`L5Struct`) and `Work.ThmF.ChV12.bor_subgroupOf_cover` /
  `Work.ThmF.ChV12.L5twoTransitive` (`L5twoTransitive`): the Bruhat decomposition `X = B ∪ B t B`
  and the resulting 2-transitivity of `X` on `X ⧸ B`;
* `Work.ThmF.ChV12.isStronglyEmbeddedOfBruhat`: a group `X = B ∪ B τ B` with `|B|` even,
  `B ≠ X` and `|B ⊓ B^τ|` odd has `B` strongly embedded (the only two-point stabilisers are the
  conjugates of `B ⊓ B^τ`);
* `Work.ThmF.L5.twoPoint_bor_subgroupOf` (`X5RankOneAux`): the two-point stabiliser of `B`
  inside `X` is `Ksub H t`, of odd order (`Work.ThmF.ChV12.L5oddKsub`);
* `Work.ThmF.L5.Q0sub_inf_Ksub_eq_bot`, `Work.ThmF.L5.subgroupOf_inf_eq` and
  `Subgroup.subgroupOf_sup`: `Q₀sub H` is a complement of `Ksub H t` in `B`, normalised by `B`
  (`Work.ThmF.L5.subgroupOf_bor_le_normalizer_subgroupOf`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

theorem L5splitRankOne {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} (hC4 : Submission.Blueprint.ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : Submission.Blueprint.IsSplitRankOne ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) ((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) (Work.ThmF.Lemma5.tX H t) := by
  -- `B ⊓ B^{tX} = Ksub H t` has odd order
  have hodd : Odd (Nat.card ↥(((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) ⊓
      (((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)).map
        (MulAut.conj (Work.ThmF.Lemma5.tX H t)).toMonoidHom))) := by
    show Odd (Nat.card ↥(Submission.Blueprint.twoPoint
      ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
      (Work.ThmF.Lemma5.tX H t)))
    rw [Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := Work.ThmF.Ksub H t) (K := Work.ThmF.Lemma5.X5 H t)
      (Work.ThmF.L5.Ksub_le_X5 (H := H) (t := t))).toEquiv]
    exact L5oddKsub h
  -- `|B|` is even
  have hev : Even (Nat.card ↥((Work.ThmF.L5.bor H t).subgroupOf
      (Work.ThmF.Lemma5.X5 H t))) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := Work.ThmF.L5.bor H t) (K := Work.ThmF.Lemma5.X5 H t)
      (Work.ThmF.L5.bor_le_X5 (H := H) (t := t))).toEquiv) ▸ Work.ThmF.L5.even_card_bor h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `B` is strongly embedded in `X`
    exact isStronglyEmbeddedOfBruhat _ _
      (Work.ThmF.ChV12.bor_subgroupOf_cover hC4 h)
      (Work.ThmF.L5.bor_subgroupOf_ne_top h) hev hodd
  · -- `X` is 2-transitive on `X ⧸ B`
    exact L5twoTransitive hC4 h
  · exact Work.ThmF.L5.orderOf_tX h
  · exact Work.ThmF.L5.tX_notMem_bor h
  · exact Subgroup.subgroupOf_mono _ (le_sup_left : Work.ThmF.Q0sub H ≤ Work.ThmF.L5.bor H t)
  · exact Work.ThmF.L5.subgroupOf_bor_le_normalizer_subgroupOf hC4 h
  · -- `Q₀sub H` is a complement of the two-point stabiliser `Ksub H t`
    rw [Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h]
    rw [← Work.ThmF.L5.subgroupOf_inf_eq]
    rw [Work.ThmF.L5.Q0sub_inf_Ksub_eq_bot h]
    exact Subgroup.bot_subgroupOf _
  · rw [Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h]
    show (Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t) ⊔
        (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) =
      (Work.ThmF.Q0sub H ⊔ Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)
    exact (Subgroup.subgroupOf_sup Work.ThmF.L5.Q0sub_le_X5 Work.ThmF.L5.Ksub_le_X5).symm

end Work.ThmF.ChV12
