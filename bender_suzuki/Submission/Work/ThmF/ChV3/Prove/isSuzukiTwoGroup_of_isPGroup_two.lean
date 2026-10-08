import Mathlib
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V §1, Corollary of Prop. 2: the non-abelian `2`-group case

In situation (B0)–(B2) (`Situation G`, with the odd order theorem `FeitThompsonProp` and Ch. II §4
Prop. 4 `ChIIFourProp` available) let `H = Q ⋊ D` be split rank-one data for an involution
`t ∉ H`, `D = H ∩ H^t`.  If `Q` is a `2`-group and `Q` is not abelian, then `Q` is a Suzuki
two-group in Higman's sense (`Submission.Blueprint.IsSuzukiTwoGroup`).

The paper's Corollary of Prop. 2 reads "the Sylow `2`-subgroup `S` of `Q` is abelian or is a
Suzuki `2`-group".  Here `Q` *is* a `2`-group, so the only Sylow `2`-subgroup of `Q` is `Q`
itself, and the non-abelian alternative of the corollary is the one that applies.

Concretely:

* `K = J(D,t)` is cyclic and `Ksub H t = Kset H t` (Ch. V §1 Prop. 2,
  `Work.ThmF.ChV12.Ksub_cyclic_normal`, using `FeitThompsonProp`);
* `K` acts regularly on `Inv(H)` (Ch. I §2, `Work.ThmF.L5.Kset_regular`), so the cyclic group
  `K` acts on `Q` by conjugation (`K ≤ H ≤ N_G(Q)`) with the powers of one generator transitive
  on the involutions of `Q`;
* `Inv(H)` has at least two elements (`Work.ThmF.Bender.cardInvGeTwo`) and lies in `Q`
  (Ch. V §1 Prop. 1 (c), `Work.ThmF.ChV12.prop1c`: the involutions of `H` are central in the
  nilpotent group `Q`), so `Q` has at least two involutions.

These are exactly the hypotheses of `Work.ThmF.ChV12.isSuzukiTwoGroup_of_Ksub_cyclic`, which
concludes.
-/

namespace Work.ThmF.ChV3.Prove

theorem isSuzukiTwoGroup_of_isPGroup_two {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hS : Submission.Blueprint.Situation G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hSp : IsPGroup 2 ↥Q) (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Submission.Blueprint.IsSuzukiTwoGroup ↥Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Ch. V §1 Prop. 2: `K = J(D,t)` is cyclic and `Ksub H t = Kset H t`.
  obtain ⟨hKcyc, hKset, -⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS h
  -- `Q` is a `2`-group, hence nilpotent.
  have hnil : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent hSp
  -- `D = H ∩ H^t` acts transitively on `Inv(H)` (strong embeddedness).
  have hDtrans : ∀ a ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ b ∈ Submission.Blueprint.involutions (H : Set G),
      ∃ d ∈ Submission.Blueprint.twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv h.stronglyEmbedded h.invol h.not_mem
  -- Ch. V §1 Prop. 1 (c): the involutions of `H` are central in `Q`, hence lie in `Q`.
  have hInv_le : Submission.Blueprint.involutions (H : Set G) ⊆
      Submission.Blueprint.involutions (Q : Set G) := fun u hu =>
    ⟨(Work.ThmF.mem_centerOf.mp (Work.ThmF.ChV12.prop1c hS H Q t h hDtrans hnil u hu)).1, hu.2⟩
  -- `|Inv(H)| ≥ 2` (four-group of (B0)) and `Inv(H) ⊆ Inv(Q)`.
  have hcard : 2 ≤ (Submission.Blueprint.involutions (Q : Set G)).ncard :=
    le_trans (Work.ThmF.Bender.cardInvGeTwo h.stronglyEmbedded hS.1.1)
      (Set.ncard_le_ncard hInv_le)
  -- `K ≤ H` normalises `Q`, so `K` acts on `Q`.
  have hStab : ∀ k ∈ Work.ThmF.Ksub H t, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := by
    intro k hk x hx
    have hkH : k ∈ H := (Subgroup.mem_inf.mp (Work.ThmF.Ksub_le_twoPoint (H := H) t hk)).1
    exact (Subgroup.mem_normalizer_iff.mp (h.normal hkH) x).mp hx
  -- `K = Kset H t` is transitive on `Inv(H)` (Ch. I §2).
  have hKtrans : ∀ a ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ b ∈ Submission.Blueprint.involutions (H : Set G),
      ∃ k ∈ Work.ThmF.Kset H t, k * a * k⁻¹ = b := by
    intro a ha b hb
    obtain ⟨k, hk, -⟩ := Work.ThmF.L5.Kset_regular h a ha b hb
    exact ⟨k, hk.1, hk.2⟩
  exact Work.ThmF.ChV12.isSuzukiTwoGroup_of_Ksub_cyclic H t Q h.le hSp hStab hcard hnab
    hKcyc hKset hKtrans

end Work.ThmF.ChV3.Prove
