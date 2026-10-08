import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.F1EqF.prop2c_of_even
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3Sub

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156) in the general form consumed by Ch. II §4
Prop. 1 (a): for a finite group `F`, a strongly embedded `K ≤ F`, a prime `p ≠ 2` and a
`p`-subgroup `Q ≤ K` maximal among the `p`-subgroups of `K` with at least three fixed points of
`F ⧸ K`, the normaliser of `Q` in `K` has even order.

This is `Work.DoubleTransitivity.Sec4.prop2` (which already covers both `2`-rank cases, using
Brauer–Suzuki), transported across the identification `N_K(Q) ≅ K ⊓ N_F(Q)`
(`Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf`). -/
theorem ch1_s4_prop2_of_brsz (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  intro F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax
  have hMF : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => (hQmax R hQR hRK hRp hR3).le⟩
  have heven : Even (Nat.card ↥(Subgroup.normalizer (Q : Set F) ⊓ K)) :=
    (Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hMF).2
  have hcard : Nat.card ↥(K ⊓ Subgroup.normalizer (Q : Set F)) =
      Nat.card ↥(Subgroup.normalizer (Q : Set F) ⊓ K) := by rw [inf_comm]
  rw [Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hQK, hcard]
  exact heven

theorem prop2c {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H)
    {x : G} (hx : x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t)
    (hx1 : x ≠ 1) :
    (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard = 2 :=
  Work.ThreePoints.F1EqF.prop2c_of_even hC hBrSz hS hH ht htH
    (fun X M hM hXM hX3 =>
      Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
        hFT hC (ch1_s4_prop2_of_brsz hBrSz) hS hH hX3 hM hXM)
    hx hx1

end Work.ThreePoints.P3Sub
