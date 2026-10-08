import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.NPC.Engine
import Submission.Work.Grun.pResidual
import Submission.Work.ThmF.Tools.hasNormalIndexP_iff
import Submission.Work.PGroup.isCoatom_index_eq_prime
import Submission.Work.Skeleton.Minimal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Tools

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

/-- A nontrivial finite `p`-group has a normal subgroup of index `p`.

A maximal proper subgroup `M` of a finite `p`-group `Q` is normal (`Q` is nilpotent, so it
satisfies the normalizer condition) and has index `p` (`Work.PGroup.isCoatom_index_eq_prime`). -/
theorem exists_normal_index_eq_prime_of_isPGroup {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsPGroup p Q) (hnt : Nontrivial Q) :
    ∃ M : Subgroup Q, M.Normal ∧ M.index = p := by
  obtain ⟨M, hM⟩ := Work.Skeleton.exists_isCoatom_subgroup Q
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  exact ⟨M,
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM,
    Work.PGroup.isCoatom_index_eq_prime hQ hM⟩

/-- A normal subgroup of index `p` in a quotient `G ⧸ N` pulls back to a normal subgroup of
index `p` in `G`. -/
theorem hasNormalIndexP_of_quotient {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (h : HasNormalIndexP p (G ⧸ N)) : HasNormalIndexP p G := by
  obtain ⟨M, hMnormal, hMindex⟩ := h
  haveI : M.Normal := hMnormal
  exact ⟨M.comap (QuotientGroup.mk' N), Subgroup.normal_comap (QuotientGroup.mk' N),
    by rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hMindex]⟩

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem burnsideCorollary {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card G) (hno : ¬ HasNormalIndexP p G) (P : Sylow p G) : ¬ (Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G)) := by
  intro h
  -- Burnside's normal `p`-complement theorem: if the Sylow `p`-subgroup is central in its
  -- normalizer, then `G` has a normal `p`-complement `N`.
  have hnpc : Work.NPC.HasNormalPComplement p G := Work.NPC.burnside_npc P h
  obtain ⟨N, hN⟩ := hnpc
  haveI : N.Normal := hN.normal
  -- Since `p ∣ |G|` while `|N|` is coprime to `p`, the quotient `G ⧸ N` is a nontrivial
  -- `p`-group, hence has a normal subgroup of index `p`.
  have hnt : Nontrivial (G ⧸ N) := by
    have hNtop : N ≠ ⊤ := by
      intro htop
      have hdvd : p ∣ Nat.card N := by rw [htop, Subgroup.card_top]; exact hp
      have hg : (Nat.card N).gcd p = 1 := hN.coprime_card.gcd_eq_one
      have hpg : p ∣ (Nat.card N).gcd p := Nat.dvd_gcd hdvd (dvd_refl p)
      rw [hg] at hpg
      exact (Fact.out : p.Prime).not_dvd_one hpg
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact hNtop (QuotientGroup.subgroup_eq_top_of_subsingleton N hs)
  obtain ⟨M, hMnormal, hMindex⟩ :=
    exists_normal_index_eq_prime_of_isPGroup hN.isPGroup_quotient hnt
  -- Pulling this back to `G` produces a normal subgroup of `G` of index `p`, contradicting
  -- the hypothesis.
  exact hno (hasNormalIndexP_of_quotient ⟨M, hMnormal, hMindex⟩)

end Work.ThmF.Tools
