import Mathlib
import Submission.OddOrder.Isaacs.Ch05_Transfer.Main

namespace Work.BSW.Cases.K4

-- NOTE for the prover: import `Submission.OddOrder.Isaacs.Ch05_Transfer.Main`; the Burnside
-- normal p-complement result there is `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer`.
/-- Simplicity rules out the hypothesis of Burnside's normal `p`-complement result: in a
non-abelian finite simple group of order divisible by `p`, no Sylow `p`-subgroup `P` (given here as
an arbitrary `p`-subgroup of index prime to `p`, i.e. a Sylow `p`-subgroup) is centralized by its
own normalizer. -/
theorem exists_not_mem_centralizer_of_isPGroup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (hidx : ¬ p ∣ P.index) (hp : p ∣ Nat.card G) :
    ∃ g : G, g ∈ Subgroup.normalizer (P : Set G) ∧ g ∉ Subgroup.centralizer (P : Set G) := by
  classical
  -- Suppose, for contradiction, that `N_G(P) ≤ C_G(P)`; then Burnside applies.
  by_contra hcon
  have hsub : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro g hg
    by_contra hgc
    exact hcon ⟨g, hg, hgc⟩
  -- View `P` as a Sylow `p`-subgroup (its index is prime to `p`).
  let S : Sylow p G := hP.toSylow hidx
  have hSset : (S : Set G) = (P : Set G) := rfl
  have hSsub : (S : Subgroup G) = P := rfl
  have hburn : OddOrder.Isaacs.Ch05.HasNormalPComplement p G :=
    OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer S (by
      rw [hSset, hSsub]
      exact hsub)
  -- `p` divides `|P|`, since `p ∤ [G : P]` but `p ∣ |G|`.
  have hpP : p ∣ Nat.card P := by
    have hprod : p ∣ Nat.card P * P.index := by
      rw [Subgroup.card_mul_index P]; exact hp
    rcases (Fact.out : p.Prime).dvd_mul.mp hprod with h' | h'
    · exact h'
    · exact absurd h' hidx
  obtain ⟨N, _hNnorm, hNcomp⟩ := hburn
  -- `N` is normal, and `G` is simple, so `N = ⊥` or `N = ⊤`.
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · -- `N = ⊥` forces `P = ⊤`: then `G` is a nontrivial `p`-group, hence not simple nonabelian.
    have hPtop : P = ⊤ := by
      have hS : (S : Subgroup G) = ⊤ := by
        have h' := hNcomp S
        rw [hNbot] at h'
        exact Subgroup.isComplement'_bot_left.mp h'
      rw [← hSsub]
      exact hS
    have hPG : IsPGroup p G := by
      have htop : IsPGroup p (⊤ : Subgroup G) := hPtop ▸ hP
      exact htop.of_equiv Subgroup.topEquiv
    -- The center of a nontrivial finite `p`-group is nontrivial; by simplicity it is everything.
    have hcenter : Subgroup.center G = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exfalso
        have hlt := hPG.bot_lt_center
        rw [h] at hlt
        exact lt_irrefl _ hlt
      · exact h
    -- Hence `G` is commutative, contradicting non-abelian-ness.
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (hcenter.symm ▸ Subgroup.mem_top a) b).symm
  · -- `N = ⊤` forces `P = ⊥`, contradicting `p ∣ |P|`.
    have hPbot : P = ⊥ := by
      have hS : (S : Subgroup G) = ⊥ := by
        have h' := hNcomp S
        rw [hNtop] at h'
        exact Subgroup.isComplement'_top_left.mp h'
      rw [← hSsub]
      exact hS
    have hcard : Nat.card P = 1 := hPbot.symm ▸ Subgroup.card_bot
    exact (Fact.out : p.Prime).not_dvd_one (hcard ▸ hpP)

end Work.BSW.Cases.K4
