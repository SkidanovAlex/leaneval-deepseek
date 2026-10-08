import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CPTC

theorem NcardPairsEqSum {G : Type} [Group G] [Fintype G] (Z J : Set G)
    [DecidablePred (fun s : G => s ∈ J)] :
    ({p : G × G | p.1 ∈ Z ∧ p.2 ∈ J ∧ p.1 * p.2 = p.2 * p.1} : Set (G × G)).ncard
      = ∑ s ∈ (Finset.univ.filter (fun s : G => s ∈ J)),
          (Z ∩ Subgroup.centralizer ({s} : Set G)).ncard := by
  classical
  -- Each fibre `Z ∩ C_G(s)` is the set of `z ∈ Z` commuting with `s`.
  have hterm : ∀ s : G, (Z ∩ Subgroup.centralizer ({s} : Set G)).ncard
      = Nat.card {z : G // z ∈ Z ∧ z * s = s * z} := by
    intro s
    have hset : (Z ∩ Subgroup.centralizer ({s} : Set G))
        = {z : G | z ∈ Z ∧ z * s = s * z} := by
      ext z
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hset, ← Nat.card_coe_set_eq]
    rfl
  -- Left-hand side: swap the roles of the two coordinates, turning the pair set into the total
  -- space of the family `s ↦ {z ∈ Z : z * s = s * z}` over `s ∈ J`.
  have hL : ({p : G × G | p.1 ∈ Z ∧ p.2 ∈ J ∧ p.1 * p.2 = p.2 * p.1} : Set (G × G)).ncard
      = ∑ s : {s : G // s ∈ J},
          Nat.card {z : G // z ∈ Z ∧ z * (s : G) = (s : G) * z} := by
    rw [← Nat.card_coe_set_eq]
    let e : ↥({p : G × G | p.1 ∈ Z ∧ p.2 ∈ J ∧ p.1 * p.2 = p.2 * p.1} : Set (G × G)) ≃
        (Σ s : {s : G // s ∈ J}, {z : G // z ∈ Z ∧ z * (s : G) = (s : G) * z}) :=
      { toFun := fun p => ⟨⟨p.1.2, p.2.2.1⟩, ⟨p.1.1, p.2.1, p.2.2.2⟩⟩
        invFun := fun q => ⟨(q.2.1, q.1.1), q.2.2.1, q.1.2, q.2.2.2⟩
        left_inv := by intro p; exact Subtype.ext rfl
        right_inv := by
          rintro ⟨⟨s, hs⟩, ⟨z, hz, hc⟩⟩
          rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
  -- Right-hand side: the `Finset` sum over `J` is the sum over the subtype `{s // s ∈ J}`.
  have hsum : (∑ s ∈ (Finset.univ.filter (fun s : G => s ∈ J)),
        (Z ∩ Subgroup.centralizer ({s} : Set G)).ncard)
      = ∑ s : {s : G // s ∈ J},
          (Z ∩ Subgroup.centralizer ({(s : G)} : Set G)).ncard := by
    rw [← Finset.sum_subtype_eq_sum_filter (s := Finset.univ)]
    rw [show Finset.subtype (fun s : G => s ∈ J) Finset.univ = Finset.univ from by
          ext x; simp]
  rw [hL, hsum]
  apply Finset.sum_congr rfl
  intro s _
  exact (hterm (s : G)).symm

end Work.CPTC
