import Mathlib

namespace Work.BG

/-- If `S` is an abelian Sylow `2`-subgroup of a finite group, then `N_G(S)/C_G(S)` has odd order:
an element of the normalizer whose square centralizes `S` already centralizes `S`. -/
theorem l42NgridParity {G : Type} [Group G] [Finite G]
    (S : Sylow 2 G) (hab : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x)
    {z : G} (hzN : z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hz2 : z ^ 2 ∈ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  -- `S` is abelian, hence contained in its own centralizer.
  haveI : IsMulCommutative (S : Subgroup G) := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  set C : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G) with hC
  set N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) with hN
  have hzN' : z ∈ N := by rw [hN]; exact hzN
  have hz2' : z ^ 2 ∈ C := by rw [hC]; exact hz2
  -- `S ≤ C ≤ N`.
  have hSN : (S : Subgroup G) ≤ N := by rw [hN]; exact Subgroup.le_normalizer
  have hSC : (S : Subgroup G) ≤ C := by rw [hC]; exact Subgroup.le_centralizer _
  -- The index of `S` in `N` is odd (Sylow), hence so is the index of `C` in `N`,
  -- which is the order of `N/C`.
  have hn2 : ¬ 2 ∣ (S : Subgroup G).index := Sylow.not_dvd_index S
  have hnrel : ¬ 2 ∣ (S : Subgroup G).relIndex N := by
    intro hv
    apply hn2
    rw [← Subgroup.relIndex_mul_index hSN]
    exact dvd_mul_of_dvd_left hv _
  have hodd : ¬ 2 ∣ C.relIndex N := fun hv =>
    hnrel (hv.trans (Subgroup.relIndex_dvd_of_le_left N hSC))
  -- `C` is normal in `N`; pass to the quotient `N ⧸ C`.
  haveI : (C.subgroupOf N).Normal := by
    rw [hC, hN]; exact Subgroup.normal_subgroupOf_centralizer_normalizer _
  set q : N ⧸ (C.subgroupOf N) := (QuotientGroup.mk' (C.subgroupOf N)) (⟨z, hzN'⟩ : N) with hq
  have hq2 : q ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hz2'
  have hcard : Nat.card (N ⧸ (C.subgroupOf N)) = C.relIndex N := by
    rw [← Subgroup.index_eq_card (C.subgroupOf N)]
    rfl
  have hoddN : ¬ 2 ∣ Nat.card (N ⧸ (C.subgroupOf N)) := by rw [hcard]; exact hodd
  -- An element of odd order whose square is trivial is trivial.
  have hq1 : q = 1 := by
    have hdvd2 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2
    have hdvdN : orderOf q ∣ Nat.card (N ⧸ (C.subgroupOf N)) := orderOf_dvd_natCard q
    have hone : orderOf q = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact h
      · exact absurd (h ▸ hdvdN) hoddN
    exact orderOf_eq_one_iff.mp hone
  have hzC : z ∈ C := by
    have hmem : (⟨z, hzN'⟩ : N) ∈ C.subgroupOf N :=
      (QuotientGroup.eq_one_iff (⟨z, hzN'⟩ : N)).mp hq1
    exact Subgroup.mem_subgroupOf.mp hmem
  exact hzC

end Work.BG
