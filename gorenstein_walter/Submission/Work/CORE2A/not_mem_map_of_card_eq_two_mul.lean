import Mathlib
import Submission.Work.CORE2A.Defs

namespace Work.CORE2A

theorem not_mem_map_of_card_eq_two_mul {K : Type} [Group K] [Finite K] (C : Subgroup K)
    [C.Normal] (hCodd : Odd (Nat.card C)) (P : Subgroup K) (hP : IsPGroup 2 P)
    (hPi : Odd P.index) {M L : Subgroup (K ⧸ C)}
    (hMne : M ≠ ⊥) (hML : Nat.card M = 2 * Nat.card L) (hLle : L ≤ M) :
    ¬ (∀ x ∈ P, QuotientGroup.mk' C x ∈ L) := by
  classical
  intro h
  -- The image `P' = P.map (mk' C)` of `P` in `K ⧸ C` is contained in `L`.
  have hP'L : P.map (QuotientGroup.mk' C) ≤ L := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  -- `2 ∤ P.index`.
  have hPi' : ¬ 2 ∣ P.index :=
    fun hd => (Nat.not_even_iff_odd.mpr hPi) (even_iff_two_dvd.mpr hd)
  -- The index of the image of `P` in `K ⧸ C` equals the index of `P ⊔ C` in `K`.
  have hidx : (P.map (QuotientGroup.mk' C)).index = (P ⊔ C).index := by
    have h1 : (Subgroup.comap (QuotientGroup.mk' C)
        (Subgroup.map (QuotientGroup.mk' C) P)).index
        = (Subgroup.map (QuotientGroup.mk' C) P).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C)
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk' C] at h1
    exact h1.symm
  -- `(P ⊔ C).index` divides the odd number `P.index`.
  have h2notPc : ¬ 2 ∣ (P ⊔ C).index :=
    fun hd => hPi' (hd.trans (Subgroup.index_dvd_of_le (le_sup_left : P ≤ P ⊔ C)))
  -- `L.index` divides the index of the image of `P`, hence is likewise odd.
  have h2notL : ¬ 2 ∣ L.index := fun hd =>
    h2notPc (hidx ▸ (hd.trans (Subgroup.index_dvd_of_le hP'L)))
  -- But `L ≤ M` together with `|M| = 2|L|` forces `L.index = 2 * M.index`, which is even.
  have hLidx : L.index = 2 * M.index := by
    have hrel := Subgroup.relIndex_mul_index hLle
    have hrel2 : L.relIndex M = 2 := by
      have hcard : Nat.card ↥(L.subgroupOf M) = Nat.card ↥L :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLle).toEquiv
      have hcm := Subgroup.card_mul_index (L.subgroupOf M)
      rw [hcard, hML] at hcm
      have hcm' : Nat.card ↥L * (L.subgroupOf M).index = Nat.card ↥L * 2 := by
        rw [hcm]; ring
      exact Nat.mul_left_cancel Nat.card_pos hcm'
    rw [hrel2] at hrel
    exact hrel.symm
  exact h2notL ⟨M.index, hLidx⟩

end Work.CORE2A
