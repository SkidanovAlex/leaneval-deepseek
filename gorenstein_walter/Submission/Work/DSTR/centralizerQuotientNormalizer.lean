import Mathlib
import Submission.Work.DSTR.centralizer_map_eq_of_odd_card

namespace Work.DSTR

theorem centralizerQuotientNormalizer {X : Type} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]
    (hZodd : Odd (Nat.card Z)) {t : X} (ht : orderOf t = 2) {P : Subgroup X}
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X)) :
    Subgroup.centralizer ({(QuotientGroup.mk' Z) t} : Set (X ⧸ Z)) ≤
      Subgroup.normalizer (((P.map (QuotientGroup.mk' Z) : Subgroup (X ⧸ Z))) : Set (X ⧸ Z)) := by
  classical
  -- In the quotient, the centralizer of `tZ` is the image of `C_X(t)`
  -- (this is where oddness of `|Z|` and `t² = 1` are used).
  rw [← centralizer_map_eq_of_odd_card Z hZodd t ht]
  rw [Subgroup.le_normalizer_iff]
  intro y hy k hk
  -- Unpack `y ∈ C_X(t).map π` and `k ∈ P.map π`.
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hk
  -- The hypothesis `C_X(t) ≤ N_X(P)` says `c` normalizes `P`.
  refine Subgroup.mem_map.mpr ⟨c * p * c⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hN hc) p).mp hp
  · rw [map_mul, map_mul, map_inv]

end Work.DSTR
