import Mathlib

namespace Work.CORE2B

open DihedralGroup

/-- In a dihedral group `DihedralGroup m` with `m` even, every involution `z` admits a further
involution `u ≠ 1`, `u ≠ z` commuting with `z`.  (Used in the analysis of a group with dihedral
Sylow 2-subgroup: `z` and `u` generate a Klein four group together with `z * u`.)

The proof is a direct case analysis on the normal form `z = r i` or `z = sr i`. -/
theorem L27_dihedral_commuting_involution {m : ℕ} [NeZero m] (hm : Even m)
    (z : DihedralGroup m) (hz : z ^ 2 = 1) :
    ∃ u : DihedralGroup m, u ^ 2 = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u := by
  obtain ⟨k, hk⟩ := hm
  have hc : (k : ZMod m) + (k : ZMod m) = 0 := by
    rw [← Nat.cast_add, hk, ZMod.natCast_self]
  rcases z with i | i
  · -- `z = r i`, a rotation-involution: then `i + i = 0`, and `sr 0` commutes with it.
    have hz' : i + i = 0 := by
      rw [pow_two, DihedralGroup.r_mul_r, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at hz
      exact hz
    refine ⟨sr 0, ?_, ?_, ?_, ?_⟩
    · rw [pow_two, DihedralGroup.sr_mul_self]
    · change (DihedralGroup.sr 0 : DihedralGroup m) ≠ DihedralGroup.r 0
      exact fun h => nomatch h
    · exact fun h => nomatch h
    · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq,
        zero_add, zero_sub]
      exact eq_neg_iff_add_eq_zero.mpr hz'
  · -- `z = sr i`, a reflection: then `r k` (with `m = k + k`) is the central involution.
    refine ⟨r (k : ZMod m), ?_, ?_, ?_, ?_⟩
    · rw [pow_two, DihedralGroup.r_mul_r, ← Nat.cast_add, hk, ZMod.natCast_self,
        DihedralGroup.r_zero]
    · intro h
      rw [← DihedralGroup.r_zero, DihedralGroup.r.injEq] at h
      have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      have hk0 : 0 < k := by omega
      have hkm : k < m := by omega
      have hd : m ∣ k := (ZMod.natCast_eq_zero_iff k m).mp h
      have := Nat.le_of_dvd hk0 hd
      omega
    · exact fun h => nomatch h
    · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq,
        sub_eq_add_neg, neg_eq_iff_add_eq_zero.mpr hc]

end Work.CORE2B
