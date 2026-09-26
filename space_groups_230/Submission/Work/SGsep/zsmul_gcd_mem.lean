import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

/-- Bézout step for orders modulo a lattice: the set `{k : ℤ | k • u ∈ L}` is an additive
subgroup of `ℤ`, so if `o • u ∈ L` and `k • u ∈ L` then `gcd o |k| • u ∈ L`.  (Stated for an
arbitrary additive group with an integer action.) -/
theorem zsmul_gcd_mem {M : Type*} [AddCommGroup M] {L : AddSubgroup M} {u : M} {m : ℕ} {k : ℤ}
    (hm : (m : ℤ) • u ∈ L) (hk : k • u ∈ L) :
    (((Nat.gcd m k.natAbs : ℕ) : ℤ)) • u ∈ L := by
  -- `|k| • u ∈ L`
  have hkabs : ((k.natAbs : ℕ) : ℤ) • u ∈ L := by
    rcases Int.natAbs_eq k with h | h
    · rw [← h]; exact hk
    · have h2 : ((k.natAbs : ℕ) : ℤ) = -k := by rw [h]; simp
      rw [h2, neg_zsmul]; exact neg_mem hk
  -- Bézout: `gcd m |k| = a * m + b * |k|`
  have hbez : ((Nat.gcd m k.natAbs : ℕ) : ℤ) =
      Nat.gcdA m k.natAbs * (m : ℤ) + Nat.gcdB m k.natAbs * ((k.natAbs : ℕ) : ℤ) := by
    rw [Nat.gcd_eq_gcd_ab]; ring
  rw [hbez, add_zsmul]
  apply add_mem
  · rw [mul_zsmul]; exact AddSubgroup.zsmul_mem L hm _
  · rw [mul_zsmul]; exact AddSubgroup.zsmul_mem L hkabs _

end Work.SGsep
