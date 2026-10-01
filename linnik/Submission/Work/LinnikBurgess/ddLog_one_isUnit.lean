import Mathlib
import Submission.Work.LinnikBurgess.ddLevelDefs

namespace Work.LinnikBurgess

open Finset

/-- For a prime `p` and `1 ≤ j`, the `p`-adic valuation of `j` is at most `j - 1`:
`p ^ padicValNat p j ∣ j` forces `p ^ padicValNat p j ≤ j`, while `padicValNat p j < 2 ^ padicValNat p j`. -/
lemma padicValNat_le_sub_one {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) :
    padicValNat p j ≤ j - 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hlt : padicValNat p j < j := by
    calc padicValNat p j < 2 ^ padicValNat p j := Nat.lt_two_pow_self
      _ ≤ p ^ padicValNat p j := Nat.pow_le_pow_left hp2 _
      _ ≤ j := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  omega

/-- The `j = 1` coefficient of the truncated `p`-adic logarithm is `1`. -/
lemma ddLogCoeff_one (p m : ℕ) : ddLogCoeff p m 1 = 1 := by
  simp [ddLogCoeff]

/-- Every coefficient `ddLogCoeff p m j` with `2 ≤ j` is divisible by `p`. -/
lemma dvd_ddLogCoeff (p m j : ℕ) [Fact p.Prime] (hj : 2 ≤ j) :
    (p : ZMod (p ^ m)) ∣ ddLogCoeff p m j := by
  have hbound : padicValNat p j ≤ j - 1 := padicValNat_le_sub_one (by omega)
  have he : 1 ≤ 3 * (j - 1) - padicValNat p j := by omega
  unfold ddLogCoeff
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le he
  rw [hk, pow_add, pow_one]
  exact ⟨(-1 : ZMod (p ^ m)) ^ (j - 1) * (p : ZMod (p ^ m)) ^ k
      * (((j / p ^ padicValNat p j : ℕ)) : ZMod (p ^ m))⁻¹, by ring⟩

/-- `1 + p * T` is a unit in `ZMod (p ^ m)`: its "inverse" is the finite geometric series
`∑_{i<m} (-(p T))^i`, since `(p T)^m = p^m T^m = 0`. -/
lemma isUnit_one_add_p_mul (p m : ℕ) (T : ZMod (p ^ m)) :
    IsUnit (1 + (p : ZMod (p ^ m)) * T) := by
  set x := (p : ZMod (p ^ m)) * T with hx
  have hxm : x ^ m = 0 := by
    rw [hx, mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  have hgeo := Commute.mul_geom_sum₂ (Commute.one_left (-x)) m
  simp only [one_pow] at hgeo
  have hneg : (-x) ^ m = 0 := by rw [neg_pow, hxm, mul_zero]
  have h1 : (1 : ZMod (p ^ m)) - (-x) = 1 + x := by ring
  rw [h1, hneg, sub_zero] at hgeo
  exact ⟨Units.mkOfMulEqOne (1 + x)
    (∑ i ∈ range m, (1 : ZMod (p ^ m)) * (-x) ^ (m - 1 - i)) hgeo, rfl⟩

theorem ddLog_one_isUnit {p m : ℕ} [Fact p.Prime] (hm : 1 ≤ m) :
    IsUnit (Work.LinnikBurgess.ddLog p m 1) := by
  have h1mem : 1 ∈ Icc 1 m := mem_Icc.mpr ⟨le_rfl, hm⟩
  have hddlog : ddLog p m 1 = ∑ j ∈ Icc 1 m, ddLogCoeff p m j := by
    simp only [ddLog, one_pow, mul_one]
  rw [hddlog, sum_eq_add_sum_sdiff_singleton_of_mem h1mem]
  have hdiff : Icc 1 m \ {1} = Icc 2 m := by
    ext x
    simp only [mem_sdiff, mem_singleton, mem_Icc]
    omega
  rw [hdiff, ddLogCoeff_one]
  obtain ⟨T, hT⟩ := Finset.dvd_sum (s := Icc 2 m) (f := fun j => ddLogCoeff p m j)
    (fun j hj => dvd_ddLogCoeff p m j (by simp only [mem_Icc] at hj; omega))
  rw [hT]
  exact isUnit_one_add_p_mul p m T

end Work.LinnikBurgess
