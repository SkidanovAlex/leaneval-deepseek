import Mathlib
import Submission.Work.LinnikBurgess.ddLevelDefs

namespace Work.LinnikBurgess

open scoped BigOperators

/-- In `ZMod (p^m)` the class of `p^k` is `0` as soon as `k ≥ m` (for `m = 0` this uses that
`ZMod 1` is trivial, but the same proof covers both cases: `p^0 = 1` divides every `p^k`). -/
lemma ddLog_cast_pow_eq_zero {p m k : ℕ} (h : m ≤ k) : (p : ZMod (p ^ m)) ^ k = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p h

/-- The canonical reduction `ZMod n → ZMod m` (`m ∣ n`) commutes with inversion at every unit:
the `ZMod` inverse of a unit is its genuine inverse, hence is preserved by any ring homomorphism
which sends it to a unit. -/
lemma ddLog_cast_castHom_inv {n m : ℕ} (h : m ∣ n) (a : ZMod n) (ha : IsUnit a) :
    ZMod.castHom h (ZMod m) a⁻¹ = (ZMod.castHom h (ZMod m) a)⁻¹ := by
  set f := ZMod.castHom h (ZMod m)
  have h1 : f a⁻¹ * f a = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit a ha, map_one]
  have h3 : f a * (f a)⁻¹ = 1 := by
    have := ZMod.inv_mul_of_unit (f a) (ha.map f)
    rwa [mul_comm] at this
  calc f a⁻¹ = f a⁻¹ * 1 := (mul_one _).symm
    _ = f a⁻¹ * (f a * (f a)⁻¹) := by rw [h3]
    _ = (f a⁻¹ * f a) * (f a)⁻¹ := by rw [mul_assoc]
    _ = 1 * (f a)⁻¹ := by rw [h1]
    _ = (f a)⁻¹ := by rw [one_mul]

/-- The coefficients of the truncated `p`-adic logarithm are compatible with the reduction
`ZMod (p^e) → ZMod (p^m)` (`m ≤ e`): every factor of `ddLogCoeff p e j` is the reduction of the
corresponding factor of `ddLogCoeff p m j`.  Here `j / p ^ padicValNat p j` is coprime to `p`, hence
a unit in both rings, which is what makes the inverse factor compatible. -/
lemma ddLogCoeff_cast {p e m j : ℕ} [Fact p.Prime] (hm : m ≤ e) (hj : 1 ≤ j) :
    ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m)) (ddLogCoeff p e j)
      = ddLogCoeff p m j := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hj0 : j ≠ 0 := by omega
  -- `j / p ^ padicValNat p j` is the maximal `p`-free part of `j`, hence coprime to `p`.
  have hdiv : j.divMaxPow p = j / p ^ padicValNat p j := by
    have := Nat.pow_padicValNat_mul_divMaxPow p j
    exact Nat.eq_div_of_mul_eq_right (pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out : p.Prime))) this
  have hnotdvd : ¬ p ∣ j / p ^ padicValNat p j := by
    rw [← hdiv]
    exact Nat.not_dvd_divMaxPow hp1 hj0
  have hcop : Nat.Coprime (j / p ^ padicValNat p j) p :=
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hnotdvd).symm
  have hunit : IsUnit (((j / p ^ padicValNat p j : ℕ)) : ZMod (p ^ e)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_right e)
  simp only [ddLogCoeff, map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [ddLog_cast_castHom_inv _ _ hunit]
  simp

/-- The `j`-th coefficient of the truncated `p`-adic logarithm vanishes in `ZMod (p^m)` as soon as
`j > m`: then `3 (j - 1) - padicValNat p j ≥ 2 (j - 1) ≥ m`, so the `p`-power factor is `0`. -/
lemma ddLogCoeff_eq_zero_of_lt {p m j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) (hjm : m < j) :
    ddLogCoeff p m j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hvp : padicValNat p j ≤ j - 1 := by
    have := Nat.padicValNat_lt_self (p := p) hj0
    omega
  have hk : m ≤ 3 * (j - 1) - padicValNat p j := by omega
  simp only [ddLogCoeff]
  rw [ddLog_cast_pow_eq_zero hk]
  simp

theorem ddLog_cast {p e m : ℕ} [Fact p.Prime] (hm : m ≤ e) (w : ZMod (p ^ e)) :
    (ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))) (Work.LinnikBurgess.ddLog p e w)
      = Work.LinnikBurgess.ddLog p m ((ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))) w) := by
  unfold ddLog
  rw [map_sum]
  simp only [map_mul, map_pow]
  -- reduce the coefficients of the sum at level `e` to level `m`
  rw [Finset.sum_congr rfl (fun j hj => by
        rw [ddLogCoeff_cast hm (Finset.mem_Icc.mp hj).1])]
  -- extend the sum from `Icc 1 m` to `Icc 1 e`: the extra terms vanish
  have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 e := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, le_trans (Finset.mem_Icc.mp hx).2 hm⟩
  have hzero : ∀ x ∈ Finset.Icc 1 e, x ∉ Finset.Icc 1 m →
      ddLogCoeff p m x * ((ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))) w) ^ x = 0 := by
    intro x hxt hxs
    have h1 : 1 ≤ x := (Finset.mem_Icc.mp hxt).1
    have h2 : m < x := by
      have hmem := hxs
      simp only [Finset.mem_Icc, not_and_or] at hmem
      omega
    rw [ddLogCoeff_eq_zero_of_lt h1 h2, zero_mul]
  rw [Finset.sum_subset hsub hzero]

end Work.LinnikBurgess
