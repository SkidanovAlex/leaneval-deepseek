import Mathlib
import Submission.NK.LocalAnabelian.Kummer.Quot
import Submission.NK.LocalAnabelian.Kummer.kummerField_eq_of_div_mem_powSubgroup

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian.Kummer

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- The image in `K'` of a power of a unit `a : kˣ` is the corresponding power of the
image of `a`. -/
private lemma algebraMap_zpow_units (a : kˣ) (n : ℤ) :
    algebraMap k K' ((a ^ n : kˣ) : k) = (algebraMap k K' (a : k)) ^ n := by
  rw [Units.val_zpow_eq_zpow_val]
  exact map_zpow₀ (algebraMap k K' : k →+* K') (a : k) n

/-- The image of a unit of `k` in `K'` is nonzero. -/
private lemma algebraMap_units_ne_zero (a : kˣ) : algebraMap k K' (a : k) ≠ 0 := by
  have h := (FaithfulSMul.algebraMap_injective k K').ne (Units.ne_zero a)
  simpa using h

/-! ## Replacing a class by a coprime power

If `p ∤ n`, then `k(a^{1/p}) = k(a^{n/p})`: the two sets of `p`-th roots generate the
same subfield, because Bézout coefficients `n s + p t = 1` express one root in terms of
the other.  No separability hypothesis is needed. -/
private theorem kummerField_zpow_eq_of_not_dvd (p : ℕ) (hp : p.Prime) {a : kˣ} {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) :
    kummerField (K' := K') p (a ^ n) = kummerField (K' := K') p a := by
  have hP : Prime (p:ℤ) := by rw [Int.prime_iff_natAbs_prime]; simpa using hp
  have hcop : IsCoprime (p:ℤ) n := (Prime.coprime_iff_not_dvd hP).mpr hn
  have hg : (p:ℤ).gcd n = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hb := Int.gcd_eq_gcd_ab (p:ℤ) n
  rw [hg] at hb
  norm_num at hb
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, n * s + (p:ℤ) * t = 1 :=
    ⟨Int.gcdB (p:ℤ) n, Int.gcdA (p:ℤ) n, by linarith [hb]⟩
  have ha0 : algebraMap k K' (a : k) ≠ 0 := algebraMap_units_ne_zero a
  apply le_antisymm
  · -- `kummerField p (a^n) ≤ kummerField p a`
    rw [kummerField_le_iff]
    intro β hβ
    have hβ0 : β ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero, algebraMap_zpow_units] at hβ
      exact (zpow_ne_zero n ha0) hβ.symm
    set v : K'ˣ := Units.mk0 β hβ0 with hv
    set w : K'ˣ := Units.mk0 (algebraMap k K' (a : k)) ha0 with hw
    have hvp : v ^ p = w ^ n := by
      apply Units.ext
      simp only [v, w, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [hβ, algebraMap_zpow_units]
    let α : K' := β ^ s * (algebraMap k K' (a : k)) ^ t
    have hα0 : α ≠ 0 := mul_ne_zero (zpow_ne_zero s hβ0) (zpow_ne_zero t ha0)
    have hx' : (Units.mk0 α hα0 : K'ˣ) = v ^ s * w ^ t := by
      apply Units.ext
      simp only [α, v, w, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    have hA : (v ^ s) ^ (p:ℤ) = w ^ (n * s) := by
      rw [← zpow_mul, mul_comm s (p:ℤ), zpow_mul, zpow_natCast, hvp, ← zpow_mul]
    have hB : (w ^ t) ^ (p:ℤ) = w ^ ((p:ℤ) * t) := by
      rw [← zpow_mul, mul_comm t (p:ℤ)]
    have hxp : (Units.mk0 α hα0) ^ p = w := by
      rw [hx', ← zpow_natCast, mul_zpow, hA, hB, ← zpow_add, hst, zpow_one]
    have hαp : α ^ p = algebraMap k K' (a : k) := by
      have hh := congrArg (fun z : K'ˣ => (z : K')) hxp
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at hh
      exact hh
    have hαmem : α ∈ kummerField (K' := K') p a := mem_kummerField_of_pow_eq hαp
    have hβeq : β = α ^ n := by
      have hA2 : (v ^ s) ^ n = v ^ (s * n) := (zpow_mul v s n).symm
      have hB2 : (w ^ t) ^ n = w ^ (t * n) := (zpow_mul w t n).symm
      have hveq : (Units.mk0 α hα0) ^ n = v := by
        rw [hx', mul_zpow, hA2, hB2]
        have hs : s * n = 1 - (p:ℤ) * t := by linarith [hst, mul_comm s n]
        have hvt : v ^ ((p:ℤ) * t) = w ^ (n * t) := by
          rw [zpow_mul, zpow_natCast, hvp, ← zpow_mul]
        have hv1 : v ^ (s*n) = v * (w ^ (n*t))⁻¹ := by
          rw [hs, sub_eq_add_neg, zpow_add, zpow_one, zpow_neg, hvt]
        have hwt : w ^ (t*n) = w ^ (n*t) := by rw [mul_comm t n]
        rw [hv1, hwt, mul_assoc, inv_mul_cancel, mul_one]
      have hh := congrArg (fun z : K'ˣ => (z : K')) hveq
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hh
      exact hh.symm
    rw [hβeq]
    exact IntermediateField.pow_mem _ hαmem n
  · -- `kummerField p a ≤ kummerField p (a^n)`
    rw [kummerField_le_iff]
    intro α hα
    have hα0 : α ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hα
      exact ha0 hα.symm
    have hmul : (α ^ n) ^ s = α ^ (n * s) := (zpow_mul α n s).symm
    have hmul2 : (algebraMap k K' (a : k)) ^ t = α ^ ((p:ℤ) * t) := by
      rw [← hα, ← zpow_natCast, ← zpow_mul]
    have hsplit : (α ^ n) ^ s * (algebraMap k K' (a : k)) ^ t = α := by
      rw [hmul, hmul2, ← zpow_add₀ hα0, hst, zpow_one]
    have hαn : (α ^ n) ^ p = algebraMap k K' (a : k) ^ n := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm n (p:ℤ), zpow_mul, zpow_natCast, hα]
    have hmem : α ^ n ∈ kummerField (K' := K') p (a ^ n) := by
      apply mem_kummerField_of_pow_eq
      rw [hαn, algebraMap_zpow_units]
    rw [← hsplit]
    exact IntermediateField.mul_mem _ (IntermediateField.pow_mem _ hmem s)
      (by rw [← algebraMap_zpow_units]; exact IntermediateField.algebraMap_mem _ _)

/-- If `y` lies in the cyclic subgroup generated by `x` and both are nontrivial
elements of the Kummer class group `kˣ/(kˣ)^p`, then `y` and `x` define the same
Kummer field.  Indeed, the quotient has exponent `p`, so `y = x^n` for some `n`
coprime to `p`, and the Kummer field only depends on the class up to `p`-th
powers and is unchanged under replacing `a` by a coprime power. -/
theorem kummerFieldQuot_eq_of_mem_zpowers {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p)
    {x y : KummerGroup p k} (hx : x ≠ 1) (hy : y ≠ 1) (h : y ∈ Subgroup.zpowers x) :
    kummerFieldQuot (K' := K') p y = kummerFieldQuot (K' := K') p x := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have hxp : x ^ p = 1 := by
    refine QuotientGroup.induction_on x (fun a => ?_)
    show (QuotientGroup.mk' (powSubgroup p k) a) ^ p = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  have hxpp : x ^ (p:ℤ) = 1 := by rw [zpow_natCast, hxp]
  have hndvd : ¬ (p:ℤ) ∣ n := by
    rintro ⟨m, hm⟩
    have hxn : x ^ n = 1 := by
      rw [hm, zpow_mul x (p:ℤ) m, hxpp, one_zpow]
    rw [hn] at hxn
    exact hy hxn
  have ha : (QuotientGroup.mk' (powSubgroup p k) (Quotient.out x)) = x := by
    rw [QuotientGroup.mk'_apply]; exact Quotient.out_eq x
  have hb : (QuotientGroup.mk' (powSubgroup p k) (Quotient.out y)) = y := by
    rw [QuotientGroup.mk'_apply]; exact Quotient.out_eq y
  have hclass : (QuotientGroup.mk' (powSubgroup p k) (Quotient.out y))
      = (QuotientGroup.mk' (powSubgroup p k) ((Quotient.out x) ^ n)) := by
    rw [hb, map_zpow, ha, hn]
  have hkey : (Quotient.out y)⁻¹ * (Quotient.out x) ^ n ∈ powSubgroup p k :=
    (QuotientGroup.eq (s := powSubgroup p k)).mp (by
      simpa only [QuotientGroup.mk'_apply] using hclass)
  have h1 : kummerField (K' := K') p (Quotient.out y)
      = kummerField (K' := K') p ((Quotient.out x) ^ n) :=
    kummerField_eq_of_div_mem_powSubgroup p hkey
  have h2 : kummerField (K' := K') p ((Quotient.out x) ^ n)
      = kummerField (K' := K') p (Quotient.out x) :=
    kummerField_zpow_eq_of_not_dvd p hp hndvd
  rw [kummerFieldQuot, kummerFieldQuot, h1, h2]

end NK.LocalAnabelian.Kummer
