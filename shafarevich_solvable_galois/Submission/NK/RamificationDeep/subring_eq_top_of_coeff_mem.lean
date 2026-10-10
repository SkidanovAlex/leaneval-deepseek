import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Data.Nat.Choose.Lucas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationDeep

open Polynomial

private lemma coeff_X_sub_C_pow {K : Type*} [Ring K] (z : K) (n k : ℕ) :
    ((X - C z) ^ n).coeff k = (-z) ^ (n - k) * (n.choose k : K) := by
  rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]

private lemma not_dvd_choose_pow_multiplicity {p n : ℕ} [Fact p.Prime] (hn : 0 < n) :
    ¬ p ∣ n.choose (p ^ multiplicity p n) := by
  obtain ⟨c, hc_eq, hc_nd⟩ :=
    (Nat.finiteMultiplicity_iff.mpr ⟨(Fact.out : p.Prime).ne_one, hn⟩ :
      FiniteMultiplicity p n).exists_eq_pow_mul_and_not_dvd
  have hlucas : n.choose (p ^ multiplicity p n) ≡ c [MOD p] := by
    have hh := Choose.choose_pow_mul_pow_mul_modEq_choose_nat
      (p := p) (k := multiplicity p n) (a := c) (b := 1)
    rw [mul_one, Nat.choose_one_right, ← hc_eq] at hh
    exact hh
  intro hd
  exact hc_nd (Nat.modEq_zero_iff_dvd.mp
    (hlucas.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)))

private lemma pow_multiplicity_le {p n : ℕ} (hn : 0 < n) : p ^ multiplicity p n ≤ n :=
  Nat.le_of_dvd hn (pow_multiplicity_dvd p n)

private lemma prime_char_case {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (S : Subring K) {n m : ℕ}
    (h : ∀ z : K, ∀ k : ℕ, ((X - C z) ^ n).coeff k ∈ S)
    (hmn : p ^ m ≤ n) (hndvd : ¬ p ∣ n.choose (p ^ m)) : S = ⊤ := by
  have hcast : (n.choose (p ^ m) : K) ≠ 0 := fun h0 =>
    hndvd ((CharP.cast_eq_zero_iff K p _).mp h0)
  have hperf : PerfectRing K (p ^ m) := inferInstance
  have humul : ∀ z : K,
      ((-1 : K) ^ (p ^ m) * (n.choose (p ^ m) : K)) * z ^ (p ^ m) ∈ S := by
    intro z
    have h1 : ((X - C z) ^ n).coeff (n - p ^ m) ∈ S := h z (n - p ^ m)
    rw [coeff_X_sub_C_pow, Nat.sub_sub_self hmn, Nat.choose_symm hmn, neg_pow] at h1
    have hrw : ((-1 : K) ^ (p ^ m) * (n.choose (p ^ m) : K)) * z ^ (p ^ m)
        = ((-1 : K) ^ (p ^ m) * z ^ (p ^ m)) * (n.choose (p ^ m) : K) := by ring
    rw [hrw]
    exact h1
  have hu : ((-1 : K) ^ (p ^ m) * (n.choose (p ^ m) : K)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hcast
  refine le_antisymm le_top fun z _ => ?_
  have hroot :
      ((powMulEquiv K (p ^ m)).symm
          (((-1 : K) ^ (p ^ m) * (n.choose (p ^ m) : K))⁻¹ * z)) ^ (p ^ m)
        = ((-1 : K) ^ (p ^ m) * (n.choose (p ^ m) : K))⁻¹ * z :=
    powMulEquiv_symm_pow_p K (p ^ m) _
  have hmem := humul ((powMulEquiv K (p ^ m)).symm
    (((-1 : K) ^ (p ^ m) * (n.choose (p ^ m) : K))⁻¹ * z))
  rw [hroot, mul_inv_cancel_left₀ hu] at hmem
  exact hmem

theorem subring_eq_top_of_coeff_mem {l : Type*} [Field l] [PerfectField l] (S : Subring l)
    {n : ℕ} (hn : 0 < n)
    (h : ∀ z : l, ∀ k : ℕ, ((Polynomial.X - Polynomial.C z) ^ n).coeff k ∈ S) : S = ⊤ := by
  by_cases hnc : (n : l) = 0
  · rcases CharP.char_is_prime_or_zero l (ringChar l) with hprime | hzero
    · have hfact : Fact (Nat.Prime (ringChar l)) := ⟨hprime⟩
      exact prime_char_case (ringChar l) S h (pow_multiplicity_le hn)
        (not_dvd_choose_pow_multiplicity hn)
    · exfalso
      have hcz : CharZero l := (CharP.ringChar_zero_iff_CharZero l).mp hzero
      exact (Nat.cast_ne_zero.mpr hn.ne') hnc
  · have hkey : ∀ t : l, t * (n : l) ∈ S := by
      intro t
      have h1 : ((X - C t) ^ n).coeff (n - 1) ∈ S := h t (n - 1)
      have hch : n.choose (n - 1) = n :=
        (Nat.choose_symm (n := n) (k := 1) hn).trans (Nat.choose_one_right n)
      rw [coeff_X_sub_C_pow, Nat.sub_sub_self hn, hch, pow_one] at h1
      have h3 := S.neg_mem h1
      simpa using h3
    refine le_antisymm le_top fun z _ => ?_
    have hfin : (z * (n : l)⁻¹) * (n : l) ∈ S := hkey (z * (n : l)⁻¹)
    rwa [mul_assoc, inv_mul_cancel₀ hnc, mul_one] at hfin

end NK.RamificationDeep
