import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.PolyFraction

open Polynomial

private lemma isRelPrime_pow_left {α : Type*} [CommMonoid α] [DecompositionMonoid α]
    {x y : α} (h : IsRelPrime x y) (n : ℕ) : IsRelPrime (x ^ n) y := by
  induction n with
  | zero => simpa using isRelPrime_one_left (x := y)
  | succ n ih => rw [pow_succ]; exact ih.mul_left h

private lemma isRelPrime_pow_right {α : Type*} [CommMonoid α] [DecompositionMonoid α]
    {x y : α} (h : IsRelPrime x y) (n : ℕ) : IsRelPrime x (y ^ n) :=
  (isRelPrime_pow_left h.symm n).symm

theorem exists_const_mul_pow_of_pow_eq_div {F : Type*} [Field F] {g : Polynomial F}
    (hg0 : g.eval 0 ≠ 0) {p : ℕ} {b : FractionRing (Polynomial F)}
    (hb : b ^ p * algebraMap (Polynomial F) (FractionRing (Polynomial F)) g
        = algebraMap (Polynomial F) (FractionRing (Polynomial F)) (Polynomial.C (g.eval 0))) :
    ∃ (a : F) (h : Polynomial F), g = Polynomial.C a * h ^ p := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    rw [pow_zero, one_mul] at hb
    exact ⟨g.eval 0, 1, by
      simpa using IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F)) hb⟩
  · set n : Polynomial F := IsFractionRing.num (Polynomial F) b with hn
    set d : Polynomial F := (IsFractionRing.den (Polynomial F) b : Polynomial F) with hd
    have hnd : IsRelPrime n d := by
      rw [hn, hd]; exact IsFractionRing.num_den_reduced (Polynomial F) b
    have hbnd : algebraMap (Polynomial F) (FractionRing (Polynomial F)) n
        / algebraMap (Polynomial F) (FractionRing (Polynomial F)) d = b := by
      rw [hn, hd]; exact IsFractionRing.mk'_num_den' (Polynomial F) b
    have hd0 : d ≠ 0 := by
      rw [hd]; exact nonZeroDivisors.ne_zero (IsFractionRing.den (Polynomial F) b).2
    have hD0 : algebraMap (Polynomial F) (FractionRing (Polynomial F)) d ≠ 0 := by
      intro h
      exact hd0 (IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F))
        (by rw [h, map_zero]))
    have hkey : (algebraMap (Polynomial F) (FractionRing (Polynomial F)) n) ^ p
          * algebraMap (Polynomial F) (FractionRing (Polynomial F)) g
        = algebraMap (Polynomial F) (FractionRing (Polynomial F)) (Polynomial.C (g.eval 0))
          * (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d) ^ p := by
      have h := hb
      rw [← hbnd] at h
      rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero p hD0)] at h
      exact h
    have key : n ^ p * g = Polynomial.C (g.eval 0) * d ^ p := by
      apply IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F))
      rw [map_mul, map_pow, map_mul, map_pow]
      exact hkey
    have hnp_dvd : n ^ p ∣ Polynomial.C (g.eval 0) * d ^ p := ⟨g, key.symm⟩
    have hcop : IsRelPrime (n ^ p) (d ^ p) :=
      isRelPrime_pow_right (isRelPrime_pow_left hnd p) p
    have hnp_dvd_C : n ^ p ∣ Polynomial.C (g.eval 0) := hcop.dvd_of_dvd_mul_right hnp_dvd
    have hCunit : IsUnit (Polynomial.C (g.eval 0)) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr hg0)
    have hnp_unit : IsUnit (n ^ p) := isUnit_of_dvd_unit hnp_dvd_C hCunit
    have hn_unit : IsUnit n :=
      isUnit_of_dvd_unit (dvd_pow_self n (Nat.pos_iff_ne_zero.mp hp)) hnp_unit
    obtain ⟨c, hc⟩ : ∃ c : F, n = Polynomial.C c :=
      ⟨n.coeff 0, eq_C_of_degree_le_zero (le_of_eq (degree_eq_zero_of_isUnit hn_unit))⟩
    have hc0 : c ≠ 0 := by
      have hCc : IsUnit (Polynomial.C c) := by rw [← hc]; exact hn_unit
      exact (isUnit_C.mp hCc).ne_zero
    refine ⟨g.eval 0 * (c ^ p)⁻¹, d, ?_⟩
    have hkey2 : Polynomial.C (c ^ p) * g = Polynomial.C (g.eval 0) * d ^ p := by
      have h := key
      rw [hc, ← C_pow] at h
      exact h
    have hunitC : Polynomial.C ((c ^ p)⁻¹) * Polynomial.C (c ^ p) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero p hc0), C_1]
    calc g = 1 * g := (one_mul g).symm
      _ = (Polynomial.C ((c ^ p)⁻¹) * Polynomial.C (c ^ p)) * g := by rw [hunitC]
      _ = Polynomial.C ((c ^ p)⁻¹) * (Polynomial.C (c ^ p) * g) := by rw [mul_assoc]
      _ = Polynomial.C ((c ^ p)⁻¹) * (Polynomial.C (g.eval 0) * d ^ p) := by rw [hkey2]
      _ = Polynomial.C (g.eval 0 * (c ^ p)⁻¹) * d ^ p := by
            rw [← mul_assoc, ← C_mul]
            congr 1
            rw [mul_comm]

end Commons.FieldTheory.PolyFraction