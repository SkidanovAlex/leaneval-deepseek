/-
Copyright (c) 2024. All rights reserved.

# Frobenius-orbit disjointness for the `C₄` residual (case (β))

The number-theoretic core of Higman's §4 eigenvalue bookkeeping in its simplest form: the
Frobenius (`×2`) orbits of the residues `1 - 2 ^ k` (`k < n`) modulo `2 ^ n - 1` are pairwise
disjoint.  Equivalently, the congruence `2 ^ u · (1 - 2 ^ k₁) ≡ 1 - 2 ^ k₂ (mod 2 ^ n - 1)` forces
`k₁ = k₂`.

This is what makes the `M_k = {x ↦ c · x ^ (2 ^ k)}` (`k < n`) "Frobenius components" of
`Hom_{𝔽₂}(GF(2^n), GF(2^n))` pairwise non-isomorphic as `𝔽₂[ξ]`-modules (their `ξ`-eigenvalues
are `ν ^ (1 - 2 ^ k)`), so an *irreducible* `ξ`-submodule of `Hom(S,W)` lies inside a single
`M_k`, all of whose non-zero elements are bijections.
-/

import Mathlib
import Submission.Work.Higman.H8.two_pow_add_inj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

/-- **Frobenius-orbit disjointness.**  For `n ≥ 2` and `k₁, k₂, u < n`, if
`2 ^ u + 2 ^ k₂ ≡ 1 + 2 ^ ((u + k₁) % n) (mod 2 ^ n - 1)` — the reducible form of the collision
`2 ^ u · (1 - 2 ^ k₁) ≡ 1 - 2 ^ k₂` — then `k₁ = k₂`. -/
theorem frob_orbit_eq {n : ℕ} (hn : 2 ≤ n) {k₁ k₂ u : ℕ}
    (hk₁ : k₁ < n) (hk₂ : k₂ < n) (hu : u < n)
    (h : 2 ^ u + 2 ^ k₂ ≡ 1 + 2 ^ ((u + k₁) % n) [MOD 2 ^ n - 1]) :
    k₁ = k₂ := by
  have hn1 : 1 ≤ n := by omega
  have h2n_ge2 : 2 ≤ 2 ^ n := by
    have h1 : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hmp : 0 < 2 ^ n - 1 := by omega
  set m : ℕ := 2 ^ n - 1 with hm
  set e : ℕ := (u + k₁) % n with he
  have he_lt : e < n := by rw [he]; exact Nat.mod_lt _ (by omega)
  set A : ℕ := 2 ^ u + 2 ^ k₂ with hA
  set B : ℕ := 1 + 2 ^ e with hB
  -- bounds
  have hu_le : u ≤ n - 1 := by omega
  have hk2_le : k₂ ≤ n - 1 := by omega
  have hpow2u : 2 ^ u ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hu_le
  have hpow2k : 2 ^ k₂ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hk2_le
  have hpow2e : 2 ^ e ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow_half : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [← two_mul, show (2 : ℕ) * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 from by ring, ← pow_succ]
    congr 1
    omega
  have hA_le : A ≤ 2 ^ n := by rw [hA]; omega
  have hB_le : B ≤ 2 ^ (n - 1) + 1 := by rw [hB]; omega
  have hA_two : 2 ≤ A := by
    rw [hA]
    have h1 : 1 ≤ 2 ^ u := Nat.one_le_pow u 2 (by norm_num)
    have h2 : 1 ≤ 2 ^ k₂ := Nat.one_le_pow k₂ 2 (by norm_num)
    omega
  have hB_two : 2 ≤ B := by
    rw [hB]
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num)
    omega
  have hhalf_lt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hAm : A - B < m := by rw [hm]; omega
  have hBm : B - A < m := by rw [hm]; omega
  -- `A ≡ B` and the bounds force `A = B`
  have hdiff : A = B := by
    have hmod : A ≡ B [MOD m] := h
    rcases le_total B A with hBA | hAB
    · have h1 : A - B ≡ 0 [MOD m] := by
        have h2 : B + (A - B) ≡ B + 0 [MOD m] := by
          rw [add_zero, Nat.add_sub_cancel' hBA]
          exact hmod
        exact Nat.ModEq.add_left_cancel' B h2
      have h2 : A - B = 0 :=
        Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h1) hAm
      omega
    · have h1 : B - A ≡ 0 [MOD m] := by
        have h2 : A + (B - A) ≡ A + 0 [MOD m] := by
          rw [add_zero, Nat.add_sub_cancel' hAB, Nat.ModEq.comm]
          exact hmod
        exact Nat.ModEq.add_left_cancel' A h2
      have h2 : B - A = 0 :=
        Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h1) hBm
      omega
  have hkey : 2 ^ u + 2 ^ k₂ = 2 ^ 0 + 2 ^ e := by
    rw [← hA, hdiff, hB]; norm_num
  rcases le_total u k₂ with hle | hlt
  · have h1 := two_pow_add_inj hle (Nat.zero_le e) hkey
    obtain ⟨hu0, hk2e⟩ := h1
    have hee : e = k₁ := by rw [he, hu0, Nat.zero_add, Nat.mod_eq_of_lt hk₁]
    omega
  · have hkey' : 2 ^ k₂ + 2 ^ u = 2 ^ 0 + 2 ^ e := by rw [add_comm]; exact hkey
    have h1 := two_pow_add_inj hlt (Nat.zero_le e) hkey'
    obtain ⟨hk20, hue⟩ := h1
    have hmod' : u + k₁ ≡ u [MOD n] := by
      have h1 : (u + k₁) % n = e := he.symm
      rw [Nat.ModEq, h1, ← hue]
      exact (Nat.mod_eq_of_lt hu).symm
    have hk1dvd : n ∣ k₁ := by
      have h2 : u + k₁ ≡ u + 0 [MOD n] := by simpa using hmod'
      exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_left_cancel' u h2)
    have hk10 : k₁ = 0 := Nat.eq_zero_of_dvd_of_lt hk1dvd hk₁
    omega

/-- **The multiplicative order of `2` modulo `2 ^ n - 1` is `n`.**  If `2 ^ t ≡ 1 (mod 2 ^ n - 1)`
then `n ∣ t`. -/
theorem dvd_of_pow_two_modEq_one {n t : ℕ} (hn : 0 < n)
    (h : (2 : ℕ) ^ t ≡ 1 [MOD 2 ^ n - 1]) : n ∣ t := by
  have h2n : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] := by
    show 2 ^ n % (2 ^ n - 1) = 1 % (2 ^ n - 1)
    have hpow : 2 ^ n = 1 + (2 ^ n - 1) := by
      have := Nat.one_le_pow n 2 (by norm_num); omega
    nth_rewrite 1 [hpow]
    exact Nat.add_mod_right 1 (2 ^ n - 1)
  have hcomp : (2 : ℕ) ^ t = (2 ^ n) ^ (t / n) * 2 ^ (t % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h3 : (2 : ℕ) ^ t ≡ 2 ^ (t % n) [MOD 2 ^ n - 1] := by
    rw [hcomp]
    simpa using (h2n.pow (t / n)).mul (Nat.ModEq.refl (2 ^ (t % n)))
  have h5 : (2 : ℕ) ^ (t % n) ≡ 1 [MOD 2 ^ n - 1] := h3.symm.trans h
  have h6 : 2 ^ n - 1 ∣ 2 ^ (t % n) - 1 :=
    (Nat.modEq_iff_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ (t % n))
      (Nat.one_le_pow (t % n) 2 (by norm_num))).mp h5.symm
  have hlt : 2 ^ (t % n) - 1 < 2 ^ n - 1 := by
    have hlt2 : 2 ^ (t % n) < 2 ^ n :=
      Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt t hn)
    have h1 : 1 ≤ 2 ^ (t % n) := Nat.one_le_pow _ 2 (by norm_num)
    omega
  have h8 : 2 ^ (t % n) - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h6 hlt
  have h10 : t % n = 0 := by
    by_contra hc
    have hpos : 1 ≤ t % n := Nat.one_le_iff_ne_zero.mpr hc
    have hge : 2 ^ 1 ≤ 2 ^ (t % n) := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  exact Nat.dvd_of_mod_eq_zero h10

/-- **The exponent map `k ↦ 2 ^ k` is injective modulo `2 ^ n - 1` on `{0, …, n-1}`.**
Equivalently, the scalars `ν ^ (1 - 2 ^ k)` (`k < n`) are pairwise distinct for `ν` of order
`2 ^ n - 1`. -/
theorem pow_two_modEq_one_eq {n : ℕ} (hn : 0 < n) {k₁ k₂ : ℕ} (hk₁ : k₁ < n) (hk₂ : k₂ < n)
    (h : 2 ^ k₁ ≡ 2 ^ k₂ [MOD 2 ^ n - 1]) : k₁ = k₂ := by
  have h2n : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] := by
    show 2 ^ n % (2 ^ n - 1) = 1 % (2 ^ n - 1)
    have hpow : 2 ^ n = 1 + (2 ^ n - 1) := by
      have := Nat.one_le_pow n 2 (by norm_num); omega
    nth_rewrite 1 [hpow]
    exact Nat.add_mod_right 1 (2 ^ n - 1)
  rcases le_total k₁ k₂ with hle | hle
  · have h1 : 2 ^ k₁ * 2 ^ (n - k₂) ≡ 2 ^ k₂ * 2 ^ (n - k₂) [MOD 2 ^ n - 1] := h.mul_right _
    rw [← pow_add, ← pow_add, Nat.add_sub_of_le (le_of_lt hk₂)] at h1
    have h3 : 2 ^ (k₁ + (n - k₂)) ≡ 1 [MOD 2 ^ n - 1] := h1.trans h2n
    have hd : n ∣ k₁ + (n - k₂) := dvd_of_pow_two_modEq_one hn h3
    obtain ⟨c, hc⟩ := hd
    have hlt : k₁ + (n - k₂) < 2 * n := by omega
    have hpos : 0 < k₁ + (n - k₂) := by omega
    have hc1 : c = 1 := by
      have hcpos : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        omega
      have hclt : c < 2 := by
        have hlt' : n * c < n * 2 := by
          rw [← hc, Nat.mul_comm n 2]
          exact hlt
        exact Nat.lt_of_mul_lt_mul_left hlt'
      omega
    rw [hc1, mul_one] at hc
    omega
  · have h1 : 2 ^ k₂ * 2 ^ (n - k₁) ≡ 2 ^ k₁ * 2 ^ (n - k₁) [MOD 2 ^ n - 1] :=
      h.symm.mul_right _
    rw [← pow_add, ← pow_add, Nat.add_sub_of_le (le_of_lt hk₁)] at h1
    have h3 : 2 ^ (k₂ + (n - k₁)) ≡ 1 [MOD 2 ^ n - 1] := h1.trans h2n
    have hd : n ∣ k₂ + (n - k₁) := dvd_of_pow_two_modEq_one hn h3
    obtain ⟨c, hc⟩ := hd
    have hlt : k₂ + (n - k₁) < 2 * n := by omega
    have hpos : 0 < k₂ + (n - k₁) := by omega
    have hc1 : c = 1 := by
      have hcpos : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        omega
      have hclt : c < 2 := by
        have hlt' : n * c < n * 2 := by
          rw [← hc, Nat.mul_comm n 2]
          exact hlt
        exact Nat.lt_of_mul_lt_mul_left hlt'
      omega
    rw [hc1, mul_one] at hc
    omega

end Work.Higman.H8
