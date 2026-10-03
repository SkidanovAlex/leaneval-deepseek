/-
# `Submission.Work.FIArea7CF.r2count_upper` — clash-free copy of `Submission.Work.FIArea7.r2count_upper`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.R2countDefs
import Submission.Work.FIArea7CF.exists_gaussPrime_gnorm_eq
import Submission.Work.FIArea7CF.dvd_gaussInt_of_dvd_gnorm
import Submission.Work.FIArea7.prod_factorization_filter_pow_mul
import Submission.Work.FIArea7.not_dvd_div_pow_factorization
import Submission.Work.FIArea7CF.card_Sz_one

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

local notation "gnorm" => Work.FIPlan.gnorm

/-! ## Auxiliary norm facts -/

lemma gnorm_one_add_I : gnorm (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) = 2 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_def]

lemma prime_one_add_I : Prime (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) :=
  prime_of_gnorm_prime (p := 2) (by norm_num) gnorm_one_add_I

lemma one_add_I_ne_zero : (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) ≠ 0 := by
  intro h
  have h2 : gnorm (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) = gnorm (0 : GaussianInt) := by rw [h]
  rw [gnorm_one_add_I] at h2
  simp [Work.FIPlan.gnorm] at h2

lemma natCast_ne_zero {p : ℕ} (hp : p ≠ 0) : ((p : ℕ) : GaussianInt) ≠ 0 := by
  intro h
  refine hp ?_
  have h1 := congrArg Zsqrtd.re h
  simpa using h1

/-- The map `w ↦ w * π` identifies the `z` of norm `|π|²N` divisible by `π` with the `w`
of norm `N`. -/
lemma filter_dvd_eq_image (π : GaussianInt) (hπ : π ≠ 0) (N : ℕ) :
    (Sz (gnorm π * N)).filter (fun z => π ∣ z) = (Sz N).image (fun w => w * π) := by
  have hgπ : 0 < gnorm π := Nat.pos_of_ne_zero (fun h => hπ (gnorm_eq_zero_iff.mp h))
  ext z
  constructor
  · intro hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzS, ⟨w, rfl⟩⟩ := hz
    rw [Finset.mem_image]
    have h2 : gnorm (π * w) = gnorm π * N := (mem_Sz_iff.mp hzS).1
    have h3 : gnorm π * gnorm w = gnorm π * N := by rw [← gnorm_mul, h2]
    have hgw : gnorm w = N := Nat.eq_of_mul_eq_mul_left hgπ h3
    exact ⟨w, mem_Sz_of_gnorm_eq hgw, by rw [mul_comm]⟩
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨w, hwS, hwz⟩ := hz
    rw [Finset.mem_filter]
    refine ⟨mem_Sz_of_gnorm_eq ?_, w, by rw [← hwz, mul_comm]⟩
    rw [← hwz, gnorm_mul, (mem_Sz_iff.mp hwS).1, mul_comm]

lemma card_filter_dvd_eq (π : GaussianInt) (hπ : π ≠ 0) (N : ℕ) :
    ((Sz (gnorm π * N)).filter (fun z => π ∣ z)).card = (Sz N).card := by
  rw [filter_dvd_eq_image π hπ N,
    Finset.card_image_of_injective _ (fun a b hab => mul_right_cancel₀ hπ hab)]

/-- Splitting `Sz (|π|²N)` according to divisibility by `π`. -/
lemma card_Sz_mul (π : GaussianInt) (hπ : π ≠ 0) (N : ℕ) :
    (Sz (gnorm π * N)).card = (Sz N).card
      + ((Sz (gnorm π * N)).filter (fun z => ¬ π ∣ z)).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Sz (gnorm π * N)) (p := fun z => π ∣ z)
  rw [card_filter_dvd_eq π hπ N] at h
  exact h.symm

/-- The `z` of norm `|π|ⁱN` not divisible by `π` inject into the `z` of norm `N`. -/
lemma card_filter_notDvd_le (π : GaussianInt) (hπ : Prime π) (N i : ℕ) :
    ((Sz (gnorm π ^ i * N)).filter (fun z => ¬ π ∣ z)).card ≤ (Sz N).card := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hsp0 : star π ≠ 0 := fun h => hπ0 (by rw [← star_star π, h, star_zero])
  have hgpos : 0 < gnorm π := Nat.pos_of_ne_zero (fun h => hπ0 (gnorm_eq_zero_iff.mp h))
  have hsub : (Sz (gnorm π ^ i * N)).filter (fun z => ¬ π ∣ z) ⊆
      (Sz N).image (fun w => w * (star π) ^ i) := by
    intro z hz
    rw [Finset.mem_filter, mem_Sz_iff] at hz
    obtain ⟨⟨hg, -⟩, hznd⟩ := hz
    have hdvd : π ^ i ∣ z * star z := by
      rw [mul_star_eq_gnorm, hg]
      have hcast : ((gnorm π ^ i * N : ℕ) : GaussianInt)
          = π ^ i * ((star π) ^ i * (N : GaussianInt)) := by
        rw [Nat.cast_mul, Nat.cast_pow, ← mul_star_eq_gnorm π, mul_pow]
        ring
      rw [hcast]
      exact dvd_mul_right _ _
    obtain ⟨c, hc⟩ := hπ.pow_dvd_of_dvd_mul_left i hznd hdvd
    have hzdiv : z = (star π) ^ i * star c := by
      have h := congrArg star hc
      rw [star_mul, star_pow, star_star] at h
      rw [h, mul_comm]
    rw [Finset.mem_image]
    refine ⟨star c, mem_Sz_of_gnorm_eq ?_, ?_⟩
    · have h1 : gnorm z = gnorm ((star π) ^ i) * gnorm (star c) := by rw [hzdiv, gnorm_mul]
      rw [gnorm_pow, gnorm_star, hg] at h1
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hgpos i) h1).symm
    · rw [hzdiv]; exact mul_comm _ _
  calc ((Sz (gnorm π ^ i * N)).filter (fun z => ¬ π ∣ z)).card
      ≤ ((Sz N).image (fun w => w * (star π) ^ i)).card := Finset.card_le_card hsub
    _ = (Sz N).card :=
        Finset.card_image_of_injective _ (fun a b hab => mul_right_cancel₀ (pow_ne_zero i hsp0) hab)

/-- `Sz (|π|^e N)` grows by at most the factor `e+1` when `π` is a Gaussian prime. -/
lemma card_Sz_pow_mul_le (π : GaussianInt) (hπ : Prime π) (e N : ℕ) :
    (Sz (gnorm π ^ e * N)).card ≤ (e + 1) * (Sz N).card := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hkey : gnorm π ^ (e + 1) * N = gnorm π * (gnorm π ^ e * N) := by ring
    rw [hkey, card_Sz_mul π hπ.ne_zero (gnorm π ^ e * N)]
    have hle : ((Sz (gnorm π * (gnorm π ^ e * N))).filter (fun z => ¬ π ∣ z)).card
        ≤ (Sz N).card := by
      rw [← hkey]
      exact card_filter_notDvd_le π hπ N (e + 1)
    calc (Sz (gnorm π ^ e * N)).card
          + ((Sz (gnorm π * (gnorm π ^ e * N))).filter (fun z => ¬ π ∣ z)).card
        ≤ (e + 1) * (Sz N).card + (Sz N).card := add_le_add ih hle
      _ = (Nat.succ e + 1) * (Sz N).card := by rw [Nat.succ_eq_add_one]; ring

/-! ## The ramified prime `2 = (1+i)(1-i)` -/

lemma filter_notDvd_one_add_I (N : ℕ) :
    (Sz (2 * N)).filter (fun z => ¬ (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∣ z) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  rw [Finset.mem_filter, mem_Sz_iff] at hz
  obtain ⟨⟨hg, -⟩, hznd⟩ := hz
  have htwo : ((2 : ℕ) : GaussianInt)
      = (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) * star (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) := by
    rw [← gnorm_one_add_I]
    exact (mul_star_eq_gnorm _).symm
  have hdvd2 : ((2 : ℕ) : GaussianInt) ∣ z * star z := by
    refine ⟨(N : ℕ), ?_⟩
    rw [mul_star_eq_gnorm, hg, Nat.cast_mul]
  have h1 : (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∣ z * star z :=
    (show (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∣ ((2 : ℕ) : GaussianInt) from
      ⟨star _, htwo⟩).trans hdvd2
  rcases prime_one_add_I.dvd_or_dvd h1 with h | h
  · exact hznd h
  · obtain ⟨c, hc⟩ := h
    have h2 : star (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∣ z := ⟨star c, by
      have hh := congrArg star hc
      rw [star_mul, star_star] at hh
      rw [hh, mul_comm]⟩
    refine hznd (((show (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt)
        ∣ star (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) from
      ⟨-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), by decide⟩)).trans h2)

lemma card_Sz_two_mul (N : ℕ) : (Sz (2 * N)).card = (Sz N).card := by
  have h := card_Sz_mul (⟨(1 : ℤ), (1 : ℤ)⟩ : GaussianInt) one_add_I_ne_zero N
  rw [gnorm_one_add_I] at h
  rw [h, filter_notDvd_one_add_I N, Finset.card_empty, add_zero]

lemma card_Sz_two_pow_mul (e N : ℕ) : (Sz (2 ^ e * N)).card = (Sz N).card := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [show 2 ^ (e + 1) * N = 2 * (2 ^ e * N) by ring, card_Sz_two_mul, ih]

/-! ## The inert primes `p ≡ 3 (mod 4)` -/

lemma filter_notDvd_natCast_mod_three (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (N : ℕ) :
    (Sz (p ^ 2 * N)).filter (fun z => ¬ ((p : ℕ) : GaussianInt) ∣ z) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  rw [Finset.mem_filter, mem_Sz_iff] at hz
  obtain ⟨⟨hg, -⟩, hznd⟩ := hz
  exact hznd (dvd_gaussInt_of_dvd_gnorm hp h3 ⟨p * N, by rw [hg]; ring⟩)

lemma card_Sz_prime_sq_mul (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (N : ℕ) :
    (Sz (p ^ 2 * N)).card = (Sz N).card := by
  have h := card_Sz_mul ((p : ℕ) : GaussianInt) (natCast_ne_zero hp.ne_zero) N
  rw [gnorm_natCast] at h
  rw [h, filter_notDvd_natCast_mod_three p hp h3 N, Finset.card_empty, add_zero]

lemma card_Sz_prime_mul_eq_zero (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (N : ℕ)
    (hN : ¬ p ∣ N) : (Sz (p * N)).card = 0 := by
  rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  rw [mem_Sz_iff] at hz
  obtain ⟨hg, -⟩ := hz
  obtain ⟨w, hw⟩ := dvd_gaussInt_of_dvd_gnorm hp h3 (show p ∣ gnorm z from ⟨N, by rw [hg]⟩)
  have h1 : gnorm z = gnorm ((p : ℕ) : GaussianInt) * gnorm w := by rw [hw, gnorm_mul]
  rw [gnorm_natCast, hg] at h1
  have h2 : p * gnorm w = N := by
    have h3' : p * (p * gnorm w) = p * N := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h3'
  exact hN ⟨gnorm w, h2.symm⟩

/-- Cutting two `p`-powers off the norm does not increase the count. -/
lemma card_Sz_mul_prime_sq_le (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (e N : ℕ) :
    (Sz (p ^ (e + 2) * N)).card ≤ (Sz (p ^ e * N)).card := by
  have hp0 : ((p : ℕ) : GaussianInt) ≠ 0 := natCast_ne_zero hp.ne_zero
  have hsub : Sz (p ^ (e + 2) * N) ⊆
      (Sz (p ^ e * N)).image (fun w => w * ((p : ℕ) : GaussianInt)) := by
    intro z hz
    rw [mem_Sz_iff] at hz
    obtain ⟨hg, -⟩ := hz
    obtain ⟨w, hw⟩ := dvd_gaussInt_of_dvd_gnorm hp h3
      (show p ∣ gnorm z from ⟨p ^ (e + 1) * N, by rw [hg]; ring⟩)
    rw [Finset.mem_image]
    refine ⟨w, mem_Sz_of_gnorm_eq ?_, ?_⟩
    · have h1 : gnorm z = gnorm ((p : ℕ) : GaussianInt) * gnorm w := by rw [hw, gnorm_mul]
      rw [gnorm_natCast, hg] at h1
      have h2 : p ^ 2 * (p ^ e * N) = p ^ 2 * gnorm w := by rw [← h1]; ring
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h2).symm
    · rw [hw]; exact mul_comm _ _
  calc (Sz (p ^ (e + 2) * N)).card
      ≤ ((Sz (p ^ e * N)).image (fun w => w * ((p : ℕ) : GaussianInt))).card :=
        Finset.card_le_card hsub
    _ = (Sz (p ^ e * N)).card :=
        Finset.card_image_of_injective _ (fun a b hab => mul_right_cancel₀ hp0 hab)

lemma card_Sz_mod_three_even (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (k N : ℕ) :
    (Sz (p ^ (2 * k) * N)).card = (Sz N).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : p ^ (2 * (k + 1)) * N = p ^ 2 * (p ^ (2 * k) * N) := by ring
    rw [h, card_Sz_prime_sq_mul p hp h3 (p ^ (2 * k) * N), ih]

lemma card_Sz_mod_three_odd (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (e N : ℕ)
    (he : Odd e) (hN : ¬ p ∣ N) : (Sz (p ^ e * N)).card = 0 := by
  obtain ⟨k, hk⟩ := he
  subst hk
  induction k with
  | zero => simpa using card_Sz_prime_mul_eq_zero p hp h3 N hN
  | succ k ih =>
    have hgoal : (Sz (p ^ (2 * (k + 1) + 1) * N)).card ≤ 0 := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
      calc (Sz (p ^ (2 * k + 1 + 2) * N)).card ≤ (Sz (p ^ (2 * k + 1) * N)).card :=
            card_Sz_mul_prime_sq_le p hp h3 (2 * k + 1) N
        _ = 0 := ih
    exact Nat.eq_zero_of_le_zero hgoal

/-! ## The main bound -/

theorem main_bound (n : ℕ) :
    (Sz n).card ≤ 4 * ∏ p ∈ n.primeFactors.filter (fun p => p % 4 = 1),
      (n.factorization p + 1) := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hsub : Sz 0 ⊆ {0} := by
      intro z hz
      rw [Finset.mem_singleton]
      exact gnorm_eq_zero_iff.mp (mem_Sz_iff.mp hz).1
    have hcard : (Sz 0).card ≤ 1 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hR : 4 * ∏ p ∈ (0 : ℕ).primeFactors.filter (fun p => p % 4 = 1),
        ((0 : ℕ).factorization p + 1) = 4 := by simp
    rw [hR]
    omega
  · rcases eq_or_lt_of_le (show 1 ≤ n from hnpos) with h1 | h1
    · rw [← h1, card_Sz_one]
      simp
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have hn0 : n ≠ 0 := by omega
      set e := n.factorization p with he
      set m := n / p ^ e with hm
      have hpe_dvd : p ^ e ∣ n := by
        rw [he]
        exact (hp.pow_dvd_iff_le_factorization hn0).mpr le_rfl
      have hn_eq : n = p ^ e * m := by
        rw [hm]
        exact (Nat.mul_div_cancel' hpe_dvd).symm
      have hm_ndvd : ¬ p ∣ m := by
        rw [hm]
        exact not_dvd_div_pow_factorization n p hn0 hp
      have he1 : 1 ≤ e := by
        rw [he]
        exact (hp.dvd_iff_one_le_factorization hn0).mp hpdvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hn_eq
          omega
        · exact h
      have hm_lt : m < n := by
        rw [hn_eq]
        have h2 : 2 ≤ p ^ e := by
          have hle : p ^ 1 ≤ p ^ e := pow_le_pow_right₀ (le_of_lt hp.one_lt) he1
          rw [pow_one] at hle
          exact le_trans hp.two_le hle
        calc m = 1 * m := (one_mul m).symm
          _ < 2 * m := by omega
          _ ≤ p ^ e * m := Nat.mul_le_mul_right m h2
      have IH : (Sz m).card ≤ 4 * ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1),
          (m.factorization q + 1) := ih m hm_lt
      have key := prod_factorization_filter_pow_mul p e m hp hm_ndvd hm_pos.ne'
      have key' : ∏ q ∈ n.primeFactors.filter (fun q => q % 4 = 1),
            (n.factorization q + 1)
          = (if p % 4 = 1 then e + 1 else 1) *
            ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1), (m.factorization q + 1) := by
        rw [hn_eq]
        exact key
      rcases eq_or_ne p 2 with hp2 | hp2
      · subst hp2
        have hcard : (Sz n).card = (Sz m).card := by
          rw [hn_eq]
          exact card_Sz_two_pow_mul e m
        have hR : 4 * (∏ q ∈ n.primeFactors.filter (fun q => q % 4 = 1),
              (n.factorization q + 1))
            = 4 * ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1),
                (m.factorization q + 1) := by
          rw [key', if_neg (by norm_num : ¬ (2 : ℕ) % 4 = 1), one_mul]
        rw [hR, hcard]
        exact IH
      · by_cases hp41 : p % 4 = 1
        · obtain ⟨π, hπp, hπg⟩ := exists_gaussPrime_gnorm_eq p hp hp41
          have hcard : (Sz n).card ≤ (e + 1) * (Sz m).card := by
            rw [hn_eq]
            have h := card_Sz_pow_mul_le π hπp e m
            rwa [hπg] at h
          have hR : 4 * (∏ q ∈ n.primeFactors.filter (fun q => q % 4 = 1),
                (n.factorization q + 1))
              = (e + 1) * (4 * ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1),
                  (m.factorization q + 1)) := by
            rw [key', if_pos hp41]; ring
          calc (Sz n).card ≤ (e + 1) * (Sz m).card := hcard
            _ ≤ (e + 1) * (4 * ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1),
                  (m.factorization q + 1)) := Nat.mul_le_mul_left _ IH
            _ = 4 * (∏ q ∈ n.primeFactors.filter (fun q => q % 4 = 1),
                  (n.factorization q + 1)) := hR.symm
        · have hp43 : p % 4 = 3 := by
            have hod : Odd p := hp.odd_of_ne_two hp2
            obtain ⟨k, hk⟩ := hod
            omega
          have hR : 4 * (∏ q ∈ n.primeFactors.filter (fun q => q % 4 = 1),
                (n.factorization q + 1))
              = 4 * ∏ q ∈ m.primeFactors.filter (fun q => q % 4 = 1),
                  (m.factorization q + 1) := by
            rw [key', if_neg hp41, one_mul]
          rcases Nat.even_or_odd e with hev | hodd
          · obtain ⟨k, hk⟩ := hev
            have hcard : (Sz n).card = (Sz m).card := by
              rw [hn_eq, hk, show k + k = 2 * k by ring]
              exact card_Sz_mod_three_even p hp hp43 k m
            rw [hR, hcard]
            exact IH
          · have hcard : (Sz n).card = 0 := by
              rw [hn_eq]
              exact card_Sz_mod_three_odd p hp hp43 e m hodd hm_ndvd
            rw [hcard]
            exact Nat.zero_le _

theorem r2count_upper (n : ℕ) (hn : 0 < n) :
    Work.FIArea7.r2count n ≤ 4 * ∏ p ∈ n.primeFactors.filter (fun p => p % 4 = 1), (n.factorization p + 1) := by
  rw [r2count_eq_Sz_card]
  exact main_bound n

end

end Work.FIArea7
