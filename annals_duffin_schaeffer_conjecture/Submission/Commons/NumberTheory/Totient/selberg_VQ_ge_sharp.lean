import Mathlib
import Submission.Commons.NumberTheory.Totient.selberg_VQ_ge
import Submission.Commons.NumberTheory.Totient.sum_mu_sq_div_totient_ge_log_add_one
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_sharp
import Submission.Commons.NumberTheory.Mertens.eulerMascheroni_exp_neg_lower

namespace Commons.NumberTheory.Totient

open scoped BigOperators
open Finset

noncomputable section

private lemma divisors_mul_prime (Q p : ℕ) (hp : Nat.Prime p) (_hpQ : ¬ p ∣ Q) (hQ : Q ≠ 0) :
    (Q * p).divisors = Q.divisors ∪ Q.divisors.image (fun d => d * p) := by
  have hQp0 : Q * p ≠ 0 := mul_ne_zero hQ hp.ne_zero
  ext e
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hedvd, _⟩
    by_cases hpe : p ∣ e
    · right
      refine ⟨e / p, ⟨?_, hQ⟩, ?_⟩
      · have he : p * (e / p) = e := Nat.mul_div_cancel' hpe
        have h' : e ∣ p * Q := by rwa [mul_comm Q p] at hedvd
        have h : p * (e / p) ∣ p * Q := by rwa [← he] at h'
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos h
      · rw [mul_comm, Nat.mul_div_cancel' hpe]
    · left
      exact ⟨((hp.coprime_iff_not_dvd).mpr hpe).symm.dvd_of_dvd_mul_right hedvd, hQ⟩
  · rintro (⟨hedvd, _⟩ | ⟨d, ⟨hdvd, _⟩, rfl⟩)
    · exact ⟨hedvd.trans (Nat.dvd_mul_right Q p), hQp0⟩
    · exact ⟨mul_dvd_mul_right hdvd p, hQp0⟩

/-- `Tle (Q*p) z = Tle Q z + (1/(p-1)) * Tle Q (z/p)` for `p` prime, `p ∤ Q`, `Q ≠ 0`. -/
private lemma Tle_mul_prime (Q p z : ℕ) (hp : Nat.Prime p) (hpQ : p ∉ Q.primeFactors)
    (hQ : Q ≠ 0) :
    Tle (Q * p) z = Tle Q z + ((p : ℝ) - 1)⁻¹ * Tle Q (z / p) := by
  have hpndvd : ¬ p ∣ Q := fun h => hpQ ((Nat.mem_primeFactors).mpr ⟨hp, h, hQ⟩)
  have hdisj : Disjoint Q.divisors (Q.divisors.image (fun d => d * p)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at hb
    obtain ⟨d, hd, hdp⟩ := hb
    have hpda : p ∣ a := by rw [← hdp]; exact dvd_mul_left p d
    have hpa : p ∣ Q := hpda.trans (Nat.dvd_of_mem_divisors ha)
    exact hpndvd hpa
  have hinj : Set.InjOn (fun d => d * p) (Q.divisors : Set ℕ) :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hp.pos hab
  unfold Tle
  rw [divisors_mul_prime Q p hp hpndvd hQ, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image hinj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ Q := Nat.dvd_of_mem_divisors hd
  have hpnd : ¬ p ∣ d := fun h => hpndvd (h.trans hdvd)
  have hcop : Nat.Coprime d p := ((hp.coprime_iff_not_dvd).mpr hpnd).symm
  have htot : (d * p).totient = d.totient * (p - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]
  by_cases hle : d * p ≤ z
  · have hddiv : d ≤ z / p := (Nat.le_div_iff_mul_le hp.pos).mpr hle
    rw [if_pos hle, if_pos hddiv]
    have hcast : ((d.totient * (p - 1) : ℕ) : ℝ) = (d.totient : ℝ) * ((p:ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hp.one_le]; push_cast; ring
    rw [htot, hcast, mul_inv, mul_comm]
  · have hddiv : ¬ d ≤ z / p := fun h => hle ((Nat.le_div_iff_mul_le hp.pos).mp h)
    rw [if_neg hle, if_neg hddiv, mul_zero]

/-- `Vp (Q*p) = Vp Q * (1 - 1/p)` for `p` prime, `p ∉ Q.primeFactors`, `Q ≠ 0`. -/
private lemma Vp_mul_prime (Q p : ℕ) (hp : Nat.Prime p) (hpQ : p ∉ Q.primeFactors) (hQ : Q ≠ 0) :
    Vp (Q * p) = Vp Q * (1 - (p : ℝ)⁻¹) := by
  unfold Vp
  rw [Nat.primeFactors_mul hQ hp.ne_zero, hp.primeFactors]
  rw [Finset.prod_union]
  · rw [Finset.prod_singleton]
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at hb
    rw [hb] at ha
    exact hpQ ha


/-- Adding a coprime prime factor does not increase `LHS`. -/
private lemma LHS_mul_prime (Q p z : ℕ) (hp : Nat.Prime p) (hpQ : p ∉ Q.primeFactors)
    (hQ : Q ≠ 0) : LHS (Q * p) z ≤ LHS Q z := by
  unfold LHS
  rw [Tle_mul_prime Q p z hp hpQ hQ, Vp_mul_prime Q p hp hpQ hQ]
  have hle : Tle Q (z / p) ≤ Tle Q z := by
    unfold Tle
    apply Finset.sum_le_sum
    intro d hd
    have : d ≤ z / p → d ≤ z := fun h => h.trans (Nat.div_le_self z p)
    by_cases h : d ≤ z / p
    · rw [if_pos h, if_pos (this h)]
    · rw [if_neg h]
      by_cases hz : d ≤ z
      · rw [if_pos hz]; positivity
      · rw [if_neg hz]
  have hv : 0 ≤ Vp Q := by
    unfold Vp
    apply Finset.prod_nonneg
    intro p' hp'
    have hp'1 : (1:ℝ) ≤ (p':ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp').one_le
    have : (p':ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp'1
    linarith
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hp1nz : (p:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    linarith
  have key : (Tle Q z + ((p:ℝ) - 1)⁻¹ * Tle Q (z / p)) * (Vp Q * (1 - (p:ℝ)⁻¹))
      - Tle Q z * Vp Q = Vp Q * (p:ℝ)⁻¹ * (Tle Q (z / p) - Tle Q z) := by
    field_simp
    ring
  have hlast : Vp Q * (p:ℝ)⁻¹ * (Tle Q (z / p) - Tle Q z) ≤ 0 := by
    have h1 : Tle Q (z / p) - Tle Q z ≤ 0 := sub_nonpos.mpr hle
    have h2 : 0 ≤ Vp Q * (p:ℝ)⁻¹ := mul_nonneg hv (by positivity)
    nlinarith [h1, h2]
  linarith [key, hlast]

/-- Adding a finite product of distinct primes coprime to `N` does not increase `LHS`. -/
private lemma LHS_mul_prod_primes_le : ∀ (S : Finset ℕ) (N z : ℕ),
    N ≠ 0 → Squarefree N → (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, p ∉ N.primeFactors) →
    LHS (N * ∏ p ∈ S, p) z ≤ LHS N z := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro N z hN hNsq hS hdisj; simp
  | insert a s ha ih =>
      intro N z hN hNsq hS hdisj
      have hap : Nat.Prime a := hS a (Finset.mem_insert_self a s)
      have ha_nin : a ∉ N.primeFactors := hdisj a (Finset.mem_insert_self a s)
      have hsp : ∀ p ∈ s, Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have hsdisj : ∀ p ∈ s, p ∉ N.primeFactors := fun p hp => hdisj p (Finset.mem_insert_of_mem hp)
      rw [Finset.prod_insert ha]
      have hNa0 : N * a ≠ 0 := mul_ne_zero hN hap.ne_zero
      have hNacop : Nat.Coprime N a :=
        ((hap.coprime_iff_not_dvd).mpr
          (fun h => ha_nin (Nat.mem_primeFactors.mpr ⟨hap, h, hN⟩))).symm
      have hNasq : Squarefree (N * a) := (Nat.squarefree_mul hNacop).mpr ⟨hNsq, hap.squarefree⟩
      have hsdisj' : ∀ p ∈ s, p ∉ (N * a).primeFactors := by
        intro p hp
        rw [Nat.primeFactors_mul hN hap.ne_zero, hap.primeFactors]
        intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hsdisj p hp h
        · rw [Finset.mem_singleton] at h
          exact ha (h ▸ hp)
      calc LHS (N * (a * ∏ p ∈ s, p)) z
            = LHS ((N * a) * ∏ p ∈ s, p) z := by
              rw [show N * (a * ∏ p ∈ s, p) = (N * a) * ∏ p ∈ s, p from by ring]
        _ ≤ LHS (N * a) z := ih (N * a) z hNa0 hNasq hsp hsdisj'
        _ ≤ LHS N z := LHS_mul_prime N a z hap ha_nin hN

/-- Reduction to the primorial: for squarefree `P` with all prime factors `≤ y`,
`LHS (primorial y) (√y) ≤ LHS P (√y)`. -/
private lemma LHS_primorial_le (P y : ℕ) (hP : Squarefree P)
    (hsub : P.primeFactors ⊆ Nat.primesLE y) :
    LHS (primorial y) (Nat.sqrt y) ≤ LHS P (Nat.sqrt y) := by
  rcases eq_or_ne P 0 with h0 | hP0
  · subst h0
    exact absurd hP not_squarefree_zero
  set S : Finset ℕ := Nat.primesLE y \ P.primeFactors with hSdef
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  have hdisj : ∀ p ∈ S, p ∉ P.primeFactors := fun p hp => (Finset.mem_sdiff.mp hp).2
  have hprod : P * ∏ p ∈ S, p = primorial y := by
    have h1 : (∏ p ∈ S, p) * ∏ p ∈ P.primeFactors, p = ∏ p ∈ Nat.primesLE y, p := by
      rw [hSdef]; exact Finset.prod_sdiff hsub
    rw [Nat.prod_primeFactors_of_squarefree hP] at h1
    rw [primorial, ← h1, mul_comm]
  rw [← hprod]
  exact LHS_mul_prod_primes_le S P (Nat.sqrt y) hP0 hP hSprime hdisj


/-- `Nat.sqrt y ≤ y`. -/
private lemma primeFactors_primorial_subset_aux : True := trivial

private lemma divisors_primorial_filter (y z : ℕ) (hz : z ≤ y) :
    (primorial y).divisors.filter (fun d => d ≤ z) = (Finset.Icc 1 z).filter Squarefree := by
  apply Finset.Subset.antisymm
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hdz⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, hdz⟩, Squarefree.squarefree_of_dvd hdvd (primorial_squarefree y)⟩
    have : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero (primorial_ne_zero y))
    omega
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdz⟩, hdsq⟩ := hd
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, primorial_ne_zero y⟩, hdz⟩
    have hPF : d.primeFactors ⊆ Nat.primesLE y := by
      intro p hp
      rw [Nat.mem_primesLE]
      exact ⟨le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
              (le_trans hdz hz), Nat.prime_of_mem_primeFactors hp⟩
    rw [primorial, ← Nat.prod_primeFactors_of_squarefree hdsq]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hPF

private lemma Tle_primorial_eq (y z : ℕ) (hz : z ≤ y) :
    Tle (primorial y) z =
      ∑ r ∈ Finset.Icc 1 z, ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 / (Nat.totient r : ℝ) := by
  unfold Tle
  rw [← Finset.sum_filter]
  rw [divisors_primorial_filter y z hz]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hsq : Squarefree r
  · have hmu : ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 = 1 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]; norm_num
    rw [if_pos hsq, hmu, one_div]
  · have hmu : ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 = 0 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num
    rw [if_neg hsq, hmu]; simp

lemma LHS_primorial_eq (y : ℕ) :
    LHS (primorial y) (Nat.sqrt y) =
      (∑ r ∈ Finset.Icc 1 (Nat.sqrt y),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 / (Nat.totient r : ℝ))
      * ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
  rw [LHS, Tle_primorial_eq y (Nat.sqrt y) (Nat.sqrt_le_self y), Vp, primeFactors_primorial]

/-! ## Monotonicity of the prime product and the finite range -/

private lemma primesLE_prod_mono {y y' : ℕ} (h : y ≤ y') :
    ∏ p ∈ Nat.primesLE y', (1 - (p:ℝ)⁻¹) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨le_trans (Nat.mem_primesLE.mp hp).1 h, (Nat.mem_primesLE.mp hp).2⟩
  · intro p hp
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)
  · intro p hp _
    show (1 - (p:ℝ)⁻¹) ≤ 1
    have : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
    linarith

private lemma prod_primesLE_97_ge : (0.12:ℝ) ≤ ∏ p ∈ Nat.primesLE 97, (1 - (p:ℝ)⁻¹) := by
  have h : Nat.primesLE 97 = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} : Finset ℕ) := by decide
  rw [h]; norm_num

private lemma prod_primesLE_99_ge : (0.12:ℝ) ≤ ∏ p ∈ Nat.primesLE 99, (1 - (p:ℝ)⁻¹) := by
  have h : Nat.primesLE 99 = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} : Finset ℕ) := by decide
  rw [h]; norm_num

private lemma prod_primesLE_15_ge : (0.19:ℝ) ≤ ∏ p ∈ Nat.primesLE 15, (1 - (p:ℝ)⁻¹) := by
  have h : Nat.primesLE 15 = ({2,3,5,7,11,13} : Finset ℕ) := by decide
  rw [h]; norm_num

private lemma prod_primesLE_8_eq : ∏ p ∈ Nat.primesLE 8, (1 - (p:ℝ)⁻¹) = 8/35 := by
  have h : Nat.primesLE 8 = ({2,3,5,7} : Finset ℕ) := by decide
  rw [h]; norm_num

private lemma prod_primesLE_3_eq : ∏ p ∈ Nat.primesLE 3, (1 - (p:ℝ)⁻¹) = 1/3 := by
  have h : Nat.primesLE 3 = ({2,3} : Finset ℕ) := by decide
  rw [h]; norm_num

private lemma log2_ge : (0.69:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
private lemma log3_ge : (1.09:ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
private lemma log4_ge : (1.38:ℝ) ≤ Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
  rw [h]; linarith [Real.log_two_gt_d9]

/-- Finite range `y < 100`: `LHS (primorial y) (√y) ≥ 7/25`. -/
private lemma primorial_bound_small (y : ℕ) (hy1 : 1 ≤ y) (hy : y < 100) :
    (7/25 : ℝ) ≤ LHS (primorial y) (Nat.sqrt y) := by
  rw [LHS_primorial_eq]
  rcases lt_or_ge y 4 with h4 | h4
  · -- 1 ≤ y ≤ 3
    have hz1 : 1 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 1) (n := y)).mpr (by rw [pow_two]; omega)
    have hS : (1:ℝ) ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt y), ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 / (Nat.totient r : ℝ) := by
      have h1 := sum_mu_sq_div_totient_ge_log_add_one (Nat.sqrt y) hz1
      have hlog : (0:ℝ) ≤ Real.log (Nat.sqrt y : ℝ) := Real.log_nonneg (by exact_mod_cast hz1)
      linarith
    have hM : (1/3:ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
      have hy3 : y ≤ 3 := by omega
      have := primesLE_prod_mono hy3
      rw [prod_primesLE_3_eq] at this
      linarith [this]
    nlinarith [hS, hM]
  · rcases lt_or_ge y 9 with h9 | h9
    · -- 4 ≤ y ≤ 8
      have hz2 : 2 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 2) (n := y)).mpr (by rw [pow_two]; omega)
      have hz1 : 1 ≤ Nat.sqrt y := le_trans (by norm_num : (1:ℕ) ≤ 2) hz2
      have hS : (1.69:ℝ) ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt y), ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 / (Nat.totient r : ℝ) := by
        have h1 := sum_mu_sq_div_totient_ge_log_add_one (Nat.sqrt y) hz1
        have hlog : (0.69:ℝ) ≤ Real.log (Nat.sqrt y : ℝ) :=
          le_trans log2_ge (Real.log_le_log (by norm_num) (by exact_mod_cast hz2))
        linarith [h1, hlog]
      have hM : (8/35:ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
        have hy8 : y ≤ 8 := by omega
        have := primesLE_prod_mono hy8
        rw [prod_primesLE_8_eq] at this
        linarith [this]
      nlinarith [hS, hM]
    · rcases lt_or_ge y 16 with h16 | h16
      · -- 9 ≤ y ≤ 15
        have hz3 : 3 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 3) (n := y)).mpr (by rw [pow_two]; omega)
        have hz1 : 1 ≤ Nat.sqrt y := le_trans (by norm_num : (1:ℕ) ≤ 3) hz3
        have hS : (2.09:ℝ) ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt y), ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 / (Nat.totient r : ℝ) := by
          have h1 := sum_mu_sq_div_totient_ge_log_add_one (Nat.sqrt y) hz1
          have hlog : (1.09:ℝ) ≤ Real.log (Nat.sqrt y : ℝ) :=
            le_trans log3_ge (Real.log_le_log (by norm_num) (by exact_mod_cast hz3))
          linarith [h1, hlog]
        have hM : (0.19:ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
          have hy15 : y ≤ 15 := by omega
          exact le_trans prod_primesLE_15_ge (primesLE_prod_mono hy15)
        nlinarith [hS, hM]
      · -- 16 ≤ y ≤ 99
        have hz4 : 4 ≤ Nat.sqrt y := by
          have h4sq : (4:ℕ)^2 = 16 := by norm_num
          refine (Nat.le_sqrt' (m := 4) (n := y)).mpr ?_
          rw [h4sq]; exact h16
        have hz1 : 1 ≤ Nat.sqrt y := le_trans (by norm_num : (1:ℕ) ≤ 4) hz4
        have hS : (2.38:ℝ) ≤ ∑ r ∈ Finset.Icc 1 (Nat.sqrt y), ((ArithmeticFunction.moebius r : ℤ) : ℝ)^2 / (Nat.totient r : ℝ) := by
          have h1 := sum_mu_sq_div_totient_ge_log_add_one (Nat.sqrt y) hz1
          have hlog : (1.38:ℝ) ≤ Real.log (Nat.sqrt y : ℝ) :=
            le_trans log4_ge (Real.log_le_log (by norm_num) (by exact_mod_cast hz4))
          linarith [h1, hlog]
        have hM : (0.12:ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
          have hy99 : y ≤ 99 := by omega
          exact le_trans prod_primesLE_99_ge (primesLE_prod_mono hy99)
        nlinarith [hS, hM]

/-- The prime-product lower bound of the main arithmetic. -/
private lemma arith_bound (y : ℕ) (hy : 100 ≤ y) (S M : ℝ)
    (hS : Real.log (Nat.sqrt y) + 1 ≤ S)
    (hM : Real.exp (-Real.eulerMascheroniConstant)
        * Real.exp (-(3/2) / Real.log (y:ℝ)) / Real.log (y:ℝ) ≤ M) :
    (7/25 : ℝ) ≤ S * M := by
  set L := Real.log (y:ℝ) with hLdef
  have hypos : (0:ℝ) < (y:ℝ) := by positivity
  have hy1 : (1:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 1 < y)
  have hLpos : (0:ℝ) < L := by rw [hLdef]; exact Real.log_pos hy1
  have hL : (4.5:ℝ) ≤ L := by
    rw [hLdef]
    have h2 : (0.6931471803:ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
    have h5 : (1.6094379123:ℝ) ≤ Real.log 5 := le_of_lt Real.log_five_gt_d9
    have hlog100 : (4.5:ℝ) ≤ Real.log 100 := by
      have h : Real.log 100 = 2 * (Real.log 2 + Real.log 5) := by
        rw [show (100:ℝ) = 2^2 * 5^2 by norm_num, Real.log_mul (by positivity) (by positivity),
            Real.log_pow, Real.log_pow]; ring
      rw [h]; linarith
    have h100 : (100:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
    exact le_trans hlog100 (Real.log_le_log (by norm_num) h100)
  have hlogz : (1/2:ℝ) * L - 0.1 ≤ Real.log (Nat.sqrt y : ℝ) := by
    rw [hLdef]
    have hz10 : (10:ℕ) ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 10) (n := y)).mpr (by rw [pow_two]; omega)
    have hz10R : (10:ℝ) ≤ (Nat.sqrt y : ℝ) := by exact_mod_cast hz10
    have hlt : (y:ℝ) < ((Nat.sqrt y : ℝ) + 1)^2 := by
      have h := Nat.lt_succ_sqrt y
      have hR : (y:ℝ) < ((Nat.sqrt y + 1 : ℕ):ℝ) * ((Nat.sqrt y + 1:ℕ):ℝ) := by exact_mod_cast h
      have hc : ((Nat.sqrt y + 1 : ℕ):ℝ) = (Nat.sqrt y:ℝ) + 1 := by push_cast; ring
      rw [hc] at hR; nlinarith [hR]
    have hkey : (100:ℝ) * (y:ℝ) < (11 * (Nat.sqrt y : ℝ))^2 := by
      have h2 : (100:ℝ) * (y:ℝ) < 100 * ((Nat.sqrt y : ℝ) + 1)^2 := by nlinarith
      have h3 : (100:ℝ) * ((Nat.sqrt y : ℝ) + 1)^2 ≤ (11 * (Nat.sqrt y : ℝ))^2 := by
        nlinarith [hz10R, sq_nonneg ((Nat.sqrt y:ℝ))]
      linarith
    have hsqrt : Real.sqrt (y:ℝ) < (11/10) * (Nat.sqrt y : ℝ) := by
      have hs : Real.sqrt ((100:ℝ) * y) < Real.sqrt ((11 * (Nat.sqrt y:ℝ))^2) :=
        Real.sqrt_lt_sqrt (by positivity) hkey
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 100), Real.sqrt_sq (by positivity)] at hs
      have h100 : Real.sqrt (100:ℝ) = 10 := by
        rw [show (100:ℝ) = 10^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h100] at hs; linarith
    have hlog : Real.log ((10/11) * Real.sqrt (y:ℝ)) ≤ Real.log (Nat.sqrt y : ℝ) := by
      apply Real.log_le_log (by positivity)
      linarith
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (le_of_lt hypos)] at hlog
    have hlog1011 : Real.log (10/11) ≥ -(0.1:ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/10 by norm_num)
      have hh : Real.log (11/10) ≤ (1:ℝ)/10 := by linarith
      have he : Real.log (10/11) = -Real.log (11/10) := by
        rw [← Real.log_inv]; norm_num
      rw [he]; linarith
    linarith
  have hS' : (0.5) * L + 0.9 ≤ S := by linarith
  have hg := Commons.NumberTheory.Mertens.eulerMascheroni_exp_neg_lower
  have hM' : (0.56) * Real.exp (-(3/2) / L) / L ≤ M := by
    have h1 : (0.56) * Real.exp (-(3/2) / L) / L
        ≤ Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(3/2) / L) / L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hLpos)
      apply mul_le_mul_of_nonneg_right hg (le_of_lt (Real.exp_pos _))
    linarith
  have hSM : ((0.5) * L + 0.9) * ((0.56) * Real.exp (-(3/2) / L) / L) ≤ S * M := by
    apply mul_le_mul hS' hM'
    · positivity
    · linarith
  have hkey2 : (0.5:ℝ) ≤ (0.5 + 0.9 / L) * Real.exp (-(3/2) / L) := by
    have hlogb : (3/2)/L ≤ Real.log (1 + 1.8 / L) := by
      have hx : (0:ℝ) ≤ 1.8 / L := by positivity
      have h := Real.le_log_one_add_of_nonneg hx
      have hd : 2 * (1.8 / L) / (1.8 / L + 2) = 3.6 / (1.8 + 2*L) := by
        field_simp; ring
      rw [hd] at h
      have hb : (3/2)/L ≤ 3.6 / (1.8 + 2*L) := by
        rw [div_le_iff₀ hLpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith only [hL]
      linarith
    have hexp : Real.exp ((3/2)/L) ≤ 1 + 1.8/L := by
      have h := Real.exp_le_exp.mpr hlogb
      rwa [Real.exp_log (by positivity)] at h
    have hexp_neg : Real.exp ((-(3/2))/L) = (Real.exp ((3/2)/L))⁻¹ := by
      rw [show (-(3/2))/L = -((3/2)/L) by ring, Real.exp_neg]
    have hgoal : (0.5 + 0.9/L) * Real.exp ((-(3/2))/L) = (0.5 + 0.9/L) * (Real.exp ((3/2)/L))⁻¹ := by
      rw [hexp_neg]
    rw [hgoal, inv_eq_one_div, mul_one_div, le_div_iff₀ (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left hexp (show (0:ℝ) ≤ 0.5 by norm_num)
    have heq : (0.5 + 0.9/L) = 0.5 * (1 + 1.8/L) := by field_simp; ring
    rw [heq]; linarith [h]
  -- normalize exp argument
  have hkey3 : ((0.5) * L + 0.9) * ((0.56) * Real.exp (-(3/2) / L) / L)
      = 0.56 * ((0.5 + 0.9/L) * Real.exp (-(3/2) / L)) := by
    field_simp
  have hkey4 : ((0.5 + 0.9 / L) * Real.exp (-(3/2) / L)) = ((0.5 + 0.9 / L) * Real.exp ((-(3/2)) / L)) := by
    rw [show (-(3/2))/L = -(3/2)/L by ring]
  rw [hkey3] at hSM
  rw [← hkey4] at hkey2
  have hfinal : (0.56:ℝ) * 0.5 ≤ 0.56 * ((0.5 + 0.9 / L) * Real.exp (-(3/2) / L)) :=
    mul_le_mul_of_nonneg_left hkey2 (by norm_num)
  linarith [hSM, hfinal]

/-- The primorial bound for `y ≥ 100`. -/
private lemma primorial_bound_big (y : ℕ) (hy : 100 ≤ y) :
    (7/25 : ℝ) ≤ LHS (primorial y) (Nat.sqrt y) := by
  rw [LHS_primorial_eq]
  have hz1 : 1 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 1) (n := y)).mpr (by rw [pow_two]; omega)
  have hS := sum_mu_sq_div_totient_ge_log_add_one (Nat.sqrt y) hz1
  have hM := Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_sharp y hy
  exact arith_bound y hy _ _ hS hM

/-! ## The main theorem -/

theorem selberg_VQ_ge_sharp (P y : ℕ) (hP : Squarefree P) (hy1 : 1 ≤ y)
    (hy : ∀ p ∈ P.primeFactors, p ≤ y) :
    (7/25 : ℝ) ≤ (∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0)
      * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hsub : P.primeFactors ⊆ Nat.primesLE y := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨hy p hp, Nat.prime_of_mem_primeFactors hp⟩
  have hred : LHS (primorial y) (Nat.sqrt y) ≤ LHS P (Nat.sqrt y) := LHS_primorial_le P y hP hsub
  have hprim : (7/25 : ℝ) ≤ LHS (primorial y) (Nat.sqrt y) := by
    by_cases hy100 : 100 ≤ y
    · exact primorial_bound_big y hy100
    · exact primorial_bound_small y hy1 (by omega)
  change (7/25 : ℝ) ≤ LHS P (Nat.sqrt y)
  exact le_trans hprim hred

end

end Commons.NumberTheory.Totient
