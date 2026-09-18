import Mathlib
import Submission.Commons.NumberTheory.Totient.log_le_sum_mu_sq_div_totient
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv
import Submission.Commons.NumberTheory.Totient.sum_divisors_inv_totient_squarefree_eq
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_invLog

open scoped BigOperators
open Finset

noncomputable section

namespace Commons.NumberTheory.Totient

/-- The primorial `∏_{p ≤ y} p` over primes `p ≤ y`. -/
def primorial (y : ℕ) : ℕ := ∏ p ∈ Nat.primesLE y, p

lemma primorial_ne_zero (y : ℕ) : primorial y ≠ 0 := by
  rw [primorial]
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero)

lemma primorial_squarefree (y : ℕ) : Squarefree (primorial y) := by
  rw [primorial, Nat.squarefree_iff_factorization_le_one (Finset.prod_ne_zero_iff.mpr
    (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero))]
  intro q
  rw [Nat.factorization_prod_apply (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero)]
  have h1 : ∀ p ∈ Nat.primesLE y, p.factorization q = if p = q then 1 else 0 := by
    intro p hp
    rw [(Nat.mem_primesLE.mp hp).2.factorization]
    simp [Finsupp.single_apply]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_ite_eq' (Nat.primesLE y) q (fun _ => 1)]
  split <;> omega

lemma primeFactors_primorial (y : ℕ) : (primorial y).primeFactors = Nat.primesLE y := by
  rw [primorial]
  exact Nat.primeFactors_prod (fun p hp => (Nat.mem_primesLE.mp hp).2)

/-- `Vp N = ∏_{p | N} (1 - 1/p)`. -/
def Vp (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)

/-- The truncated totient-divisor sum `∑_{d | N, d ≤ z} 1/φ(d)` (as a real). -/
def Tle (N z : ℕ) : ℝ := ∑ d ∈ N.divisors, if d ≤ z then (Nat.totient d : ℝ)⁻¹ else 0

/-- The quantity `(∑_{d|N,d≤z} 1/φ d) · ∏_{p|N}(1-1/p)`. -/
def LHS (N z : ℕ) : ℝ := Tle N z * Vp N

/-- The divisors of `Q * p` for `p` prime, `p ∤ Q`, `Q ≠ 0`. -/
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

/-- The squarefree numbers `≤ z` are exactly the divisors of `primorial y` that are `≤ z`,
when `z ≤ y`. -/
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

/-- For `z ≤ y`, `Tle (primorial y) z` is the squarefree-restricted sum of `1/φ`. -/
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


/-- `Vp (primorial y') ≤ Vp (primorial y)` when `y ≤ y'`. -/
private lemma Vp_primorial_mono {y y' : ℕ} (h : y ≤ y') :
    Vp (primorial y') ≤ Vp (primorial y) := by
  rw [Vp, Vp, primeFactors_primorial, primeFactors_primorial]
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨le_trans (Nat.mem_primesLE.mp hp).1 h, (Nat.mem_primesLE.mp hp).2⟩
  · intro p hp
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)
  · intro p hp _
    have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
    have : (0:ℝ) ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr hp0
    linarith

/-- Lower bound for `Tle` by a sum over an explicit set of divisors. -/
private lemma Tle_ge_sum (y z : ℕ) (s : Finset ℕ) (hs : s ⊆ (primorial y).divisors)
    (hsz : ∀ d ∈ s, d ≤ z) :
    ∑ d ∈ s, (Nat.totient d : ℝ)⁻¹ ≤ Tle (primorial y) z := by
  unfold Tle
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [Finset.mem_filter]
    exact ⟨hs hd, hsz d hd⟩
  · intro d _ _
    exact inv_nonneg.mpr (by positivity)


/-- `Vp N ≥ 0`. -/
private lemma Vp_nonneg (N : ℕ) : 0 ≤ Vp N := by
  unfold Vp
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)

/-- The primorial bound for `y < 100`, by finite verification. -/
private lemma primorial_bound_small (y : ℕ) (hy1 : 1 ≤ y) (hy : y < 100) :
    (1/5 : ℝ) ≤ LHS (primorial y) (Nat.sqrt y) := by
  have hz1le : 1 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 1) (n := y)).mpr (by omega)
  rw [LHS]
  by_cases hz1eq : Nat.sqrt y = 1
  · have hy3 : y ≤ 3 := by
      have h2 : Nat.sqrt y < 2 := by omega
      have := (Nat.sqrt_lt' (m := y) (n := 2)).mp h2
      omega
    have hV : Vp (primorial 3) ≤ Vp (primorial y) := Vp_primorial_mono hy3
    have hV3 : (1/3 : ℝ) ≤ Vp (primorial 3) := by
      rw [Vp, primeFactors_primorial, show Nat.primesLE 3 = {2, 3} by decide]; norm_num
    have h1mem : (1:ℕ) ∈ (primorial y).divisors := by
      rw [Nat.mem_divisors]; exact ⟨one_dvd _, primorial_ne_zero y⟩
    have hT : (1:ℝ) ≤ Tle (primorial y) 1 := by
      have h := Tle_ge_sum y 1 {1}
        (by intro d hd; rw [Finset.mem_singleton] at hd; subst hd; exact h1mem)
        (by intro d hd; rw [Finset.mem_singleton] at hd; subst hd; exact le_rfl)
      simpa using h
    rw [hz1eq]
    have hkey := mul_le_mul hT hV (by linarith) (by linarith)
    simp only [one_mul] at hkey
    linarith
  · have hz2 : 2 ≤ Nat.sqrt y := by omega
    have hy2 : 2 ≤ y := by
      have := (Nat.le_sqrt' (m := 2) (n := y)).mp hz2; omega
    have hV : Vp (primorial 99) ≤ Vp (primorial y) := Vp_primorial_mono (by omega)
    have hV99 : (0.11 : ℝ) ≤ Vp (primorial 99) := by
      rw [Vp, primeFactors_primorial,
        show Nat.primesLE 99 = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97}
          by decide]
      norm_num
    have h1mem : (1:ℕ) ∈ (primorial y).divisors := by
      rw [Nat.mem_divisors]; exact ⟨one_dvd _, primorial_ne_zero y⟩
    have h2mem : (2:ℕ) ∈ (primorial y).divisors := by
      rw [Nat.mem_divisors]
      refine ⟨?_, primorial_ne_zero y⟩
      rw [primorial]
      exact Finset.dvd_prod_of_mem (fun p => p) (Nat.mem_primesLE.mpr ⟨hy2, by norm_num⟩)
    have hT2 : (2:ℝ) ≤ Tle (primorial y) (Nat.sqrt y) := by
      have h := Tle_ge_sum y (Nat.sqrt y) ({1,2} : Finset ℕ)
        (by
          intro d hd
          rw [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact h1mem
          · exact h2mem)
        (by
          intro d hd
          rw [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact hz1le
          · exact hz2)
      have hsum : (∑ d ∈ ({1,2}:Finset ℕ), (Nat.totient d : ℝ)⁻¹) = 2 := by
        rw [show ({1,2}:Finset ℕ) = (insert 1 {2}) from rfl,
          Finset.sum_insert (by decide), Finset.sum_singleton, Nat.totient_one,
          show Nat.totient 2 = 1 by decide]
        norm_num
      linarith [h, hsum]
    have hkey := mul_le_mul hT2 hV (by linarith) (by linarith)
    linarith


/-- Ratio bound: `log (√y) ≥ (4/9) log y` for `y ≥ 100`. -/
private lemma log_sqrt_ge (y : ℕ) (hy : 100 ≤ y) :
    (4/9 : ℝ) * Real.log (y:ℝ) ≤ Real.log (Nat.sqrt y : ℝ) := by
  have hz10 : 10 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 10) (n := y)).mpr (by omega)
  have hzpos : (0:ℝ) < (Nat.sqrt y : ℝ) := by exact_mod_cast (by omega : 0 < Nat.sqrt y)
  have hltR : (y:ℝ) < ((Nat.sqrt y : ℝ) + 1)^2 := by
    have h : y < (Nat.sqrt y + 1) * (Nat.sqrt y + 1) := Nat.lt_succ_sqrt y
    have hR : (y:ℝ) < ((Nat.sqrt y + 1 : ℕ) : ℝ) * ((Nat.sqrt y + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    have hc : ((Nat.sqrt y + 1 : ℕ) : ℝ) = (Nat.sqrt y : ℝ) + 1 := by push_cast; ring
    rw [hc] at hR
    nlinarith [hR]
  have h1 : ((Nat.sqrt y : ℝ) + 1) ≤ 1.1 * (Nat.sqrt y : ℝ) := by
    have hzR : (10:ℝ) ≤ (Nat.sqrt y : ℝ) := by exact_mod_cast hz10
    linarith
  have hle1 : (y:ℝ) ≤ 1.21 * (Nat.sqrt y : ℝ)^2 := by
    nlinarith [hltR, h1, hzpos]
  have hypos : (0:ℝ) < (y:ℝ) := by positivity
  have hlog := Real.log_le_log hypos hle1
  have hlog2 : Real.log (1.21 * (Nat.sqrt y : ℝ)^2)
      = Real.log 1.21 + 2 * Real.log (Nat.sqrt y : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
  have hlny : (9 * Real.log 1.21 : ℝ) ≤ Real.log (y:ℝ) := by
    have h100 : (100:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
    calc (9 * Real.log 1.21 : ℝ) = Real.log (1.21^9) := by rw [Real.log_pow]; ring
      _ ≤ Real.log 100 := Real.log_le_log (by positivity) (by norm_num)
      _ ≤ Real.log (y:ℝ) := Real.log_le_log (by norm_num) h100
  rw [hlog2] at hlog
  linarith

/-- The primorial bound for `y ≥ 100`. -/
private lemma primorial_bound_big (y : ℕ) (hy : 100 ≤ y) :
    (1/5 : ℝ) ≤ LHS (primorial y) (Nat.sqrt y) := by
  have hzy : Nat.sqrt y ≤ y := Nat.sqrt_le_self y
  have hz1 : 1 ≤ Nat.sqrt y := (Nat.le_sqrt' (m := 1) (n := y)).mpr (by omega)
  rw [LHS]
  have hT : Real.log (Nat.sqrt y : ℝ) ≤ Tle (primorial y) (Nat.sqrt y) := by
    rw [Tle_primorial_eq y (Nat.sqrt y) hzy]
    exact Commons.NumberTheory.Totient.log_le_sum_mu_sq_div_totient (Nat.sqrt y) hz1
  have hVp : Vp (primorial y) = ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
    rw [Vp, primeFactors_primorial]
  rw [hVp]
  have hProd : (9/20 : ℝ) / Real.log (y:ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) :=
    Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_invLog y hy
  have hratio : (4/9 : ℝ) * Real.log (y:ℝ) ≤ Real.log (Nat.sqrt y : ℝ) := log_sqrt_ge y hy
  have hlny : (0:ℝ) < Real.log (y:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hT' : (4/9) * Real.log (y:ℝ) ≤ Tle (primorial y) (Nat.sqrt y) := le_trans hratio hT
  have hA : (0:ℝ) ≤ (9/20)/Real.log (y:ℝ) := div_nonneg (by norm_num) hlny.le
  have hB : (0:ℝ) ≤ Tle (primorial y) (Nat.sqrt y) := le_trans (mul_nonneg (by norm_num) hlny.le) hT'
  have hkey := mul_le_mul hT' hProd hA hB
  have heq : ((4/9:ℝ) * Real.log (y:ℝ)) * ((9/20)/Real.log (y:ℝ)) = 1/5 := by
    field_simp; ring
  linarith [hkey, heq]

/-- The Selberg `V(Q)` lower bound. -/
theorem selberg_VQ_ge (P y : ℕ) (hP : Squarefree P) (hy1 : 1 ≤ y)
    (hy : ∀ p ∈ P.primeFactors, p ≤ y) :
    (1/5 : ℝ) ≤ (∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0)
      * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hsub : P.primeFactors ⊆ Nat.primesLE y :=
    fun p hp => Nat.mem_primesLE.mpr ⟨hy p hp, Nat.prime_of_mem_primeFactors hp⟩
  have hred : LHS (primorial y) (Nat.sqrt y) ≤ LHS P (Nat.sqrt y) := LHS_primorial_le P y hP hsub
  have hbound : (1/5 : ℝ) ≤ LHS (primorial y) (Nat.sqrt y) := by
    by_cases hy100 : 100 ≤ y
    · exact primorial_bound_big y hy100
    · exact primorial_bound_small y hy1 (by omega)
  change (1/5 : ℝ) ≤ LHS P (Nat.sqrt y)
  exact le_trans hbound hred

end Commons.NumberTheory.Totient
