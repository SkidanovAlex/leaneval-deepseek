import Mathlib.Data.Nat.Cast.Order.Field
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Totient.sum_mu_sq_div_d_mul_totient_le_two

namespace Commons.NumberTheory.Totient

open scoped BigOperators
open Finset

/-- The weight `h(e) = μ(e)² · 2^(ω e) / φ(e)` (with `ω` the number of distinct prime
factors).  It is (coprime-)multiplicative, takes the value `2/(p-1)` at a prime `p` and
vanishes on prime powers `p^k`, `k ≥ 2`. -/
private noncomputable def hval (e : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius e : ℤ) : ℝ)^2 * (2:ℝ)^(ArithmeticFunction.cardDistinctFactors e)
    / (Nat.totient e : ℝ)

private lemma hval_one : hval 1 = 1 := by simp [hval]

private lemma hval_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    hval (a * b) = hval a * hval b := by
  have hmu : ArithmeticFunction.moebius (a*b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  have homega : ArithmeticFunction.cardDistinctFactors (a*b)
      = ArithmeticFunction.cardDistinctFactors a + ArithmeticFunction.cardDistinctFactors b :=
    ArithmeticFunction.cardDistinctFactors_mul hab
  have hphi : Nat.totient (a*b) = Nat.totient a * Nat.totient b := Nat.totient_mul hab
  unfold hval
  rw [hmu, homega, hphi]
  push_cast
  rw [pow_add]
  ring

private lemma hval_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) : hval (p^k) = 0 := by
  unfold hval
  have hmu : ArithmeticFunction.moebius (p^k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  rw [hmu]
  simp

private lemma hval_nonneg (e : ℕ) : 0 ≤ hval e := by
  unfold hval; positivity

private lemma hval_prime_val (p : ℕ) (hp : Nat.Prime p) : hval p = 2 / ((p:ℝ) - 1) := by
  unfold hval
  rw [ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.cardDistinctFactors_apply_prime hp,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  norm_num

/-- `σ 1 d = ∏_{p | d} (p + 1)` for squarefree `d`. -/
private lemma sigma_one_eq_prod (d : ℕ) (hsq : Squarefree d) :
    ArithmeticFunction.sigma 1 d = ∏ p ∈ d.primeFactors, (p + 1) := by
  have hd : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hd]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hfac : d.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hpp (Nat.mem_primeFactors.mp hp).2.1
  rw [hfac]
  simp

/-- `φ d = ∏_{p | d} (p - 1)` for squarefree `d`. -/
private lemma totient_eq_prod_pred (d : ℕ) (hsq : Squarefree d) :
    Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
  have hd : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  rw [totient_eq_prod_primeFactors d hd]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hfac : d.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hsq hpp (Nat.mem_primeFactors.mp hp).2.1
  rw [hfac]; simp

/-- For squarefree `d`, `σ(d)/φ(d) = ∑_{e | d} h(e)`; the right-hand side is the Euler
product `∏_{p | d} (1 + 2/(p-1))`. -/
private lemma F_eq_sum_hval (d : ℕ) (hsq : Squarefree d) :
    ((ArithmeticFunction.sigma 1 d : ℕ) : ℝ) / (Nat.totient d : ℝ) = ∑ e ∈ d.divisors, hval e := by
  have hd : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  have heuler : ∑ e ∈ d.divisors, hval e = ∏ p ∈ d.primeFactors, (1 + hval p) :=
    (Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors hval d hd hval_one
      hval_mul hval_prime_pow).symm
  rw [heuler, sigma_one_eq_prod d hsq, totient_eq_prod_pred d hsq, Nat.cast_prod, Nat.cast_prod]
  have h1 : (∏ p ∈ d.primeFactors, (1 + hval p))
      = ∏ p ∈ d.primeFactors, (((p:ℝ)+1)/((p:ℝ)-1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    rw [hval_prime_val p hpp]
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
    have hne : (p:ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h1, Finset.prod_div_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    push_cast
    ring
  · apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [Nat.cast_sub hp1]
    ring

/-- The weight `g(e) = h(e)/e = μ(e)² · 2^(ω e) / (e · φ(e))`, `= ∏_{p | e} 2/(p(p-1))`
for squarefree `e`. -/
private noncomputable def gval (e : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius e : ℤ) : ℝ)^2 * (2:ℝ)^(ArithmeticFunction.cardDistinctFactors e)
    / ((e:ℝ) * (Nat.totient e : ℝ))

private lemma gval_one : gval 1 = 1 := by simp [gval]

private lemma gval_nonneg (e : ℕ) : 0 ≤ gval e := by
  unfold gval; positivity

private lemma gval_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    gval (a * b) = gval a * gval b := by
  have hmu : ArithmeticFunction.moebius (a*b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  have homega : ArithmeticFunction.cardDistinctFactors (a*b)
      = ArithmeticFunction.cardDistinctFactors a + ArithmeticFunction.cardDistinctFactors b :=
    ArithmeticFunction.cardDistinctFactors_mul hab
  have hphi : Nat.totient (a*b) = Nat.totient a * Nat.totient b := Nat.totient_mul hab
  unfold gval
  rw [hmu, homega, hphi]
  push_cast
  rw [pow_add]
  ring

private lemma gval_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) : gval (p^k) = 0 := by
  unfold gval
  have hmu : ArithmeticFunction.moebius (p^k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  rw [hmu]
  simp

private lemma gval_eq_hval_div (e : ℕ) : gval e = hval e / (e:ℝ) := by
  unfold gval hval
  rw [div_div]; ring

private lemma gval_prime_val (p : ℕ) (hp : Nat.Prime p) :
    gval p = 2 / ((p:ℝ) * ((p:ℝ) - 1)) := by
  unfold gval
  rw [ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.cardDistinctFactors_apply_prime hp,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  norm_num

/-- Among the elements of `S ⊆ {1,…,z}` at most `z/e` are divisible by `e`: they are
distinct multiples of `e` not exceeding `z`. -/
private lemma card_filter_dvd_le (S : Finset ℕ) (e z : ℕ) (he : 1 ≤ e)
    (hle : ∀ d ∈ S, d ≤ z) (hpos : ∀ d ∈ S, 1 ≤ d) :
    (S.filter (fun d => e ∣ d)).card ≤ z / e := by
  classical
  calc (S.filter (fun d => e ∣ d)).card
      ≤ (Finset.Icc 1 (z / e)).card := by
        refine Finset.card_le_card_of_injOn (s := S.filter (fun d => e ∣ d))
          (t := Finset.Icc 1 (z / e)) (f := fun d => d / e) ?_ ?_
        · intro d hd
          simp only [Finset.mem_coe, Finset.mem_filter] at hd
          obtain ⟨hdS, hed⟩ := hd
          have hdle : e ≤ d := Nat.le_of_dvd (by have := hpos d hdS; omega) hed
          exact Finset.mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr hdle,
            Nat.div_le_div_right (hle d hdS)⟩
        · intro d1 hd1 d2 hd2 heq
          simp only [Finset.mem_coe, Finset.mem_filter] at hd1 hd2
          have heq' : d1 / e = d2 / e := heq
          rw [← Nat.mul_div_cancel' hd1.2, ← Nat.mul_div_cancel' hd2.2, heq']
    _ = z / e := by simp

/-! ### The Euler-product bound `∏_{p | P} (1 + 2/(p(p-1))) ≤ 4` -/

private noncomputable def fval (e : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius e : ℤ) : ℝ)^2 / ((e:ℝ) * (Nat.totient e : ℝ))

private lemma fval_one : fval 1 = 1 := by simp [fval]

private lemma fval_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    fval (a * b) = fval a * fval b := by
  have hmu : ArithmeticFunction.moebius (a*b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  have hphi : Nat.totient (a*b) = Nat.totient a * Nat.totient b := Nat.totient_mul hab
  unfold fval
  rw [hmu, hphi]
  push_cast
  ring

private lemma fval_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) : fval (p^k) = 0 := by
  unfold fval
  have hmu : ArithmeticFunction.moebius (p^k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  rw [hmu]
  simp

private lemma fval_nonneg (e : ℕ) : 0 ≤ fval e := by unfold fval; positivity

private lemma fval_prime_val (p : ℕ) (hp : Nat.Prime p) :
    fval p = 1 / ((p:ℝ) * ((p:ℝ) - 1)) := by
  unfold fval
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  norm_num

private lemma one_add_two_div_le_sq (y : ℝ) : 1 + 2/y ≤ (1 + 1/y)^2 := by
  have h : (0:ℝ) ≤ (1/y)^2 := sq_nonneg _
  have h2 : (2:ℝ)/y = 2*(1/y) := by rw [div_eq_mul_inv]; ring
  rw [h2]
  nlinarith [h]

/-- `∏_{p | P} (1 + 2/(p(p-1))) ≤ 4`.  This follows from `1 + 2x ≤ (1+x)²`, the Euler
product `∏_{p|P}(1 + 1/(p(p-1))) = ∑_{e|P} μ(e)²/(e φ(e))` and the bound
`∑_{e ≤ N} μ(e)²/(e φ(e)) ≤ 2`. -/
private lemma prod_bound (P : ℕ) :
    ∏ p ∈ P.primeFactors, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 4 := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  have heuler : ∑ e ∈ P.divisors, fval e = ∏ p ∈ P.primeFactors, (1 + fval p) :=
    (Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors fval P hP0 fval_one
      fval_mul fval_prime_pow).symm
  have hsum_le : ∑ e ∈ P.divisors, fval e ≤ 2 := by
    have hsub : P.divisors ⊆ Finset.Icc 1 P := by
      intro e he
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he,
        Nat.le_of_dvd (Nat.pos_of_ne_zero hP0) (Nat.dvd_of_mem_divisors he)⟩
    have hnn : ∀ e ∈ Finset.Icc 1 P, e ∉ P.divisors → 0 ≤ fval e :=
      fun e _ _ => fval_nonneg e
    have h1 : ∑ e ∈ P.divisors, fval e ≤ ∑ e ∈ Finset.Icc 1 P, fval e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have h2 : ∑ e ∈ Finset.Icc 1 P, fval e ≤ 2 := by
      simpa [fval] using Commons.NumberTheory.Totient.sum_mu_sq_div_d_mul_totient_le_two P
    linarith
  have hprod_eq : ∏ p ∈ P.primeFactors, (1 + fval p)
      = ∏ p ∈ P.primeFactors, (1 + 1 / ((p:ℝ) * ((p:ℝ) - 1))) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [fval_prime_val p (Nat.prime_of_mem_primeFactors hp)]
  have hfval_nn : 0 ≤ ∑ e ∈ P.divisors, fval e :=
    Finset.sum_nonneg (fun e _ => fval_nonneg e)
  calc ∏ p ∈ P.primeFactors, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∏ p ∈ P.primeFactors, (1 + 1 / ((p:ℝ) * ((p:ℝ) - 1)))^2 := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          have h1 : (0:ℝ) ≤ (p:ℝ) := by linarith [hp2]
          have h2 : (0:ℝ) ≤ (p:ℝ) - 1 := by linarith [hp2]
          have hx : 0 ≤ 2 / ((p:ℝ) * ((p:ℝ) - 1)) :=
            div_nonneg (by norm_num) (mul_nonneg h1 h2)
          linarith
        · intro p hp
          have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          exact one_add_two_div_le_sq ((p:ℝ) * ((p:ℝ) - 1))
    _ = (∏ p ∈ P.primeFactors, (1 + 1 / ((p:ℝ) * ((p:ℝ) - 1))))^2 := by
        rw [Finset.prod_pow]
    _ = (∑ e ∈ P.divisors, fval e)^2 := by rw [heuler, hprod_eq]
    _ ≤ 2^2 := by
        apply pow_le_pow_left₀ hfval_nn hsum_le
    _ = 4 := by norm_num

/-- **Main lemma.**  For squarefree `P`, the sum of `σ(d)/φ(d)` over the divisors
`d ≤ z` of `P` is at most `4z`. -/
theorem sum_sigma_div_totient_divisors_le_four_mul (P z : ℕ) (hP : Squarefree P) :
    ∑ d ∈ P.divisors.filter (fun d => d ≤ z),
        ((ArithmeticFunction.sigma 1 d : ℕ) : ℝ) / (Nat.totient d : ℝ) ≤ 4 * (z : ℝ) := by
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [Nat.divisors_zero]; simp only [Finset.filter_empty, Finset.sum_empty]; positivity
  set S : Finset ℕ := P.divisors.filter (fun d => d ≤ z) with hS
  have hSsub : S ⊆ P.divisors := by rw [hS]; exact Finset.filter_subset _ _
  have hSle : ∀ d ∈ S, d ≤ z := by
    intro d hd
    rw [hS] at hd
    exact (Finset.mem_filter.mp hd).2
  have hSpos : ∀ d ∈ S, 1 ≤ d := fun d hd => Nat.pos_of_mem_divisors (hSsub hd)
  have hstep1 : ∑ d ∈ S, ((ArithmeticFunction.sigma 1 d : ℕ) : ℝ) / (Nat.totient d : ℝ)
      = ∑ d ∈ S, ∑ e ∈ d.divisors, hval e := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ P := Nat.dvd_of_mem_divisors (hSsub hd)
    exact F_eq_sum_hval d (hP.squarefree_of_dvd hdvd)
  have hstep2 : ∑ d ∈ S, ∑ e ∈ d.divisors, hval e
      = ∑ d ∈ S, ∑ e ∈ S, (if e ∣ d then hval e else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors (hSsub hd)).ne'
    have hfil : S.filter (fun e => e ∣ d) = d.divisors := by
      ext e
      rw [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨heS, hed⟩
        exact ⟨hed, hd0⟩
      · rintro ⟨hed, _⟩
        refine ⟨?_, hed⟩
        rw [hS, Finset.mem_filter]
        exact ⟨Nat.mem_divisors.mpr ⟨hed.trans (Nat.dvd_of_mem_divisors (hSsub hd)), hP0⟩,
          le_trans (Nat.le_of_dvd (Nat.pos_of_mem_divisors (hSsub hd)) hed) (hSle d hd)⟩
    calc ∑ e ∈ d.divisors, hval e = ∑ e ∈ S.filter (fun e => e ∣ d), hval e := by rw [hfil]
      _ = ∑ e ∈ S, (if e ∣ d then hval e else 0) := by rw [Finset.sum_filter]
  have hstep3 : (∑ d ∈ S, ∑ e ∈ S, (if e ∣ d then hval e else 0))
      = ∑ e ∈ S, ∑ d ∈ S, (if e ∣ d then hval e else 0) := Finset.sum_comm
  have hstep4 : ∑ e ∈ S, ∑ d ∈ S, (if e ∣ d then hval e else 0)
      = ∑ e ∈ S, (hval e * ((S.filter (fun d => e ∣ d)).card : ℝ)) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hbound : ∑ e ∈ S, (hval e * ((S.filter (fun d => e ∣ d)).card : ℝ))
      ≤ (z:ℝ) * ∑ e ∈ S, gval e := by
    have h1 : ∀ e ∈ S, hval e * ((S.filter (fun d => e ∣ d)).card : ℝ)
        ≤ hval e * ((z:ℝ)/(e:ℝ)) := by
      intro e he
      have hhe : 0 ≤ hval e := hval_nonneg e
      have hcard : ((S.filter (fun d => e ∣ d)).card : ℝ) ≤ (z:ℝ)/(e:ℝ) := by
        have he1 : 1 ≤ e := hSpos e he
        have hc := card_filter_dvd_le S e z he1 hSle hSpos
        calc ((S.filter (fun d => e ∣ d)).card : ℝ) ≤ ((z/e : ℕ):ℝ) := by exact_mod_cast hc
          _ ≤ (z:ℝ)/(e:ℝ) := Nat.cast_div_le
      exact mul_le_mul_of_nonneg_left hcard hhe
    calc ∑ e ∈ S, (hval e * ((S.filter (fun d => e ∣ d)).card : ℝ))
        ≤ ∑ e ∈ S, hval e * ((z:ℝ)/(e:ℝ)) := Finset.sum_le_sum h1
      _ = ∑ e ∈ S, (z:ℝ) * gval e := by
          apply Finset.sum_congr rfl
          intro e he
          have he0 : (e:ℝ) ≠ 0 := by
            have : 0 < e := Nat.pos_of_mem_divisors (hSsub he); exact_mod_cast this.ne'
          rw [gval_eq_hval_div]
          field_simp
      _ = (z:ℝ) * ∑ e ∈ S, gval e := by rw [Finset.mul_sum]
  have hsum_bound : ∑ e ∈ S, gval e ≤ 4 := by
    have h1 : ∑ e ∈ S, gval e ≤ ∑ e ∈ P.divisors, gval e :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun e _ _ => gval_nonneg e)
    have h2 : ∑ e ∈ P.divisors, gval e = ∏ p ∈ P.primeFactors, (1 + gval p) :=
      (Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors gval P hP0 gval_one
        gval_mul gval_prime_pow).symm
    have h3 : ∏ p ∈ P.primeFactors, (1 + gval p)
        = ∏ p ∈ P.primeFactors, (1 + 2 / ((p:ℝ) * ((p:ℝ) - 1))) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [gval_prime_val p (Nat.prime_of_mem_primeFactors hp)]
    have h4 := prod_bound P
    linarith
  calc ∑ d ∈ S, ((ArithmeticFunction.sigma 1 d : ℕ) : ℝ) / (Nat.totient d : ℝ)
      = ∑ d ∈ S, ∑ e ∈ d.divisors, hval e := hstep1
    _ = ∑ d ∈ S, ∑ e ∈ S, (if e ∣ d then hval e else 0) := hstep2
    _ = ∑ e ∈ S, ∑ d ∈ S, (if e ∣ d then hval e else 0) := hstep3
    _ = ∑ e ∈ S, (hval e * ((S.filter (fun d => e ∣ d)).card : ℝ)) := hstep4
    _ ≤ (z:ℝ) * ∑ e ∈ S, gval e := hbound
    _ ≤ (z:ℝ) * 4 := by
          apply mul_le_mul_of_nonneg_left hsum_bound (Nat.cast_nonneg z)
    _ = 4 * (z:ℝ) := by ring

end Commons.NumberTheory.Totient