import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The number of divisors of a squarefree number is `2 ^ ω`. -/
lemma card_divisors_sqfree (u : ℕ) (hu : Squarefree u) :
    u.divisors.card = 2 ^ u.primeFactors.card := by
  rw [Nat.card_divisors hu.ne_zero]
  have hfac : ∀ p ∈ u.primeFactors, u.factorization p = 1 := by
    intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hge : 1 ≤ u.factorization p :=
      (hp'.pow_dvd_iff_le_factorization hu.ne_zero).mp
        (by simpa [pow_one] using (Nat.dvd_of_mem_primeFactors hp))
    have hle : ¬ 2 ≤ u.factorization p := fun h =>
      (Nat.squarefree_iff_prime_squarefree.mp hu) p hp'
        (by simpa [pow_two] using (hp'.pow_dvd_iff_le_factorization hu.ne_zero).mpr h)
    omega
  calc ∏ p ∈ u.primeFactors, (u.factorization p + 1)
      = ∏ p ∈ u.primeFactors, (2 : ℕ) := by
        apply Finset.prod_congr rfl; intro p hp; rw [hfac p hp]
    _ = 2 ^ u.primeFactors.card := by rw [Finset.prod_const]

/-- `∑_{d ∣ n} μ(d) = [n = 1]`, as a real number. -/
lemma sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 1 with h1 | h1
  · subst h1; simp
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0; simp
  have key := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) n h0
      (by rw [ArithmeticFunction.moebius_apply_one]; norm_num)
      (fun a b hab => by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          (Nat.coprime_iff_gcd_eq_one.mp hab)]
        push_cast; ring)
      (fun p k hp hk => by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show k ≠ 1 by omega])
  rw [← key, if_neg h1]
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < n)
  exact Finset.prod_eq_zero hp (by
    rw [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
    norm_num)

/-- The two-sided bound `log(z/e) ≤ H_{⌊z/e⌋} ≤ log(z/e) + 1` for `1 ≤ e ≤ z`. -/
lemma harmonic_log_bounds (z e : ℕ) (he1 : 1 ≤ e) (hez : e ≤ z) :
    Real.log ((z:ℝ)/(e:ℝ)) ≤ (harmonic (z/e) : ℝ) ∧
      (harmonic (z/e) : ℝ) ≤ Real.log ((z:ℝ)/(e:ℝ)) + 1 := by
  have he0 : 0 < e := by omega
  have hz0 : 0 < z := lt_of_lt_of_le he0 hez
  have he0r : (0:ℝ) < (e:ℝ) := by exact_mod_cast he0
  have hM1 : 1 ≤ z/e := (Nat.one_le_div_iff he0).mpr hez
  have hM0r : (0:ℝ) < ((z/e : ℕ) : ℝ) := by exact_mod_cast hM1
  have hle : ((z/e : ℕ) : ℝ) ≤ (z:ℝ)/(e:ℝ) := Nat.cast_div_le
  have hmod : z < (z/e + 1) * e := by
    have h1 : z = e * (z/e) + z % e := (Nat.div_add_mod z e).symm
    have h2 : z % e < e := Nat.mod_lt z he0
    calc z = e*(z/e) + z%e := h1
      _ < e*(z/e) + e := Nat.add_lt_add_left h2 _
      _ = (z/e + 1)*e := by ring
  have hlt : (z:ℝ)/(e:ℝ) < ((z/e : ℕ) : ℝ) + 1 := by
    have hmodr : (z:ℝ) < (((z/e + 1) * e : ℕ) : ℝ) := by exact_mod_cast hmod
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hmodr
    rw [div_lt_iff₀ he0r]
    linarith
  constructor
  · calc Real.log ((z:ℝ)/(e:ℝ)) ≤ Real.log (((z/e + 1 : ℕ)) : ℝ) :=
          Real.log_le_log (by positivity) (by push_cast; linarith)
      _ ≤ (harmonic (z/e) : ℝ) := log_add_one_le_harmonic (z/e)
  · have h1 : (harmonic (z/e) : ℝ) ≤ 1 + Real.log ((z/e : ℕ) : ℝ) :=
      harmonic_le_one_add_log (z/e)
    have h2 : Real.log ((z/e : ℕ) : ℝ) ≤ Real.log ((z:ℝ)/(e:ℝ)) :=
      Real.log_le_log hM0r hle
    linarith

/-- `∑_{v ∣ u} log v ≤ 2^ω(u) · log u` for squarefree `u`. -/
lemma sum_log_divisors_le (u : ℕ) (hu : Squarefree u) :
    (∑ v ∈ u.divisors, Real.log v) ≤ (2:ℝ)^(u.primeFactors.card) * Real.log u := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu0
  have hu0r : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu1
  calc (∑ v ∈ u.divisors, Real.log v) ≤ ∑ v ∈ u.divisors, Real.log u := by
        apply Finset.sum_le_sum
        intro v hv
        have hvd : v ∣ u := (Nat.mem_divisors.mp hv).1
        have hvu : v ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu0) hvd
        have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hvd (Nat.pos_of_ne_zero hu0)))
        have hvr : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv1
        exact Real.log_le_log hvr (by exact_mod_cast hvu)
    _ = (u.divisors.card : ℝ) * Real.log u := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2:ℝ)^(u.primeFactors.card) * Real.log u := by
        rw [card_divisors_sqfree u hu]
        push_cast; ring

end

end Work.LinnikAreas.Density4
