import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_mul_of_coprime
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

noncomputable section

/-- `d₂(d) = ∏_{p ∣ d} p ^ ⌊v_p(d)/2⌋`, the square root of the largest square divisor
of `d` (equal to `Nat.floorRoot 2 d`). -/
private def d2 (d : ℕ) : ℕ := (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))

private lemma d2_sq_dvd (d : ℕ) : (d2 d) ^ 2 ∣ d := by
  rw [d2]; exact sqKernel_sq_dvd d

private lemma d2_pos (d : ℕ) (hd : 0 < d) : 0 < d2 d := by
  rcases Nat.eq_zero_or_pos (d2 d) with h | h
  · exfalso
    have h2 := d2_sq_dvd d
    rw [h] at h2
    simp at h2
    omega
  · exact h

/-- `ρ(c²; d) ≤ 2 ^ ω(d) · d₂(d)`. -/
private lemma rho_csq_le (c d : ℕ) (hd : 0 < d) :
    Submission.rho (c ^ 2) d ≤ 2 ^ (Nat.primeFactors d).card * d2 d := by
  have h := sq_sum_sq_root_count_le_two_pow_omega (d := d) (b := c ^ 2) hd
  have hbound : Submission.rho (c ^ 2) d ≤ 2 ^ (Nat.primeFactors d).card * Nat.gcd (c ^ 2) (d2 d) := by
    simpa [Submission.rho, d2] using h
  calc Submission.rho (c ^ 2) d
      ≤ 2 ^ (Nat.primeFactors d).card * Nat.gcd (c ^ 2) (d2 d) := hbound
    _ ≤ 2 ^ (Nat.primeFactors d).card * d2 d :=
        Nat.mul_le_mul_left _ (Nat.gcd_le_right (c ^ 2) (d2_pos d hd))

private lemma tau_card_ge_one {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
  have h : 1 ≤ n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩
  exact_mod_cast h

private lemma two_pow_omega_le_tau {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ (Nat.primeFactors n).card ≤ (n.divisors.card : ℝ) := by
  have h := two_pow_card_primeFactors_le_card_divisors (d := n) (by omega)
  exact_mod_cast h

/-- `τ(n²) ≤ τ(n)²`. -/
private lemma tau_sq_le (n : ℕ) : (n ^ 2).divisors.card ≤ (n.divisors.card) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; norm_num
  · have hn0 : n ≠ 0 := hn.ne'
    have hn20 : n ^ 2 ≠ 0 := by positivity
    calc (n ^ 2).divisors.card
        = (Nat.primeFactors n).prod (fun p => (n ^ 2).factorization p + 1) := by
          rw [Nat.card_divisors hn20, Nat.primeFactors_pow n (by norm_num : (2 : ℕ) ≠ 0)]
      _ = (Nat.primeFactors n).prod (fun p => 2 * n.factorization p + 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.factorization_pow]
          simp [Finsupp.smul_apply, smul_eq_mul]
      _ ≤ (Nat.primeFactors n).prod (fun p => (n.factorization p + 1) ^ 2) := by
          apply Finset.prod_le_prod₀
          · intro p hp; positivity
          · intro p hp
            have h2 : 2 * n.factorization p + 1 ≤ (n.factorization p + 1) ^ 2 := by
              nlinarith [Nat.zero_le (n.factorization p)]
            exact h2
      _ = ((Nat.primeFactors n).prod (fun p => n.factorization p + 1)) ^ 2 := by rw [Finset.prod_pow]
      _ = (n.divisors.card) ^ 2 := by rw [Nat.card_divisors hn0]

/-- `A(n) = τ(n)^K 2^{ω(n)} / n`. -/
private def Aterm (K : ℝ) (n : ℕ) : ℝ :=
  ((n.divisors.card : ℝ)) ^ K * (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ)

/-- `B(n) = τ(n²)^K 2^{ω(n)} / n`. -/
private def Bterm (K : ℝ) (n : ℕ) : ℝ :=
  (((n ^ 2).divisors.card : ℝ)) ^ K * (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ)

private lemma Aterm_nonneg (K : ℝ) (n : ℕ) : 0 ≤ Aterm K n := by
  rw [Aterm]
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) K) (by positivity))
    (Nat.cast_nonneg n)

private lemma Bterm_nonneg (K : ℝ) (n : ℕ) : 0 ≤ Bterm K n := by
  rw [Bterm]
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) K) (by positivity))
    (Nat.cast_nonneg n)

/-- For `n ≥ 1` and `K ≤ m`, `A(n) ≤ τ(n)^{m+1} / n`. -/
private lemma Aterm_le (K : ℝ) {m : ℕ} (hm : K ≤ (m : ℝ)) (n : ℕ) (hn : 1 ≤ n) :
    Aterm K n ≤ ((n.divisors.card : ℝ)) ^ (m + 1) / (n : ℝ) := by
  have hτ1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) := tau_card_ge_one hn
  have h2ω : (2 : ℝ) ^ (Nat.primeFactors n).card ≤ (n.divisors.card : ℝ) :=
    two_pow_omega_le_tau hn
  have hpow : ((n.divisors.card : ℝ)) ^ K ≤ ((n.divisors.card : ℝ)) ^ m := by
    have h := Real.rpow_le_rpow_of_exponent_le hτ1 hm
    rwa [Real.rpow_natCast] at h
  have hnum : ((n.divisors.card : ℝ)) ^ K * (2 : ℝ) ^ (Nat.primeFactors n).card
      ≤ ((n.divisors.card : ℝ)) ^ (m + 1) := by
    calc ((n.divisors.card : ℝ)) ^ K * (2 : ℝ) ^ (Nat.primeFactors n).card
        ≤ ((n.divisors.card : ℝ)) ^ m * ((n.divisors.card : ℝ)) :=
          mul_le_mul hpow h2ω (by positivity) (by positivity)
      _ = ((n.divisors.card : ℝ)) ^ (m + 1) := by rw [pow_succ]
  rw [Aterm]
  exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg n)

/-- For `n ≥ 1`, `0 ≤ K ≤ m`, `B(n) ≤ τ(n)^{2m+1} / n`. -/
private lemma Bterm_le (K : ℝ) (hK : 0 ≤ K) {m : ℕ} (hm : K ≤ (m : ℝ)) (n : ℕ) (hn : 1 ≤ n) :
    Bterm K n ≤ ((n.divisors.card : ℝ)) ^ (2 * m + 1) / (n : ℝ) := by
  have hτ1 : (1 : ℝ) ≤ (n.divisors.card : ℝ) := tau_card_ge_one hn
  have h2ω : (2 : ℝ) ^ (Nat.primeFactors n).card ≤ (n.divisors.card : ℝ) :=
    two_pow_omega_le_tau hn
  have hτ2 : (((n ^ 2).divisors.card : ℝ)) ≤ ((n.divisors.card : ℝ)) ^ (2 : ℝ) := by
    calc (((n ^ 2).divisors.card : ℝ)) ≤ (((n.divisors.card) ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast tau_sq_le n
      _ = ((n.divisors.card : ℝ)) ^ (2 : ℝ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Nat.cast_pow]
  have hstep1 : (((n ^ 2).divisors.card : ℝ)) ^ K
      ≤ (((n.divisors.card : ℝ)) ^ (2 : ℝ)) ^ K :=
    Real.rpow_le_rpow (by positivity) hτ2 hK
  have hstep2 : (((n.divisors.card : ℝ)) ^ (2 : ℝ)) ^ K
      = ((n.divisors.card : ℝ)) ^ ((2 : ℝ) * K) :=
    (Real.rpow_mul (by positivity) (2 : ℝ) K).symm
  have hstep3 : ((n.divisors.card : ℝ)) ^ ((2 : ℝ) * K)
      ≤ ((n.divisors.card : ℝ)) ^ ((2 : ℝ) * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hτ1 (mul_le_mul_of_nonneg_left hm (by norm_num))
  have hstep4 : ((n.divisors.card : ℝ)) ^ ((2 : ℝ) * (m : ℝ))
      = ((n.divisors.card : ℝ)) ^ (2 * m) := by
    rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hA : (((n ^ 2).divisors.card : ℝ)) ^ K ≤ ((n.divisors.card : ℝ)) ^ (2 * m) :=
    le_trans (le_trans hstep1 (le_of_eq hstep2)) (le_trans hstep3 (le_of_eq hstep4))
  have hnum : (((n ^ 2).divisors.card : ℝ)) ^ K * (2 : ℝ) ^ (Nat.primeFactors n).card
      ≤ ((n.divisors.card : ℝ)) ^ (2 * m + 1) := by
    calc (((n ^ 2).divisors.card : ℝ)) ^ K * (2 : ℝ) ^ (Nat.primeFactors n).card
        ≤ ((n.divisors.card : ℝ)) ^ (2 * m) * ((n.divisors.card : ℝ)) :=
          mul_le_mul hA h2ω (by positivity) (by positivity)
      _ = ((n.divisors.card : ℝ)) ^ (2 * m + 1) := by rw [pow_succ]
  rw [Bterm]
  exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg n)

/-- The pointwise reduction of the summand to the separated form `A(a) · B(b)`, where
`d = a · d₂(d)²` and `b = d₂(d)`. -/
private lemma summand_le (K : ℝ) (hK : 0 ≤ K) (c d : ℕ) (hd : 1 ≤ d) :
    ((d.divisors.card : ℝ)) ^ K * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))
      ≤ Aterm K (d / (d2 d) ^ 2) * Bterm K (d2 d) := by
  have hd0 : 0 < d := hd
  set b : ℕ := d2 d with hb
  set a : ℕ := d / b ^ 2 with ha
  have hb2dvd : b ^ 2 ∣ d := by rw [hb]; exact d2_sq_dvd d
  have hd_eq : a * b ^ 2 = d := by rw [ha]; exact Nat.div_mul_cancel hb2dvd
  have hb2pos : 0 < b ^ 2 := Nat.pos_of_dvd_of_pos hb2dvd hd0
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb2pos; simp at hb2pos
    · exact h
  have hbne : b ≠ 0 := hbpos.ne'
  have hb2le : b ^ 2 ≤ d := Nat.le_of_dvd hd0 hb2dvd
  have hapos : 0 < a := Nat.div_pos hb2le hb2pos
  have hane : a ≠ 0 := hapos.ne'
  have hρ : Submission.rho (c ^ 2) d ≤ 2 ^ (Nat.primeFactors d).card * b := by
    have h := rho_csq_le c d hd0
    rw [← hb] at h
    exact h
  have hρR : ((Submission.rho (c ^ 2) d : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (Nat.primeFactors d).card * (b : ℝ) := by
    calc ((Submission.rho (c ^ 2) d : ℕ) : ℝ)
        ≤ ((2 ^ (Nat.primeFactors d).card * b : ℕ) : ℝ) := by exact_mod_cast hρ
      _ = (2 : ℝ) ^ (Nat.primeFactors d).card * (b : ℝ) := by push_cast; ring
  have hpf : Nat.primeFactors d = Nat.primeFactors a ∪ Nat.primeFactors b := by
    rw [← hd_eq, Nat.primeFactors_mul hane (pow_ne_zero 2 hbne),
      Nat.primeFactors_pow b (by norm_num : (2 : ℕ) ≠ 0)]
  have hcard : (Nat.primeFactors d).card ≤ (Nat.primeFactors a).card + (Nat.primeFactors b).card := by
    rw [hpf]; exact Finset.card_union_le _ _
  have h2pow : (2 : ℝ) ^ (Nat.primeFactors d).card
      ≤ (2 : ℝ) ^ (Nat.primeFactors a).card * (2 : ℝ) ^ (Nat.primeFactors b).card := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hcard
  have htau : ((d.divisors.card : ℝ)) ≤ ((a.divisors.card : ℝ)) * (((b ^ 2).divisors.card : ℝ)) := by
    have h := card_divisors_mul_le a (b ^ 2)
    rw [hd_eq] at h
    exact_mod_cast h
  have htauK : ((d.divisors.card : ℝ)) ^ K
      ≤ ((a.divisors.card : ℝ)) ^ K * (((b ^ 2).divisors.card : ℝ)) ^ K := by
    calc ((d.divisors.card : ℝ)) ^ K
        ≤ (((a.divisors.card : ℝ)) * (((b ^ 2).divisors.card : ℝ))) ^ K :=
          Real.rpow_le_rpow (by positivity) htau hK
      _ = ((a.divisors.card : ℝ)) ^ K * (((b ^ 2).divisors.card : ℝ)) ^ K :=
          Real.mul_rpow (by positivity) (by positivity)
  have hdR : (d : ℝ) = (a : ℝ) * (b : ℝ) ^ 2 := by
    rw [← hd_eq]; push_cast; ring
  have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast hane
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbne
  calc ((d.divisors.card : ℝ)) ^ K * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))
      ≤ ((d.divisors.card : ℝ)) ^ K
          * (((2 : ℝ) ^ (Nat.primeFactors d).card * (b : ℝ)) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hρR hdposR.le)
          (Real.rpow_nonneg (by positivity) K)
    _ ≤ (((a.divisors.card : ℝ)) ^ K * (((b ^ 2).divisors.card : ℝ)) ^ K)
          * (((2 : ℝ) ^ (Nat.primeFactors a).card * (2 : ℝ) ^ (Nat.primeFactors b).card * (b : ℝ))
              / (d : ℝ)) := by
        apply mul_le_mul htauK _ (by positivity) (by positivity)
        apply div_le_div_of_nonneg_right _ hdposR.le
        exact mul_le_mul h2pow le_rfl (by positivity) (by positivity)
    _ = Aterm K a * Bterm K b := by
        rw [Aterm, Bterm, hdR]
        field_simp

end

open scoped BigOperators

theorem sum_tau_pow_rho_div_le_general (K : ℝ) (hK : 0 ≤ K) : ∃ C B : ℝ, 0 < C ∧ ∀ c D : ℕ, (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))) ≤ C * (Real.log ((D : ℝ) + 2)) ^ B := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, K ≤ (m : ℝ) := ⟨Nat.ceil K, Nat.le_ceil K⟩
  obtain ⟨C1, hC1pos, hC1⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit (m + 1)
  obtain ⟨C2, hC2pos, hC2⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit (2 * m + 1)
  set B : ℝ := (2 : ℝ) ^ (m + 1) + (2 : ℝ) ^ (2 * m + 1) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  refine ⟨max (C1 * C2) ((Real.log 2) ^ (-B)), B, ?_, ?_⟩
  · exact lt_of_lt_of_le (mul_pos hC1pos hC2pos) (le_max_left _ _)
  · intro c D
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCl_le : (Real.log 2) ^ (-B) ≤ max (C1 * C2) ((Real.log 2) ^ (-B)) := le_max_right _ _
    have hCmaxpos : 0 < max (C1 * C2) ((Real.log 2) ^ (-B)) :=
      lt_of_lt_of_le (mul_pos hC1pos hC2pos) (le_max_left _ _)
    have hone_eq : (Real.log 2) ^ (-B) * (Real.log 2) ^ B = 1 := by
      rw [← Real.rpow_add hlog2pos]; norm_num
    rcases Nat.lt_or_ge D 2 with hDlt | hDge
    · -- `D = 0` or `D = 1`
      have hD01 : D = 0 ∨ D = 1 := by omega
      have hF1 : (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))) ≤ 1 := by
        rcases hD01 with h | h
        · subst h
          have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
            rw [Finset.Icc_eq_empty_iff]; norm_num
          rw [hempty, Finset.sum_empty]; norm_num
        · subst h
          have hone : Finset.Icc 1 1 = ({1} : Finset ℕ) := by
            ext n; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
          rw [hone, Finset.sum_singleton]
          have hρ : Submission.rho (c ^ 2) 1 ≤ 1 := by
            have h := rho_csq_le c 1 (by norm_num)
            have hd2 : d2 1 = 1 := by simp [d2]
            have hpf1 : (Nat.primeFactors 1).card = 0 := by simp
            rw [hd2, hpf1, pow_zero, mul_one] at h
            exact h
          have hρR : (Submission.rho (c ^ 2) 1 : ℝ) ≤ 1 := by exact_mod_cast hρ
          have htau1 : (1 : ℕ).divisors.card = 1 := by rw [Nat.divisors_one]; simp
          rw [htau1]
          have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
          rw [h1, Real.one_rpow, one_mul, div_one]
          exact hρR
      have hlog_le : (Real.log 2) ^ B ≤ (Real.log ((D : ℝ) + 2)) ^ B := by
        apply Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) _ hBnn
        apply Real.log_le_log (by norm_num)
        have : (0 : ℝ) ≤ (D : ℝ) := by positivity
        linarith
      have hone_le : (1 : ℝ) ≤ max (C1 * C2) ((Real.log 2) ^ (-B))
          * (Real.log ((D : ℝ) + 2)) ^ B := by
        calc (1 : ℝ) = (Real.log 2) ^ (-B) * (Real.log 2) ^ B := hone_eq.symm
          _ ≤ max (C1 * C2) ((Real.log 2) ^ (-B)) * (Real.log ((D : ℝ) + 2)) ^ B :=
              mul_le_mul hCl_le hlog_le
                (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) B) hCmaxpos.le
      exact le_trans hF1 hone_le
    · -- `D ≥ 2`
      have hD2 : 2 ≤ D := hDge
      have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
      have hpt : ∀ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))
            ≤ Aterm K (d / (d2 d) ^ 2) * Bterm K (d2 d) :=
        fun d hd => summand_le K hK c d (Finset.mem_Icc.mp hd).1
      have hinj : Set.InjOn (fun d => (d / (d2 d) ^ 2, d2 d)) ↑(Finset.Icc 1 D) := by
        intro d _ d' _ heq
        have hb : d2 d = d2 d' := congrArg Prod.snd heq
        have ha : d / (d2 d) ^ 2 = d' / (d2 d') ^ 2 := congrArg Prod.fst heq
        calc d = d / (d2 d) ^ 2 * (d2 d) ^ 2 := (Nat.div_mul_cancel (d2_sq_dvd d)).symm
          _ = d' / (d2 d') ^ 2 * (d2 d') ^ 2 := by rw [ha, hb]
          _ = d' := Nat.div_mul_cancel (d2_sq_dvd d')
      have hsub : (Finset.Icc 1 D).image (fun d => (d / (d2 d) ^ 2, d2 d))
          ⊆ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D) := by
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨d, hd, rfl⟩ := hp
        rw [Finset.mem_product]
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : 0 < d := hd1
        have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
        have hb2dvd : (d2 d) ^ 2 ∣ d := d2_sq_dvd d
        have hb2pos : 0 < (d2 d) ^ 2 := Nat.pos_of_dvd_of_pos hb2dvd hd0
        have hb2le : (d2 d) ^ 2 ≤ d := Nat.le_of_dvd hd0 hb2dvd
        have hKpos : 0 < d2 d := d2_pos d hd0
        have hKle : d2 d ≤ D := by
          have h1 : d2 d ≤ (d2 d) ^ 2 := by
            have := Nat.le_mul_of_pos_right (d2 d) hKpos
            simpa [pow_two] using this
          exact le_trans (le_trans h1 hb2le) hdD
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_Icc]
          exact ⟨Nat.div_pos hb2le hb2pos, le_trans (Nat.div_le_self d _) hdD⟩
        · rw [Finset.mem_Icc]; exact ⟨hKpos, hKle⟩
      have hF : (∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ)))
          ≤ (∑ a ∈ Finset.Icc 1 D, Aterm K a) * (∑ b ∈ Finset.Icc 1 D, Bterm K b) := by
        calc ∑ d ∈ Finset.Icc 1 D,
              ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))
            ≤ ∑ d ∈ Finset.Icc 1 D, Aterm K (d / (d2 d) ^ 2) * Bterm K (d2 d) :=
              Finset.sum_le_sum hpt
          _ = ∑ p ∈ (Finset.Icc 1 D).image (fun d => (d / (d2 d) ^ 2, d2 d)),
                Aterm K p.1 * Bterm K p.2 := by
              rw [Finset.sum_image (f := fun p => Aterm K p.1 * Bterm K p.2) hinj]
          _ ≤ ∑ p ∈ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D), Aterm K p.1 * Bterm K p.2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun p _ _ => mul_nonneg (Aterm_nonneg K p.1) (Bterm_nonneg K p.2))
          _ = (∑ a ∈ Finset.Icc 1 D, Aterm K a) * (∑ b ∈ Finset.Icc 1 D, Bterm K b) := by
              rw [Finset.sum_product, Finset.sum_mul_sum]
      have hP : (∑ a ∈ Finset.Icc 1 D, Aterm K a)
          ≤ C1 * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (m + 1)) := by
        calc ∑ a ∈ Finset.Icc 1 D, Aterm K a
            ≤ ∑ a ∈ Finset.Icc 1 D, ((a.divisors.card : ℝ)) ^ (m + 1) / (a : ℝ) :=
              Finset.sum_le_sum (fun a ha => Aterm_le K hm a (Finset.mem_Icc.mp ha).1)
          _ ≤ C1 * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (m + 1)) := hC1 D hD2
      have hQ : (∑ b ∈ Finset.Icc 1 D, Bterm K b)
          ≤ C2 * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (2 * m + 1)) := by
        calc ∑ b ∈ Finset.Icc 1 D, Bterm K b
            ≤ ∑ b ∈ Finset.Icc 1 D, ((b.divisors.card : ℝ)) ^ (2 * m + 1) / (b : ℝ) :=
              Finset.sum_le_sum (fun b hb => Bterm_le K hK hm b (Finset.mem_Icc.mp hb).1)
          _ ≤ C2 * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (2 * m + 1)) := hC2 D hD2
      have haux : (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (m + 1))
            * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (2 * m + 1))
          = (Real.log (D : ℝ)) ^ B := by
        rw [hB]
        exact (Real.rpow_add hlogD ((2 : ℝ) ^ (m + 1)) ((2 : ℝ) ^ (2 * m + 1))).symm
      calc ∑ d ∈ Finset.Icc 1 D,
            ((d.divisors.card : ℝ) ^ K) * ((Submission.rho (c ^ 2) d : ℝ) / (d : ℝ))
          ≤ (∑ a ∈ Finset.Icc 1 D, Aterm K a) * (∑ b ∈ Finset.Icc 1 D, Bterm K b) := hF
        _ ≤ (C1 * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (m + 1)))
              * (C2 * (Real.log (D : ℝ)) ^ ((2 : ℝ) ^ (2 * m + 1))) :=
            mul_le_mul hP hQ (Finset.sum_nonneg (fun b _ => Bterm_nonneg K b)) (by positivity)
        _ = C1 * C2 * (Real.log (D : ℝ)) ^ B := by rw [← haux]; ring
        _ ≤ max (C1 * C2) ((Real.log 2) ^ (-B)) * (Real.log ((D : ℝ) + 2)) ^ B := by
            apply mul_le_mul (le_max_left _ _) _ (by positivity) hCmaxpos.le
            apply Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))) _ hBnn
            apply Real.log_le_log (by positivity)
            linarith

end Commons.NumberTheory.FriedlanderIwaniec
