import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola
import Submission.Commons.NumberTheory.Totient.totient_mul_gcd
import Submission.Commons.NumberTheory.Totient.sum_divisors_mu_sq_div_totient
import Submission.Commons.NumberTheory.Totient.sum_mu_sq_div_d_mul_totient_le_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le

namespace Commons.NumberTheory.ArithmeticFunction

open Finset

noncomputable section

private def T (r x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ r / (n.totient : ℝ)

/-- The totient is submultiplicative: `φ a · φ b ≤ φ (a·b)`. -/
private theorem totient_mul_ge (a b : ℕ) :
    Nat.totient a * Nat.totient b ≤ Nat.totient (a * b) := by
  rcases Nat.eq_zero_or_pos (Nat.gcd a b) with hg | hg
  · have h := Nat.gcd_eq_zero_iff.mp hg
    obtain ⟨rfl, rfl⟩ := h
    simp [Nat.totient_zero]
  · have h := Commons.NumberTheory.Totient.totient_mul_gcd a b
    have hle : Nat.totient (Nat.gcd a b) ≤ Nat.gcd a b := Nat.totient_le _
    have h2 : Nat.totient (a * b) * Nat.totient (Nat.gcd a b) ≤
        Nat.totient (a * b) * Nat.gcd a b := Nat.mul_le_mul_left _ hle
    rw [h] at h2
    exact Nat.le_of_mul_le_mul_right h2 hg

private lemma harm_bound (m : ℕ) :
    (∑ e ∈ Finset.Icc 1 m, (1 : ℝ) / (e : ℝ)) ≤ 1 + Real.log (m : ℝ) := by
  rw [← Commons.NumberTheory.DivisorSum.harmonic_cast_eq_sum m]
  exact harmonic_le_one_add_log m

private lemma term_le (r d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) :
    (((d * e).divisors.card : ℝ)) ^ r / ((d * e).totient : ℝ)
      ≤ (((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ)) *
        (((e.divisors.card : ℝ)) ^ r / (e.totient : ℝ)) := by
  have hτ : (((d * e).divisors.card : ℝ)) ≤
      ((d.divisors.card : ℝ)) * ((e.divisors.card : ℝ)) := by
    have := Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le d e
    exact_mod_cast this
  have hφ : ((d.totient : ℝ)) * ((e.totient : ℝ)) ≤ ((d * e).totient : ℝ) := by
    have := totient_mul_ge d e
    exact_mod_cast this
  have hnum : (((d * e).divisors.card : ℝ)) ^ r ≤
      ((d.divisors.card : ℝ)) ^ r * ((e.divisors.card : ℝ)) ^ r := by
    calc (((d * e).divisors.card : ℝ)) ^ r
        ≤ (((d.divisors.card : ℝ)) * ((e.divisors.card : ℝ))) ^ r :=
          pow_le_pow_left₀ (by positivity) hτ r
      _ = ((d.divisors.card : ℝ)) ^ r * ((e.divisors.card : ℝ)) ^ r := by rw [mul_pow]
  have hφdepos : (0 : ℝ) < ((d * e).totient : ℝ) := by
    have : 0 < (d * e).totient := Nat.totient_pos.mpr (Nat.mul_pos (by omega) (by omega))
    exact_mod_cast this
  have hφdpos : (0 : ℝ) < (d.totient : ℝ) := by
    have : 0 < d.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hφepos : (0 : ℝ) < (e.totient : ℝ) := by
    have : 0 < e.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hDpos : (0 : ℝ) < (d.totient : ℝ) * (e.totient : ℝ) := mul_pos hφdpos hφepos
  calc (((d * e).divisors.card : ℝ)) ^ r / ((d * e).totient : ℝ)
      ≤ (((d.divisors.card : ℝ)) ^ r * ((e.divisors.card : ℝ)) ^ r) /
          ((d * e).totient : ℝ) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hφdepos)
    _ ≤ (((d.divisors.card : ℝ)) ^ r * ((e.divisors.card : ℝ)) ^ r) /
          ((d.totient : ℝ) * (e.totient : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hDpos hφ
    _ = ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) *
          (((e.divisors.card : ℝ)) ^ r / (e.totient : ℝ)) := by
        rw [div_mul_div_comm]

private lemma T_zero_le (x : ℕ) (hx : 1 ≤ x) :
    T 0 x ≤ 2 * (Real.log (x : ℝ) + 1) := by
  set f : ℕ → ℕ → ℝ := fun d e =>
    (((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 / (d.totient : ℝ) *
      (1 / ((d : ℝ) * (e : ℝ))) with hf
  have h1 : T 0 x = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d) := by
    unfold T
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_zero]
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hR : (∑ d ∈ n.divisors, f d (n / d)) =
        ∑ d ∈ n.divisors, (((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 /
            (d.totient : ℝ) * (1 / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      simp only [hf]
      rw [hmul]
    rw [hR, ← Finset.sum_mul,
      Commons.NumberTheory.Totient.sum_divisors_mu_sq_div_totient n hn1]
    field_simp
  have hrange : Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hz : (∑ d ∈ (0 : ℕ).divisors, f d (0 / d)) = 0 := by
    simp [Nat.divisors_zero]
  have h2 : (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d) := by
    rw [hrange, Finset.sum_insert (by simp), hz, zero_add]
  have h4 : (∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e :=
    Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola f x
  have h5 : (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e) ≤
      ∑ d ∈ Finset.Icc 1 x,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ))) *
          (1 + Real.log (x : ℝ)) := by
    calc (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e)
        = ∑ d ∈ Finset.Icc 1 x,
            ((((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ))) *
              (∑ e ∈ Finset.Icc 1 (x / d), (1 : ℝ) / (e : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
          have he0 : (e : ℝ) ≠ 0 := by
            have : 1 ≤ e := (Finset.mem_Icc.mp he).1
            exact_mod_cast (by omega : e ≠ 0)
          have hφ0 : (d.totient : ℝ) ≠ 0 := by
            have : 0 < d.totient := Nat.totient_pos.mpr (by omega)
            exact_mod_cast this.ne'
          simp only [hf]
          field_simp
      _ ≤ ∑ d ∈ Finset.Icc 1 x,
            ((((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ))) *
              (1 + Real.log (x : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdx : d ≤ x := (Finset.mem_Icc.mp hd).2
          have hxdle : x / d ≤ x := Nat.div_le_self x d
          have hxd1 : 1 ≤ x / d := (Nat.one_le_div_iff (by omega : 0 < d)).mpr hdx
          have hxdpos : (0 : ℝ) < ((x / d : ℕ) : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le zero_lt_one hxd1)
          have hh : (∑ e ∈ Finset.Icc 1 (x / d), (1 : ℝ) / (e : ℝ)) ≤
              1 + Real.log ((x / d : ℕ) : ℝ) := harm_bound (x / d)
          have hlog : Real.log ((x / d : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
            Real.log_le_log hxdpos (by exact_mod_cast hxdle)
          have hb : (∑ e ∈ Finset.Icc 1 (x / d), (1 : ℝ) / (e : ℝ)) ≤
              1 + Real.log (x : ℝ) := by linarith
          apply mul_le_mul_of_nonneg_left hb
          exact div_nonneg (sq_nonneg _) (by positivity)
  calc T 0 x = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d) := h1
    _ = ∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d) := h2
    _ = ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e := h4
    _ ≤ ∑ d ∈ Finset.Icc 1 x,
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ))) *
            (1 + Real.log (x : ℝ)) := h5
    _ = (∑ d ∈ Finset.Icc 1 x,
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ)) ^ 2 / ((d : ℝ) * (d.totient : ℝ)))) *
            (1 + Real.log (x : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ 2 * (1 + Real.log (x : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
          (Commons.NumberTheory.Totient.sum_mu_sq_div_d_mul_totient_le_two x)
        have : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
        linarith
    _ = 2 * (Real.log (x : ℝ) + 1) := by ring

private lemma T_succ_le_sum (r x : ℕ) (hx : 1 ≤ x) :
    T (r + 1) x ≤ ∑ d ∈ Finset.Icc 1 x,
      ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) * T r (x / d) := by
  set f : ℕ → ℕ → ℝ := fun d e =>
    ((d * e).divisors.card : ℝ) ^ r / ((d * e).totient : ℝ) with hf
  have h1 : T (r + 1) x = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d) := by
    unfold T
    apply Finset.sum_congr rfl
    intro n hn
    have hR : (∑ d ∈ n.divisors, f d (n / d)) =
        ∑ d ∈ n.divisors, ((n.divisors.card : ℝ)) ^ r / (n.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      simp only [hf]
      rw [hmul]
    rw [hR, Finset.sum_const, nsmul_eq_mul, pow_succ', mul_div_assoc]
  have hrange : Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hz : (∑ d ∈ (0 : ℕ).divisors, f d (0 / d)) = 0 := by simp [Nat.divisors_zero]
  have h2 : (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d) := by
    rw [hrange, Finset.sum_insert (by simp), hz, zero_add]
  have h4 : (∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e :=
    Commons.NumberTheory.ArithmeticFunction.sum_divisors_swap_hyperbola f x
  have h5 : (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e) ≤
      ∑ d ∈ Finset.Icc 1 x,
        ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) * T r (x / d) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hfac : (∑ e ∈ Finset.Icc 1 (x / d), f d e) ≤
        ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) *
          (∑ e ∈ Finset.Icc 1 (x / d), ((e.divisors.card : ℝ)) ^ r / (e.totient : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      simp only [hf]
      exact term_le r d e hd1 he1
    have hTr : (∑ e ∈ Finset.Icc 1 (x / d), ((e.divisors.card : ℝ)) ^ r / (e.totient : ℝ))
        = T r (x / d) := rfl
    calc (∑ e ∈ Finset.Icc 1 (x / d), f d e)
        ≤ ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) *
          (∑ e ∈ Finset.Icc 1 (x / d), ((e.divisors.card : ℝ)) ^ r / (e.totient : ℝ)) := hfac
      _ = ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) * T r (x / d) := by rw [hTr]
  calc T (r + 1) x = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, f d (n / d) := h1
    _ = ∑ n ∈ Finset.range (x + 1), ∑ d ∈ n.divisors, f d (n / d) := h2
    _ = ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), f d e := h4
    _ ≤ ∑ d ∈ Finset.Icc 1 x,
        ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) * T r (x / d) := h5

private lemma T_bound : ∀ r x, 1 ≤ x →
    T r x ≤ (2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r) := by
  intro r
  induction r with
  | zero =>
      intro x hx
      have h := T_zero_le x hx
      simpa using h
  | succ r ih =>
      intro x hx
      have hstep := T_succ_le_sum r x hx
      have hih : ∀ d ∈ Finset.Icc 1 x,
          T r (x / d) ≤ (2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdx : d ≤ x := (Finset.mem_Icc.mp hd).2
        have hxd1 : 1 ≤ x / d := (Nat.one_le_div_iff (by omega : 0 < d)).mpr hdx
        have hxdle : x / d ≤ x := Nat.div_le_self x d
        have hxdpos : (0 : ℝ) < ((x / d : ℕ) : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le zero_lt_one hxd1)
        have hlog : Real.log ((x / d : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
          Real.log_le_log hxdpos (by exact_mod_cast hxdle)
        have hpow : (Real.log ((x / d : ℕ) : ℝ) + 1) ^ (2 ^ r) ≤
            (Real.log (x : ℝ) + 1) ^ (2 ^ r) := by
          apply pow_le_pow_left₀
          · have : (0 : ℝ) ≤ Real.log ((x / d : ℕ) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast hxd1)
            linarith
          · linarith
        calc T r (x / d) ≤
              (2 : ℝ) ^ (2 ^ r) * (Real.log ((x / d : ℕ) : ℝ) + 1) ^ (2 ^ r) :=
              ih (x / d) hxd1
          _ ≤ (2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
      have hC : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r) := by positivity
      calc T (r + 1) x
          ≤ ∑ d ∈ Finset.Icc 1 x,
              ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) * T r (x / d) := hstep
        _ ≤ ∑ d ∈ Finset.Icc 1 x,
              ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ) *
                ((2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r)) := by
            apply Finset.sum_le_sum
            intro d hd
            exact mul_le_mul_of_nonneg_left (hih d hd) (by positivity)
        _ = (∑ d ∈ Finset.Icc 1 x, ((d.divisors.card : ℝ)) ^ r / (d.totient : ℝ)) *
              ((2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r)) := by
            rw [Finset.sum_mul]
        _ = T r x * ((2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r)) := rfl
        _ ≤ ((2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r)) *
              ((2 : ℝ) ^ (2 ^ r) * (Real.log (x : ℝ) + 1) ^ (2 ^ r)) := by
            exact mul_le_mul_of_nonneg_right (ih x hx) hC
        _ = (2 : ℝ) ^ (2 ^ (r + 1)) * (Real.log (x : ℝ) + 1) ^ (2 ^ (r + 1)) := by
            have hexp : (2 : ℕ) ^ (r + 1) = 2 ^ r * 2 := by rw [pow_succ]
            rw [hexp, pow_mul, pow_mul]
            ring

/-- The divisor-sum bound `Σ_{M ≤ Q} τ(M)^{3k}/φ(M) ≪ (log Q)^{2^{3k}}` with a
constant that is UNIFORM in `Q` (only depending on `k`). -/
theorem sum_card_divisors_pow_div_totient_le_uniform (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (3 * k) / (M.totient : ℝ)) ≤
        C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)) := by
  refine ⟨(2 : ℝ) ^ (2 ^ (3 * k)), by positivity, ?_⟩
  intro Q
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    have h0 : (∑ M ∈ Finset.Icc 1 0,
        ((M.divisors.card : ℝ)) ^ (3 * k) / (M.totient : ℝ)) = 0 := by simp
    rw [h0]
    positivity
  · have h := T_bound (3 * k) Q hQ
    simpa only [T] using h

end

end Commons.NumberTheory.ArithmeticFunction
