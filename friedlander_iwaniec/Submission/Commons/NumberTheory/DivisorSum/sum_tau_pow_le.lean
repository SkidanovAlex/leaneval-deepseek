import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_totient_asymptotic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le

open Finset

namespace Commons.NumberTheory.DivisorSum

/-- The number of divisors of `n`, as a real number. -/
private def tauR (n : ℕ) : ℝ := (n.divisors.card : ℝ)

/-- `S k x = ∑_{n ≤ x} τ(n)^k`. -/
private def Ssum (k x : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 x, (tauR n) ^ k

/-- `T k x = ∑_{n ≤ x} τ(n)^k / n`. -/
private noncomputable def Tsum (k x : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 x, (tauR n) ^ k / (n : ℝ)

private lemma tauR_nonneg (n : ℕ) : 0 ≤ tauR n := by unfold tauR; positivity

private lemma tauR_mul_le (m n : ℕ) : tauR (m * n) ≤ tauR m * tauR n := by
  unfold tauR
  exact_mod_cast Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le m n

/-- Reindexing the divisor sum: `∑_{n ≤ x} h n τ(n) = ∑_{d ≤ x} ∑_{e ≤ x/d} h (d e)`. -/
private lemma sum_mul_tauR (h : ℕ → ℝ) (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, h n * tauR n)
      = ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), h (d * e) := by
  have key : (∑ n ∈ Finset.Icc 1 x, h n * tauR n)
      = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, h (d * (n / d)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hcard : tauR n = ∑ _d ∈ n.divisors, (1 : ℝ) := by
      simp only [tauR, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [mul_one]
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    rw [Nat.mul_div_cancel' hdvd]
  rw [key]
  exact Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_swap (fun d e => h (d * e)) x

/-- `(2^k - 1) + 2^k = 2^(k+1) - 1`. -/
private lemma pred_add (k : ℕ) : (2 ^ k - 1) + 2 ^ k = 2 ^ (k + 1) - 1 := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  rw [pow_succ]; omega

/-- `T k x ≤ (T k x)²` upgrade: the recursion `T (k+1) ≤ T k ^ 2`. -/
private lemma Tsum_succ_le_sq (k x : ℕ) : Tsum (k + 1) x ≤ (Tsum k x) ^ 2 := by
  have hstep : Tsum (k + 1) x
      = ∑ n ∈ Finset.Icc 1 x, ((tauR n) ^ k / (n : ℝ)) * tauR n := by
    unfold Tsum
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_succ]; ring
  rw [hstep, sum_mul_tauR (fun n => (tauR n) ^ k / (n : ℝ)) x]
  calc ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), (tauR (d * e)) ^ k / ((d * e : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d),
          (tauR d) ^ k * (tauR e) ^ k / ((d : ℝ) * (e : ℝ)) := by
        apply Finset.sum_le_sum; intro d hd
        apply Finset.sum_le_sum; intro e he
        rw [show ((d * e : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) by push_cast; ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc (tauR (d * e)) ^ k ≤ (tauR d * tauR e) ^ k :=
              pow_le_pow_left₀ (tauR_nonneg _) (tauR_mul_le d e) k
          _ = (tauR d) ^ k * (tauR e) ^ k := mul_pow _ _ _
    _ = ∑ d ∈ Finset.Icc 1 x,
          ((tauR d) ^ k / (d : ℝ)) * (∑ e ∈ Finset.Icc 1 (x / d), (tauR e) ^ k / (e : ℝ)) := by
        apply Finset.sum_congr rfl; intro d hd
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e he
        ring
    _ ≤ ∑ d ∈ Finset.Icc 1 x, ((tauR d) ^ k / (d : ℝ)) * (Tsum k x) := by
        apply Finset.sum_le_sum; intro d hd
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (pow_nonneg (tauR_nonneg d) k) (by positivity))
        unfold Tsum
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          simp only [Finset.mem_Icc] at he ⊢
          exact ⟨he.1, le_trans he.2 (Nat.div_le_self x d)⟩
        · intro e he _
          exact div_nonneg (pow_nonneg (tauR_nonneg e) k) (by positivity)
    _ = (Tsum k x) ^ 2 := by
        rw [← Finset.sum_mul]
        have hsum : (∑ d ∈ Finset.Icc 1 x, (tauR d) ^ k / (d : ℝ)) = Tsum k x := rfl
        rw [hsum]; ring

/-- Bound for the `1/n`-weighted sum: `T k x ≪ (log (x+1))^{2^k}`. -/
private lemma T_bound_aux : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
    Tsum k x ≤ C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    refine ⟨1 + (Real.log 2)⁻¹, by positivity, ?_⟩
    intro x hx
    have hT0 : Tsum 0 x = ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / (n : ℝ) := by
      unfold Tsum
      apply Finset.sum_congr rfl
      intro n hn
      simp
    have h1 := Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log x
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogx : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
      Real.log_le_log hxpos (by linarith)
    have hlog2le : Real.log 2 ≤ Real.log ((x : ℝ) + 1) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hone_le : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log ((x : ℝ) + 1) := by
      have hinvpos : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlog2
      have h := mul_le_mul_of_nonneg_left hlog2le hinvpos.le
      rwa [inv_mul_cancel₀ (ne_of_gt hlog2)] at h
    have hbase : Tsum 0 x ≤ (1 + (Real.log 2)⁻¹) * Real.log ((x : ℝ) + 1) := by
      rw [hT0]
      calc ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (x : ℝ) := h1
        _ ≤ (1 + (Real.log 2)⁻¹) * Real.log ((x : ℝ) + 1) := by nlinarith [hone_le, hlogx]
    simpa using hbase
  | succ k ih =>
    obtain ⟨C, hCpos, hC⟩ := ih
    refine ⟨C ^ 2, by positivity, ?_⟩
    intro x hx
    have hTk : Tsum k x ≤ C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k) := hC x hx
    have hLnn : 0 ≤ Real.log ((x : ℝ) + 1) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      linarith
    have hTnonneg : 0 ≤ Tsum k x := by
      unfold Tsum
      apply Finset.sum_nonneg; intro n hn
      exact div_nonneg (pow_nonneg (tauR_nonneg n) k) (by positivity)
    have hsq : Tsum (k + 1) x ≤ (Tsum k x) ^ 2 := Tsum_succ_le_sq k x
    calc Tsum (k + 1) x ≤ (Tsum k x) ^ 2 := hsq
      _ ≤ (C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ hTnonneg hTk 2
      _ = C ^ 2 * (Real.log ((x : ℝ) + 1)) ^ (2 ^ (k + 1)) := by
            rw [mul_pow, ← pow_mul, ← pow_succ]

/-- Main induction: `S k x ≪ x (log (x+1))^{2^k - 1}`. -/
private lemma S_bound_aux : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
    Ssum k x ≤ C * (x : ℝ) * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have hS0 : Ssum 0 x = (x : ℝ) := by
      unfold Ssum
      simp only [pow_zero]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      simp
    rw [hS0, (by norm_num : (2:ℕ) ^ 0 - 1 = 0), pow_zero]
    simp
  | succ k ih =>
    obtain ⟨C, hCpos, hC⟩ := ih
    obtain ⟨C', hC'pos, hC'⟩ := T_bound_aux k
    refine ⟨C * C', mul_pos hCpos hC'pos, ?_⟩
    intro x hx
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hLnn : 0 ≤ Real.log ((x : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hEq : Ssum (k + 1) x
        = ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), (tauR (d * e)) ^ k := by
      have h1 : Ssum (k + 1) x = ∑ n ∈ Finset.Icc 1 x, (tauR n) ^ k * tauR n := by
        unfold Ssum
        apply Finset.sum_congr rfl
        intro n hn
        rw [pow_succ]
      rw [h1, sum_mul_tauR (fun n => (tauR n) ^ k) x]
    rw [hEq]
    calc ∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 (x / d), (tauR (d * e)) ^ k
        ≤ ∑ d ∈ Finset.Icc 1 x, (tauR d) ^ k * Ssum k (x / d) := by
          apply Finset.sum_le_sum; intro d hd
          unfold Ssum; rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro e he
          calc (tauR (d * e)) ^ k ≤ (tauR d * tauR e) ^ k :=
                pow_le_pow_left₀ (tauR_nonneg _) (tauR_mul_le d e) k
            _ = (tauR d) ^ k * (tauR e) ^ k := mul_pow _ _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 x,
            (tauR d) ^ k * (C * ((x : ℝ) / (d : ℝ)) * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1)) := by
          apply Finset.sum_le_sum; intro d hd
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (tauR_nonneg d) k)
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdx : d ≤ x := (Finset.mem_Icc.mp hd).2
          have hxd1 : 1 ≤ x / d := by
            have := Nat.div_pos hdx (by omega)
            omega
          have hIH := hC (x / d) hxd1
          have hcast : (((x / d : ℕ)) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
          have hlogle : Real.log ((((x / d : ℕ)) : ℝ) + 1) ≤ Real.log ((x : ℝ) + 1) := by
            apply Real.log_le_log (by positivity)
            have : (((x / d : ℕ)) : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.div_le_self x d
            linarith
          have hLn1 : 0 ≤ Real.log ((((x / d : ℕ)) : ℝ) + 1) := by
            apply Real.log_nonneg
            have : (0 : ℝ) ≤ (((x / d : ℕ)) : ℝ) := by positivity
            linarith
          have hpowle : (Real.log ((((x / d : ℕ)) : ℝ) + 1)) ^ (2 ^ k - 1)
              ≤ (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) :=
            pow_le_pow_left₀ hLn1 hlogle _
          calc Ssum k (x / d)
              ≤ C * (((x / d : ℕ)) : ℝ) * (Real.log ((((x / d : ℕ)) : ℝ) + 1)) ^ (2 ^ k - 1) := hIH
            _ ≤ C * ((x : ℝ) / (d : ℝ)) * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hcast hCpos.le) hpowle
                    (pow_nonneg hLn1 _) (mul_nonneg hCpos.le (by positivity))
      _ = C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) * (x : ℝ) * Tsum k x := by
          rw [show (∑ d ∈ Finset.Icc 1 x,
                (tauR d) ^ k * (C * ((x : ℝ) / (d : ℝ)) * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1)))
              = ∑ d ∈ Finset.Icc 1 x,
                (C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) * (x : ℝ)) * ((tauR d) ^ k / (d : ℝ)) by
                  apply Finset.sum_congr rfl; intro d hd; ring]
          rw [show Tsum k x = ∑ d ∈ Finset.Icc 1 x, (tauR d) ^ k / (d : ℝ) from rfl]
          rw [← Finset.mul_sum]
      _ ≤ C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) * (x : ℝ)
            * (C' * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k)) := by
          apply mul_le_mul_of_nonneg_left (hC' x hx)
          exact mul_nonneg (mul_nonneg hCpos.le (pow_nonneg hLnn _)) (by positivity)
      _ = (C * C') * (x : ℝ) * (Real.log ((x : ℝ) + 1)) ^ (2 ^ (k + 1) - 1) := by
          have hre : C * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) * (x : ℝ)
                * (C' * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k))
              = (C * C') * (x : ℝ) * ((Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1)
                  * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k)) := by ring
          rw [hre, ← pow_add, pred_add]

/-- The main theorem. -/
theorem sum_tau_pow_le (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ k)
        ≤ C * (x : ℝ) * (Real.log ((x : ℝ) + 1)) ^ (2 ^ k - 1) := by
  obtain ⟨C, hCpos, hC⟩ := S_bound_aux k
  exact ⟨C, hCpos, fun x hx => hC x hx⟩

end Commons.NumberTheory.DivisorSum
