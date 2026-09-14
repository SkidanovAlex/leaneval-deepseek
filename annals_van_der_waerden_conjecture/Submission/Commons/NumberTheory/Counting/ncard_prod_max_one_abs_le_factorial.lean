import Mathlib
import Submission.Commons.NumberTheory.Counting.ncard_prod_max_one_abs_le
import Submission.Commons.Analysis.SpecialFunctions.sum_pow_div_factorial_sq_le
import Submission.Commons.Analysis.SpecialFunctions.choose_pow_div_factorial_le
import Submission.Commons.Analysis.SumIntegral.monomial_log_sum_le
import Submission.Commons.Algebra.BigOperators.choose_pascal_sum_identity_pos

set_option maxHeartbeats 3200000

namespace Commons.NumberTheory.Counting

open Finset
open scoped BigOperators

noncomputable section

def Qpoly (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (((k - 1).choose j : ℕ) : ℝ) * t ^ j / (((j.factorial : ℕ) : ℝ))





lemma Qpoly_nonneg (k : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Qpoly k t := by
  unfold Qpoly
  apply Finset.sum_nonneg
  intro j hj
  apply div_nonneg
  · apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact pow_nonneg ht j
  · positivity

lemma Qpoly_mono (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : Qpoly k s ≤ Qpoly k t := by
  unfold Qpoly
  apply Finset.sum_le_sum
  intro j hj
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ hs hst j

lemma Qpoly_le_exp (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Qpoly k t ≤ Real.exp (2 * Real.sqrt (k * t)) := by
  unfold Qpoly
  have hkt : (0:ℝ) ≤ (k:ℝ) * t := by positivity
  calc (∑ j ∈ Finset.range k, (((k - 1).choose j : ℕ) : ℝ) * t ^ j / (((j.factorial : ℕ) : ℝ)))
      ≤ ∑ j ∈ Finset.range k, ((k:ℝ) * t) ^ j / ((((j.factorial : ℕ) : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by positivity
        have hc : (((k - 1).choose j : ℕ) : ℝ) ≤ (k:ℝ)^j / ((j.factorial : ℕ) : ℝ) := by
          calc (((k - 1).choose j : ℕ) : ℝ) ≤ (((k-1:ℕ)) : ℝ)^j / ((j.factorial : ℕ) : ℝ) :=
                Nat.choose_le_pow_div j (k-1)
            _ ≤ (k:ℝ)^j / ((j.factorial : ℕ) : ℝ) := by
                apply div_le_div_of_nonneg_right _ hfac.le
                exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le k 1) j
        calc (((k - 1).choose j : ℕ) : ℝ) * t ^ j / (((j.factorial : ℕ) : ℝ))
            ≤ ((k:ℝ)^j / ((j.factorial : ℕ) : ℝ)) * t ^ j / (((j.factorial : ℕ) : ℝ)) := by
              apply div_le_div_of_nonneg_right _ hfac.le
              exact mul_le_mul_of_nonneg_right hc (pow_nonneg ht j)
          _ = ((k:ℝ) * t) ^ j / ((((j.factorial : ℕ) : ℝ)) ^ 2) := by
              rw [mul_pow]; field_simp
    _ ≤ Real.exp (2 * Real.sqrt ((k:ℝ) * t)) :=
        Commons.Analysis.SpecialFunctions.sum_pow_div_factorial_sq_le k ((k:ℝ)*t) hkt

lemma key_step (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Finset.Icc 1 n, Qpoly k (Real.log ((n : ℝ) / (j : ℝ))) / (j : ℝ)) ≤
      Qpoly (k + 1) (Real.log n) := by
  have hcast : ∀ j : ℕ, ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by intro j; push_cast; ring
  have hexp : (∑ j ∈ Finset.Icc 1 n, Qpoly k (Real.log ((n : ℝ) / (j : ℝ))) / (j : ℝ))
      = ∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) / (((i.factorial : ℕ) : ℝ)) *
          (∑ j ∈ Finset.Icc 1 n, (Real.log ((n : ℝ) / (j : ℝ))) ^ i / (j : ℝ)) := by
    unfold Qpoly
    simp only [Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexp]
  calc ∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) / (((i.factorial : ℕ) : ℝ)) *
          (∑ j ∈ Finset.Icc 1 n, (Real.log ((n : ℝ) / (j : ℝ))) ^ i / (j : ℝ))
      ≤ ∑ i ∈ Finset.range k, (((k - 1).choose i : ℕ) : ℝ) / (((i.factorial : ℕ) : ℝ)) *
          ((Real.log (n : ℝ)) ^ i + (Real.log (n : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Commons.Analysis.SumIntegral.monomial_log_sum_le i n hn
    _ = Qpoly (k + 1) (Real.log n) := by
        rw [Qpoly]
        simp only [Nat.add_sub_cancel]
        rw [← Commons.Algebra.BigOperators.choose_pascal_sum_identity_pos k hk (Real.log n)]
        simp only [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          ring
        · apply Finset.sum_congr rfl
          intro i hi
          rw [hcast i]
          have hfac : ((((i + 1).factorial : ℕ)) : ℝ) = (((i:ℝ)+1) * ((i.factorial : ℕ) : ℝ)) := by
            rw [Nat.factorial_succ]; push_cast; ring
          rw [hfac]
          field_simp
          push_cast
          ring

lemma card_posProdTuple_le_Qpoly (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n : ℕ), 1 ≤ n → (Nat.card (PosProdTuple k n) : ℝ) ≤ (n : ℝ) * Qpoly k (Real.log n) := by
  induction k, hk using Nat.le_induction with
  | base =>
      intro n hn
      have h := PosProdTuple.card_le 1 n hn
      simpa [Qpoly] using h
  | succ k hk ih =>
      intro n hn
      have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      calc (Nat.card (PosProdTuple (k + 1) n) : ℝ)
          ≤ ∑ j ∈ Finset.Icc 1 n, (Nat.card (PosProdTuple k (n / j)) : ℝ) := by
              exact_mod_cast PosProdTuple.card_succ_le_sum k n
        _ ≤ ∑ j ∈ Finset.Icc 1 n, (((n / j : ℕ)) : ℝ) * Qpoly k (Real.log (((n / j : ℕ)) : ℝ)) := by
              apply Finset.sum_le_sum
              intro j hj
              rw [Finset.mem_Icc] at hj
              have hdiv : 1 ≤ n / j := Nat.div_pos hj.2 (by omega)
              exact ih (n / j) hdiv
        _ ≤ ∑ j ∈ Finset.Icc 1 n, ((n:ℝ) / (j:ℝ)) * Qpoly k (Real.log ((n:ℝ) / (j:ℝ))) := by
              apply Finset.sum_le_sum
              intro j hj
              rw [Finset.mem_Icc] at hj
              have hjpos : 0 < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
              have hdiv1 : 1 ≤ n / j := Nat.div_pos hj.2 (by omega)
              have hnj_pos : (0:ℝ) < ((n / j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n/j)
              have hle : (((n / j : ℕ)) : ℝ) ≤ (n:ℝ)/(j:ℝ) := Nat.cast_div_le
              have hlogmono : Real.log (((n / j : ℕ)) : ℝ) ≤ Real.log ((n:ℝ)/(j:ℝ)) :=
                Real.log_le_log hnj_pos hle
              have hQnn : 0 ≤ Qpoly k (Real.log (((n / j : ℕ)) : ℝ)) := Qpoly_nonneg k _ (Real.log_nonneg (by exact_mod_cast hdiv1))
              calc (((n / j : ℕ)) : ℝ) * Qpoly k (Real.log (((n / j : ℕ)) : ℝ))
                  ≤ ((n:ℝ)/(j:ℝ)) * Qpoly k (Real.log (((n / j : ℕ)) : ℝ)) :=
                    mul_le_mul_of_nonneg_right hle hQnn
                _ ≤ ((n:ℝ)/(j:ℝ)) * Qpoly k (Real.log ((n:ℝ)/(j:ℝ))) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    apply Qpoly_mono
                    · exact Real.log_nonneg (by exact_mod_cast hdiv1)
                    · exact hlogmono
        _ = (n:ℝ) * ∑ j ∈ Finset.Icc 1 n, Qpoly k (Real.log ((n:ℝ) / (j:ℝ))) / (j:ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ ≤ (n:ℝ) * Qpoly (k + 1) (Real.log n) :=
              mul_le_mul_of_nonneg_left (key_step k hk n hn) (by positivity)


lemma exp_half_le : Real.exp (1/2) ≤ (5:ℝ)/3 := by
  have hsq : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h1 : Real.exp (1/2) = Real.sqrt (Real.exp 1) := by
    rw [← hsq, Real.sqrt_sq (Real.exp_nonneg _)]
  rw [h1]
  rw [Real.sqrt_le_left (show (0:ℝ) ≤ 5/3 by norm_num)]
  linarith [Real.exp_one_lt_d9]

lemma sqrt2_div_four_add : (1:ℝ)/32 + Real.sqrt 2 / 4 ≤ 1/2 := by
  have hsq2 : Real.sqrt 2 ≤ 15/8 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  linarith

lemma Qpoly_bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Qpoly k (Real.log n) ≤
      ((5:ℝ)/3)^k + ((100:ℝ)/3)^k * (n:ℝ) * (1 + Real.log n)^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by
  have ht : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hfactpos : (0:ℝ) < ((((k-1).factorial:ℕ):ℝ)) := by positivity
  have h5nonneg : (0:ℝ) ≤ ((5:ℝ)/3)^k := by positivity
  by_cases hcase : (k:ℝ)/32 ≤ Real.log (n:ℝ)
  · have hC : Qpoly k (Real.log n) ≤
        (Real.log n + ((k-1:ℕ):ℝ))^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by
      simpa [Qpoly] using Commons.Analysis.SpecialFunctions.choose_pow_div_factorial_le k (Real.log n) ht
    have hkn : (k:ℝ) ≤ 32 * Real.log (n:ℝ) := by linarith
    have hkle : (((k-1:ℕ)):ℝ) ≤ 32 * (Real.log (n:ℝ)) := by
      have h1 : ((k-1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.sub_le k 1
      linarith
    have hsum : Real.log (n:ℝ) + ((k-1:ℕ):ℝ) ≤ 33 * (1 + Real.log (n:ℝ)) := by linarith
    have hpowpos : (0:ℝ) ≤ Real.log (n:ℝ) + ((k-1:ℕ):ℝ) := by
      have : (0:ℝ) ≤ ((k-1:ℕ):ℝ) := by positivity
      linarith
    have h33 : (33:ℝ)^(k-1) ≤ ((100:ℝ)/3)^k := by
      have h1 : (33:ℝ)^(k-1) ≤ ((100:ℝ)/3)^(k-1) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) (k-1)
      have h2 : ((100:ℝ)/3)^(k-1) ≤ ((100:ℝ)/3)^k :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
      linarith
    calc (n:ℝ) * Qpoly k (Real.log n)
        ≤ (n:ℝ) * ((Real.log n + ((k-1:ℕ):ℝ))^(k-1) / ((((k-1).factorial:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ ≤ (n:ℝ) * ((33 * (1 + Real.log (n:ℝ)))^(k-1) / ((((k-1).factorial:ℕ):ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ hfactpos.le
          exact pow_le_pow_left₀ hpowpos hsum (k-1)
      _ = (n:ℝ) * (33:ℝ)^(k-1) * (1 + Real.log (n:ℝ))^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by
          rw [mul_pow]; ring
      _ ≤ (n:ℝ) * ((100:ℝ)/3)^k * (1 + Real.log (n:ℝ))^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by
          apply div_le_div_of_nonneg_right _ hfactpos.le
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
          exact mul_le_mul_of_nonneg_left h33 (by positivity)
      _ = ((100:ℝ)/3)^k * (n:ℝ) * (1 + Real.log n)^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by ring
      _ ≤ ((5:ℝ)/3)^k + ((100:ℝ)/3)^k * (n:ℝ) * (1 + Real.log n)^(k-1) / ((((k-1).factorial:ℕ):ℝ)) :=
          le_add_of_nonneg_left h5nonneg
  · have hcaselt : Real.log (n:ℝ) < (k:ℝ)/32 := not_le.mp hcase
    have hle32 : Real.log (n:ℝ) ≤ (k:ℝ)/32 := le_of_lt hcaselt
    have hmono : Qpoly k (Real.log n) ≤ Qpoly k ((k:ℝ)/32) :=
      Qpoly_mono k ht hle32
    have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
    have hbessel := Qpoly_le_exp k ((k:ℝ)/32) (by positivity)
    have hsqrt : (2:ℝ) * Real.sqrt ((k:ℝ) * ((k:ℝ)/32)) = Real.sqrt 2 / 4 * (k:ℝ) := by
      have hkk : (k:ℝ) * ((k:ℝ)/32) = (k:ℝ)^2 / 32 := by ring
      rw [hkk, Real.sqrt_div (sq_nonneg (k:ℝ)) 32, Real.sqrt_sq hk0]
      have h16 : Real.sqrt (16:ℝ) = 4 := by
        rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
      have h32 : Real.sqrt (32:ℝ) = 4 * Real.sqrt 2 := by
        rw [show (32:ℝ) = 16 * 2 by norm_num, Real.sqrt_mul (by norm_num) 2, h16]
      rw [h32]; field_simp; rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    have hexpn : (n:ℝ) = Real.exp (Real.log (n:ℝ)) := (Real.exp_log (by positivity)).symm
    have hexp_le : (n:ℝ) ≤ Real.exp ((k:ℝ)/32) := by
      rw [hexpn]
      apply Real.exp_le_exp.mpr (le_of_lt hcaselt)
    calc (n:ℝ) * Qpoly k (Real.log n)
        ≤ (n:ℝ) * Qpoly k ((k:ℝ)/32) := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ (n:ℝ) * Real.exp (2 * Real.sqrt ((k:ℝ) * ((k:ℝ)/32))) :=
          mul_le_mul_of_nonneg_left hbessel (by positivity)
      _ = (n:ℝ) * Real.exp (Real.sqrt 2 / 4 * (k:ℝ)) := by rw [hsqrt]
      _ ≤ Real.exp ((k:ℝ)/32) * Real.exp (Real.sqrt 2 / 4 * (k:ℝ)) :=
          mul_le_mul_of_nonneg_right hexp_le (Real.exp_nonneg _)
      _ = Real.exp ((k:ℝ)/32 + Real.sqrt 2 / 4 * (k:ℝ)) := by rw [← Real.exp_add]
      _ = Real.exp (((1:ℝ)/32 + Real.sqrt 2 / 4) * (k:ℝ)) := by congr 1; ring
      _ ≤ Real.exp ((1:ℝ)/2 * (k:ℝ)) := by
          apply Real.exp_le_exp.mpr
          have := sqrt2_div_four_add
          nlinarith [hk0]
      _ = Real.exp (1/2) ^ k := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ ((5:ℝ)/3)^k := pow_le_pow_left₀ (Real.exp_nonneg _) exp_half_le k
      _ ≤ ((5:ℝ)/3)^k + ((100:ℝ)/3)^k * (n:ℝ) * (1 + Real.log n)^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by
          have : (0:ℝ) ≤ ((100:ℝ)/3)^k * (n:ℝ) * (1 + Real.log n)^(k-1) / ((((k-1).factorial:ℕ):ℝ)) := by positivity
          linarith

theorem ncard_prod_max_one_abs_le_factorial (k : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    (Nat.card {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} : ℝ) ≤
      (5 : ℝ) ^ k + (100 : ℝ) ^ k * M *
        (1 + Real.log M) ^ (k - 1) / ((k - 1).factorial : ℝ) := by
  rcases k with _ | m
  · -- k = 0
    have hsub : Subsingleton {x : Fin 0 → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have hcard : Nat.card {x : Fin 0 → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    have hM0 : (0:ℝ) ≤ M := le_trans zero_le_one hM
    calc (Nat.card {x : Fin 0 → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} : ℝ)
        ≤ 1 := by exact_mod_cast hcard
      _ ≤ (5:ℝ)^0 + (100:ℝ)^0 * M * (1+Real.log M)^((0:ℕ)-1) / (((0:ℕ)-1).factorial : ℝ) := by
          have heq : (5:ℝ)^0 + (100:ℝ)^0 * M * (1+Real.log M)^((0:ℕ)-1) / (((0:ℕ)-1).factorial : ℝ) = 1 + M := by
            norm_num
          rw [heq]; linarith
  · -- k = m+1
    have hn1 : 1 ≤ ⌊M⌋₊ := Nat.le_floor (by simpa using hM)
    have hM0 : 0 ≤ M := le_trans zero_le_one hM
    have hnM : (⌊M⌋₊ : ℝ) ≤ M := Nat.floor_le hM0
    have hlogmono : Real.log (⌊M⌋₊ : ℝ) ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast hn1) hnM
    have hbnonneg : 0 ≤ 1 + Real.log (⌊M⌋₊ : ℝ) := by
      have := Real.log_nonneg (show (1:ℝ) ≤ (⌊M⌋₊:ℝ) by exact_mod_cast hn1); linarith
    have hbase : 1 + Real.log (⌊M⌋₊ : ℝ) ≤ 1 + Real.log M := by linarith
    have hfactpos : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by positivity
    calc (Nat.card {x : Fin (m+1) → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} : ℝ)
        ≤ ((Nat.card (PosProdTuple (m+1) ⌊M⌋₊) * 3 ^ (m+1) : ℕ) : ℝ) := by
            exact_mod_cast card_int_le (m+1) M
      _ = (Nat.card (PosProdTuple (m+1) ⌊M⌋₊) : ℝ) * 3 ^ (m+1) := by push_cast; ring
      _ ≤ ((⌊M⌋₊:ℝ) * Qpoly (m+1) (Real.log ⌊M⌋₊)) * 3 ^ (m+1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact card_posProdTuple_le_Qpoly (m+1) (by omega) ⌊M⌋₊ hn1
      _ ≤ (((5:ℝ)/3)^(m+1) + ((100:ℝ)/3)^(m+1) * (⌊M⌋₊:ℝ) *
            (1+Real.log ⌊M⌋₊)^m / ((m.factorial:ℕ):ℝ)) * 3 ^ (m+1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            simpa using Qpoly_bound (m+1) (by omega) ⌊M⌋₊ hn1
      _ = (5:ℝ)^(m+1) + (100:ℝ)^(m+1) * (⌊M⌋₊:ℝ) *
            (1+Real.log ⌊M⌋₊)^m / ((m.factorial:ℕ):ℝ) := by
            have h1 : ((5:ℝ)/3)^(m+1) * 3^(m+1) = 5^(m+1) := by rw [← mul_pow]; norm_num
            have h2 : ((100:ℝ)/3)^(m+1) * 3^(m+1) = 100^(m+1) := by rw [← mul_pow]; norm_num
            rw [add_mul, h1]
            rw [show ((100:ℝ)/3)^(m+1) * (⌊M⌋₊:ℝ) * (1+Real.log ⌊M⌋₊)^m / ((m.factorial:ℕ):ℝ) * 3^(m+1)
                  = ((100:ℝ)/3)^(m+1) * 3^(m+1) * (⌊M⌋₊:ℝ) * (1+Real.log ⌊M⌋₊)^m / ((m.factorial:ℕ):ℝ) by ring]
            rw [h2]
      _ ≤ (5:ℝ)^(m+1) + (100:ℝ)^(m+1) * M * (1+Real.log M)^m / ((m.factorial:ℕ):ℝ) := by
            apply add_le_add (le_refl _)
            apply div_le_div_of_nonneg_right _ hfactpos.le
            apply mul_le_mul _ (pow_le_pow_left₀ hbnonneg hbase m) (pow_nonneg hbnonneg m) (by positivity)
            exact mul_le_mul_of_nonneg_left hnM (by positivity)

end

end Commons.NumberTheory.Counting
