import Mathlib
import Submission.Commons.NumberTheory.DirichletSeries.omega_euler_product
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.NumberTheory.EulerProduct.tsum_moebius_mul_eq_tprod_of_pow_bound
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one

namespace Commons.NumberTheory.EulerProduct

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000

/-- The majorant `n ↦ C^{ω(n)}·n^{-3/2}` is summable. -/
private lemma summable_pow_omega_mul_rpow_neg_three_halves {C : ℝ} (hC : 0 < C) :
    Summable (fun n : ℕ => (C:ℝ) ^ n.primeFactors.card * (n:ℝ) ^ (-(3/2:ℝ))) := by
  obtain ⟨A, _hApos, hA⟩ :=
    Commons.NumberTheory.DirichletSeries.pow_card_primeFactors_le_const_mul_rpow C (1/4) hC
      (by norm_num)
  have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(5/4:ℝ))) :=
    (Real.summable_nat_rpow (p := -(5/4:ℝ))).mpr (by norm_num)
  have hmaj : Summable (fun n : ℕ => A * (n:ℝ) ^ (-(5/4:ℝ))) := hbase.mul_left A
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact mul_nonneg (pow_nonneg hC.le _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero, one_mul]
      simp [Real.zero_rpow (show (-(3/2:ℝ)) ≠ 0 by norm_num),
        Real.zero_rpow (show (-(5/4:ℝ)) ≠ 0 by norm_num)]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      calc (C:ℝ) ^ n.primeFactors.card * (n:ℝ) ^ (-(3/2:ℝ))
          ≤ (A * (n:ℝ) ^ (1/4:ℝ)) * (n:ℝ) ^ (-(3/2:ℝ)) :=
            mul_le_mul_of_nonneg_right (hA n hn1) (Real.rpow_nonneg hnpos.le _)
        _ = A * ((n:ℝ) ^ (1/4:ℝ) * (n:ℝ) ^ (-(3/2:ℝ))) := by ring
        _ = A * (n:ℝ) ^ ((1/4:ℝ) + (-(3/2:ℝ))) := by rw [Real.rpow_add hnpos]
        _ = A * (n:ℝ) ^ (-(5/4:ℝ)) := by norm_num

/-- Pointwise bound: `|μ(n) f(n)| ≤ C^{ω(n)}/n²`. -/
private lemma abs_moebius_mul_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    (hbd : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ C / (p : ℝ) ^ (k + 1)) (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ) * f n| ≤ (C:ℝ) ^ n.primeFactors.card / (n:ℝ)^2 := by
  by_cases hsq : Squarefree n
  · have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 :=
      Commons.NumberTheory.Moebius.moebius_abs_le_one n
    have hstep1 : |(ArithmeticFunction.moebius n : ℝ) * f n| ≤ |f n| := by
      rw [abs_mul]
      calc |(ArithmeticFunction.moebius n : ℝ)| * |f n| ≤ 1 * |f n| :=
            mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ = |f n| := one_mul _
    refine hstep1.trans ?_
    have hprod := Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors f hmul h1 hsq
    rw [hprod, Finset.abs_prod]
    have h2 : ∏ p ∈ n.primeFactors, |f p| ≤ ∏ p ∈ n.primeFactors, C / (p:ℝ)^2 := by
      refine Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => ?_)
      simpa using hbd p 1 (Nat.prime_of_mem_primeFactors hp) le_rfl
    refine h2.trans (le_of_eq ?_)
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_pow, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
  · have hmu0 : (ArithmeticFunction.moebius n : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      norm_num
    rw [hmu0, zero_mul, abs_zero]
    exact div_nonneg (pow_nonneg hC _) (by positivity)

/-- Refined tail pointwise bound: for `n > m ≥ 1`, `|μ(n) f(n)| ≤ m^{-1/2}·C^{ω(n)}·n^{-3/2}`. -/
private lemma abs_moebius_mul_le_tail {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    (hbd : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ C / (p : ℝ) ^ (k + 1))
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    |(ArithmeticFunction.moebius n : ℝ) * f n| ≤ (Real.sqrt (m:ℝ))⁻¹ *
      ((C:ℝ) ^ n.primeFactors.card * (n:ℝ) ^ (-(3/2:ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hbase := abs_moebius_mul_le hC hmul h1 hbd n
  have h2 : (C:ℝ) ^ n.primeFactors.card / (n:ℝ)^2
      = (C:ℝ) ^ n.primeFactors.card * (n:ℝ) ^ (-(2:ℝ)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hnpos.le]
    norm_num
  rw [h2] at hbase
  refine hbase.trans ?_
  have hsplit : (n:ℝ)^(-(2:ℝ)) = (n:ℝ)^(-(3/2:ℝ)) * (n:ℝ)^(-(1/2:ℝ)) := by
    rw [← Real.rpow_add hnpos]; norm_num
  have hle : (n:ℝ)^(-(1/2:ℝ)) ≤ (Real.sqrt (m:ℝ))⁻¹ := by
    have h : (n:ℝ)^(-(1/2:ℝ)) ≤ (m:ℝ)^(-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hmpos (by exact_mod_cast (le_of_lt hmn)) (by norm_num)
    rwa [Real.rpow_neg hmpos.le, ← Real.sqrt_eq_rpow] at h
  calc (C:ℝ) ^ n.primeFactors.card * (n:ℝ)^(-(2:ℝ))
      = (C:ℝ) ^ n.primeFactors.card * ((n:ℝ)^(-(3/2:ℝ)) * (n:ℝ)^(-(1/2:ℝ))) := by
        rw [hsplit]
    _ ≤ (C:ℝ) ^ n.primeFactors.card * ((n:ℝ)^(-(3/2:ℝ)) * (Real.sqrt (m:ℝ))⁻¹) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hnpos.le _)) (pow_nonneg hC _)
    _ = (Real.sqrt (m:ℝ))⁻¹ * ((C:ℝ) ^ n.primeFactors.card * (n:ℝ)^(-(3/2:ℝ))) := by ac_rfl

theorem abs_sum_moebius_mul_sub_tprod_le_inv_sqrt {f : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    (hbd : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ C / (p : ℝ) ^ (k + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m →
      |(∑ n ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius n : ℝ) * f n)
        - ∏' p : {p : ℕ // p.Prime}, (1 - f p)| ≤ K / Real.sqrt (m : ℝ) := by
  classical
  set g : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) * f n with hgdef
  set M : ℕ → ℝ := fun n => (C:ℝ) ^ n.primeFactors.card * (n:ℝ) ^ (-(3/2:ℝ)) with hMdef
  have hMsum : Summable M := by
    rw [hMdef]; exact summable_pow_omega_mul_rpow_neg_three_halves hC
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_zero]
  have hgM : ∀ n, |g n| ≤ M n := by
    intro n
    rw [hgdef]
    show |(ArithmeticFunction.moebius n : ℝ) * f n| ≤ M n
    refine (abs_moebius_mul_le hC.le hmul h1 hbd n).trans ?_
    rw [hMdef]
    show (C:ℝ) ^ n.primeFactors.card / (n:ℝ)^2 ≤
      (C:ℝ) ^ n.primeFactors.card * (n:ℝ) ^ (-(3/2:ℝ))
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero, one_mul]
      simp [Real.zero_rpow (show (-(3/2:ℝ)) ≠ 0 by norm_num)]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have h3 : ((n:ℝ)^2)⁻¹ = (n:ℝ)^(-(2:ℝ)) := by
        rw [Real.rpow_neg hnpos.le]
        norm_num
      rw [div_eq_mul_inv, h3]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num))
        (pow_nonneg hC.le _)
  have hgsum : Summable g := Summable.of_norm_bounded hMsum (fun i => by
    rw [Real.norm_eq_abs]; exact hgM i)
  have hP : (∑' n, g n) = ∏' p : {p : ℕ // p.Prime}, (1 - f p) := by
    rw [hgdef]
    exact tsum_moebius_mul_eq_tprod_of_pow_bound hC hmul h1 hbd
  set K : ℝ := ∑' n, M n with hKdef
  have hKpos : 0 < K := by
    have hterm : M 1 = 1 := by
      rw [hMdef]
      simp [Nat.primeFactors_one]
    have hle := hMsum.sum_le_tsum ({1} : Finset ℕ) (fun i _ => by
      rw [hMdef]
      exact mul_nonneg (pow_nonneg hC.le _) (Real.rpow_nonneg (Nat.cast_nonneg i) _))
    rw [hKdef]
    calc (0:ℝ) < 1 := one_pos
      _ = M 1 := hterm.symm
      _ = ∑ i ∈ ({1} : Finset ℕ), M i := by simp
      _ ≤ ∑' n, M n := hle
  refine ⟨K, hKpos, ?_⟩
  intro m hm
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hIcc : ∑ n ∈ Finset.Icc 1 m, g n = ∑ n ∈ Finset.range (m+1), g n := by
    have hset : Finset.Icc 1 m = (Finset.range (m+1)).erase 0 := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    rw [hset]
    exact Finset.sum_erase (Finset.range (m+1)) hg0
  rw [hIcc, ← hP]
  have hsplit := hgsum.sum_add_tsum_nat_add (m+1)
  have hrepr : ∑ n ∈ Finset.range (m+1), g n - ∑' n, g n = -∑' i : ℕ, g (i + (m+1)) := by
    linarith [hsplit]
  rw [hrepr, abs_neg]
  have hMshift : Summable (fun i : ℕ => M (i + (m+1))) :=
    hMsum.comp_injective (i := fun a : ℕ => a + (m+1)) (fun a b h => Nat.add_right_cancel h)
  have hAbsG : Summable (fun i : ℕ => |g (i + (m+1))|) := by
    have h := (hgsum.comp_injective (i := fun a : ℕ => a + (m+1))
      (fun a b h => Nat.add_right_cancel h)).norm
    simpa only [Real.norm_eq_abs, Function.comp_apply] using h
  have hMaj : Summable (fun i : ℕ => (Real.sqrt (m:ℝ))⁻¹ * M (i + (m+1))) :=
    hMshift.mul_left _
  have hpt : ∀ i : ℕ, |g (i + (m+1))| ≤ (Real.sqrt (m:ℝ))⁻¹ * M (i + (m+1)) := by
    intro i
    have hlt : m < i + (m+1) := by omega
    rw [hgdef, hMdef]
    exact abs_moebius_mul_le_tail hC.le hmul h1 hbd hm hlt
  have h2 : |∑' i : ℕ, g (i + (m+1))| ≤ ∑' i : ℕ, |g (i + (m+1))| := by
    have h := norm_tsum_le_tsum_norm (f := fun i : ℕ => g (i + (m+1)))
      (by simpa only [Real.norm_eq_abs] using hAbsG)
    simpa only [Real.norm_eq_abs] using h
  refine h2.trans ?_
  have h3 : ∑' i : ℕ, |g (i + (m+1))| ≤ ∑' i : ℕ, (Real.sqrt (m:ℝ))⁻¹ * M (i + (m+1)) :=
    Summable.tsum_le_tsum hpt hAbsG hMaj
  refine h3.trans ?_
  rw [tsum_mul_left]
  have hsub : ∑' i : ℕ, M (i + (m+1)) ≤ K := by
    have hs := hMsum.sum_add_tsum_nat_add (m+1)
    have hnn : (0:ℝ) ≤ ∑ i ∈ Finset.range (m+1), M i :=
      Finset.sum_nonneg (fun i _ => by
        rw [hMdef]
        exact mul_nonneg (pow_nonneg hC.le _) (Real.rpow_nonneg (Nat.cast_nonneg i) _))
    rw [hKdef]
    linarith
  calc (Real.sqrt (m:ℝ))⁻¹ * ∑' i : ℕ, M (i + (m+1))
      ≤ (Real.sqrt (m:ℝ))⁻¹ * K :=
        mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = K / Real.sqrt (m:ℝ) := by rw [div_eq_mul_inv, mul_comm]

end Commons.NumberTheory.EulerProduct
