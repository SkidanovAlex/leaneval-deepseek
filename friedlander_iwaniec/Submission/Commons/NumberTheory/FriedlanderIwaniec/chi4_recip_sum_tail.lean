import Mathlib
import Submission.Commons.Analysis.Asymptotics.abel_tail_bound_finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset Filter

namespace Commons.NumberTheory.FriedlanderIwaniec

noncomputable section

private def chi (n : ℕ) : ℤ := ZMod.χ₄ (n : ZMod 4)
private def P (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, chi n
private def rterm (n : ℕ) : ℝ := ((chi n : ℤ) : ℝ) * (n : ℝ)⁻¹
private def rsum (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), rterm n
private def cterm (n : ℕ) : ℂ := ((chi n : ℤ) : ℂ) * (n : ℂ)⁻¹
private def csum (N : ℕ) : ℂ := ∑ n ∈ Finset.range (N + 1), cterm n

private lemma chi_block (m : ℕ) : chi m + chi (m + 1) + chi (m + 2) + chi (m + 3) = 0 := by
  have hb : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  obtain ⟨r, hr, hm⟩ : ∃ r : ℕ, r < 4 ∧ m % 4 = r := ⟨m % 4, hb, rfl⟩
  interval_cases r <;> {
    rw [chi, chi, chi, chi]
    rw [ZMod.χ₄_nat_mod_four m, ZMod.χ₄_nat_mod_four (m + 1),
        ZMod.χ₄_nat_mod_four (m + 2), ZMod.χ₄_nat_mod_four (m + 3)]
    simp_all [Nat.add_mod]
  }

private lemma sum_four (m : ℕ) : (∑ i ∈ Finset.range 4, chi (m + i)) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero]
  simpa using chi_block m

private lemma P_period (k : ℕ) : P (k + 4) = P k := by
  unfold P
  rw [Finset.sum_range_add, sum_four]
  ring

private lemma P_val (N : ℕ) : P N = 0 ∨ P N = 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N < 4
    · interval_cases N <;> decide
    · have hN4 : N - 4 + 4 = N := by omega
      have hp : P N = P (N - 4) := by rw [← hN4]; exact P_period (N - 4)
      rw [hp]
      exact ih (N - 4) (by omega)

private lemma contig_bound (x y : ℕ) (h : x ≤ y) :
    ‖∑ n ∈ Finset.Icc x y, ((chi n : ℤ) : ℂ)‖ ≤ 1 := by
  have hIcc : Finset.Ico x (y + 1) = Finset.Icc x y := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hsum : ∑ n ∈ Finset.Icc x y, chi n = P (y + 1) - P x := by
    rw [← hIcc]
    exact Finset.sum_Ico_eq_sub chi (by omega)
  have hcast : ∑ n ∈ Finset.Icc x y, ((chi n : ℤ) : ℂ)
      = ((∑ n ∈ Finset.Icc x y, chi n : ℤ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, hsum]
  rcases P_val (y + 1) with h1 | h1 <;> rcases P_val x with h2 | h2 <;> simp [h1, h2]

private lemma cterm_ofReal (n : ℕ) : cterm n = ((rterm n : ℝ) : ℂ) := by
  simp only [cterm, rterm, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_intCast,
    Complex.ofReal_natCast]

private lemma csum_eq_ofReal (N : ℕ) : csum N = ((rsum N : ℝ) : ℂ) := by
  simp only [csum, rsum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun n _ => cterm_ofReal n)

private lemma tail_bound (N M : ℕ) (hNM : N + 1 ≤ M) :
    ‖csum M - csum N‖ ≤ 2 / ((N : ℝ) + 1) := by
  have hIco : Finset.Ico (N + 1) (M + 1) = Finset.Icc (N + 1) M := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hsplit : csum M - csum N = ∑ k ∈ Finset.Ico (N + 1) (M + 1), cterm k := by
    unfold csum
    exact (Finset.sum_Ico_eq_sub cterm (by omega)).symm
  rw [hsplit, hIco]
  have hb := Commons.Analysis.Asymptotics.abel_tail_bound_finite
      (a := fun n => ((chi n : ℤ) : ℂ)) (B := 1)
      (fun x y hxy => contig_bound x y hxy) (1 : ℂ) (by norm_num)
      (N := N + 1) (M := M) hNM (by omega)
  have hcongr : ∑ k ∈ Finset.Icc (N + 1) M, cterm k
      = ∑ k ∈ Finset.Icc (N + 1) M, ((chi k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 : ℂ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold cterm
    rw [Complex.cpow_neg, Complex.cpow_one]
  rw [hcongr]
  refine le_trans hb (le_of_eq ?_)
  have hre : Complex.re (1 : ℂ) = 1 := by norm_num
  rw [hre, Real.rpow_neg_one]
  simp only [norm_one, one_div]
  push_cast
  field_simp
  ring

private lemma dist_rsum_le (n m : ℕ) (h : n + 1 ≤ m) :
    dist (rsum n) (rsum m) ≤ 2 / ((n : ℝ) + 1) := by
  have hb := tail_bound n m h
  rw [Real.dist_eq]
  have hkey : ‖csum m - csum n‖ = |rsum n - rsum m| := by
    rw [norm_sub_rev, csum_eq_ofReal, csum_eq_ofReal, ← Complex.ofReal_sub]
    exact RCLike.norm_ofReal _
  rw [← hkey]
  exact hb

private lemma tendsto_bound : Tendsto (fun N : ℕ => 2 / ((N : ℝ) + 1)) atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  simpa [mul_div_assoc, div_eq_mul_inv] using h

private lemma rsum_cauchy : CauchySeq rsum := by
  refine cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 2 / ((N : ℝ) + 1))
    (fun n m N hn hm => ?_) tendsto_bound
  rcases le_total n m with hnm | hmn
  · rcases eq_or_lt_of_le hnm with h' | h'
    · subst h'; rw [dist_self]; positivity
    · have hb := dist_rsum_le n m (by omega)
      have hle : 2 / ((n : ℝ) + 1) ≤ 2 / ((N : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact_mod_cast (by omega : N + 1 ≤ n + 1)
      linarith
  · rcases eq_or_lt_of_le hmn with h' | h'
    · subst h'; rw [dist_self]; positivity
    · have hb := dist_rsum_le m n (by omega)
      rw [dist_comm] at hb
      have hle : 2 / ((m : ℝ) + 1) ≤ 2 / ((N : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact_mod_cast (by omega : N + 1 ≤ m + 1)
      linarith

private lemma rsum_three : rsum 3 = 2 / 3 := by
  simp only [rsum, rterm, chi, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [ZMod.χ₄]

private lemma sum_eq_rsum (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (((ZMod.χ₄ (n : ZMod 4) : ℤ)) : ℝ) / n) = rsum N := by
  simp only [rsum, rterm, chi, div_eq_mul_inv]

theorem chi4_recip_sum_tail :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ,
      |(∑ n ∈ Finset.range (N + 1), (((ZMod.χ₄ (n : ZMod 4) : ℤ)) : ℝ) / n) - c| ≤ 4 / (N + 1) := by
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete rsum_cauchy
  have htail : ∀ N : ℕ, |rsum N - c| ≤ 2 / ((N : ℝ) + 1) := by
    intro N
    have hev : ∀ᶠ M in atTop, |rsum M - rsum N| ≤ 2 / ((N : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop (N + 1)] with M hM
      rw [abs_sub_comm]
      exact dist_rsum_le N M hM
    have htend : Tendsto (fun M => |rsum M - rsum N|) atTop (nhds |c - rsum N|) :=
      (hc.sub_const (rsum N)).abs
    have := le_of_tendsto htend hev
    rwa [abs_sub_comm] at this
  have hcpos : 0 < c := by
    have hle := (abs_le.mp (htail 3)).2
    rw [rsum_three] at hle
    norm_num at hle
    linarith
  refine ⟨c, hcpos, fun N => ?_⟩
  rw [sum_eq_rsum N]
  have h2 := htail N
  have h3 : 2 / ((N : ℝ) + 1) ≤ 4 / ((N : ℝ) + 1) := by
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have : |rsum N - c| ≤ 4 / ((N : ℝ) + 1) := by linarith
  simpa only [Nat.cast_add, Nat.cast_one] using this

end

end Commons.NumberTheory.FriedlanderIwaniec
