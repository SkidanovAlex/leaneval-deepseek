import Mathlib
import Submission.Commons.Analysis.Series.log_rpow_inv_div_tail_le
import Submission.Commons.Analysis.Series.summable_log_rpow_inv_div
import Submission.Commons.NumberTheory.Sieve.moebius_density_sum_le
import Submission.Commons.NumberTheory.Sieve.sum_mu_mul_density_mul_log_tendsto
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel

open scoped BigOperators
open Filter

namespace Commons.NumberTheory.Sieve

noncomputable section

/-! ## Abel summation: tail bound for the kernel `A d · log((d+1)/d)` -/

/-- Pointwise bound: if `|A d| ≤ K (log d)^{-6}` then
`|A d · log((d+1)/d)| ≤ K (log d)^{-6}/d`. -/
private lemma abel_kernel_pointwise {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ y : ℕ, 2 ≤ y → |A y| ≤ K * (Real.log (y:ℝ)) ^ (-6:ℝ)) :
    ∀ d : ℕ, 2 ≤ d →
      |A d * Real.log (((d:ℝ)+1)/(d:ℝ))| ≤ K * ((Real.log (d:ℝ)) ^ (-6:ℝ) / (d:ℝ)) := by
  intro d hd
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlogd : 0 < Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hlr_nn : 0 ≤ Real.log (((d:ℝ)+1)/(d:ℝ)) := by
    apply Real.log_nonneg
    rw [one_le_div hd0]; linarith
  have hlr_le : Real.log (((d:ℝ)+1)/(d:ℝ)) ≤ 1/(d:ℝ) := by
    have hpos : 0 < ((d:ℝ)+1)/(d:ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have heq : ((d:ℝ)+1)/(d:ℝ) - 1 = 1/(d:ℝ) := by
      rw [div_sub_one hd0.ne']; ring
    linarith [h, heq ▸ h]
  have hAd := hA d hd
  have hlogneg : 0 ≤ (Real.log (d:ℝ)) ^ (-6:ℝ) := Real.rpow_nonneg hlogd.le _
  rw [abs_mul, abs_of_nonneg hlr_nn]
  calc |A d| * Real.log (((d:ℝ)+1)/(d:ℝ))
      ≤ (K * (Real.log (d:ℝ)) ^ (-6:ℝ)) * Real.log (((d:ℝ)+1)/(d:ℝ)) :=
        mul_le_mul_of_nonneg_right hAd hlr_nn
    _ ≤ (K * (Real.log (d:ℝ)) ^ (-6:ℝ)) * (1/(d:ℝ)) :=
        mul_le_mul_of_nonneg_left hlr_le (mul_nonneg hK hlogneg)
    _ = K * ((Real.log (d:ℝ)) ^ (-6:ℝ) / (d:ℝ)) := by ring

/-- **Abel tail bound.**  If the partial sums `A d` decay like `K (log d)^{-6}`, then
`∑_{d ≥ N} A d · log((d+1)/d)` is `O(K (log N)^{-5})`. -/
theorem abel_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℕ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ y : ℕ, 2 ≤ y → |A y| ≤ K * (Real.log (y:ℝ)) ^ (-6:ℝ)) →
      Summable (fun d : ℕ => A d * Real.log (((d:ℝ)+1)/(d:ℝ))) ∧
      ∀ N : ℕ, 2 ≤ N →
        |∑' i : ℕ, A (i + N) * Real.log (((((i+N:ℕ):ℝ)+1))/(((i+N:ℕ):ℝ)))| ≤ C * K * (Real.log (N:ℝ)) ^ (-5:ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.Analysis.Series.log_rpow_inv_div_tail_le 6 (by norm_num)
  refine ⟨C0, hC0pos, ?_⟩
  intro A K hK hA
  have hpoint := abel_kernel_pointwise hK hA
  -- summability
  have hbase : Summable (fun d : ℕ => K * ((Real.log (d:ℝ)) ^ (-6:ℝ) / (d:ℝ))) :=
    (Commons.Analysis.Series.summable_log_rpow_inv_div 6 (by norm_num)).mul_left K
  have hsumm : Summable (fun d : ℕ => A d * Real.log (((d:ℝ)+1)/(d:ℝ))) := by
    refine Summable.of_norm_bounded_eventually hbase ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 2] with d hd
    rw [Real.norm_eq_abs]
    exact hpoint d hd
  refine ⟨hsumm, ?_⟩
  intro N hN
  have hsumm_shift : Summable (fun i : ℕ =>
      A (i + N) * Real.log (((((i+N:ℕ):ℝ)+1))/(((i+N:ℕ):ℝ)))) :=
    (summable_nat_add_iff N).mpr hsumm
  have hmaj : Summable (fun i : ℕ =>
      K * ((Real.log (((i+N:ℕ):ℝ))) ^ (-6:ℝ) / (((i+N:ℕ):ℝ)))) :=
    ((summable_nat_add_iff N).mpr
      (Commons.Analysis.Series.summable_log_rpow_inv_div 6 (by norm_num))).mul_left K
  have hcmp : (∑' i : ℕ, ‖A (i + N) * Real.log (((((i+N:ℕ):ℝ)+1))/(((i+N:ℕ):ℝ)))‖)
      ≤ ∑' i : ℕ, K * ((Real.log (((i+N:ℕ):ℝ))) ^ (-6:ℝ) / (((i+N:ℕ):ℝ))) := by
    refine Summable.tsum_le_tsum (fun i => ?_) hsumm_shift.norm hmaj
    rw [Real.norm_eq_abs]
    exact hpoint (i+N) (by omega)
  have htail : (∑' i : ℕ, (Real.log (((i+N:ℕ):ℝ))) ^ (-6:ℝ) / (((i+N:ℕ):ℝ)))
      ≤ C0 * (Real.log (N:ℝ)) ^ (-5:ℝ) := by
    have hreindex : (∑' i : ℕ, (Real.log (((i+N:ℕ):ℝ))) ^ (-6:ℝ) / (((i+N:ℕ):ℝ)))
        = ∑' k : ℕ, (Real.log (((N+k:ℕ):ℝ))) ^ (-6:ℝ) / (((N+k:ℕ):ℝ)) := by
      apply tsum_congr; intro i; rw [Nat.add_comm]
    rw [hreindex]
    have h := hC0 N hN
    have hexp : (Real.log (N:ℝ)) ^ (1 - (6:ℝ)) = (Real.log (N:ℝ)) ^ (-5:ℝ) := by norm_num
    rwa [hexp] at h
  calc |∑' i : ℕ, A (i + N) * Real.log (((((i+N:ℕ):ℝ)+1))/(((i+N:ℕ):ℝ)))|
      = ‖∑' i : ℕ, A (i + N) * Real.log (((((i+N:ℕ):ℝ)+1))/(((i+N:ℕ):ℝ)))‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∑' i : ℕ, ‖A (i + N) * Real.log (((((i+N:ℕ):ℝ)+1))/(((i+N:ℕ):ℝ)))‖ :=
        norm_tsum_le_tsum_norm hsumm_shift.norm
    _ ≤ ∑' i : ℕ, K * ((Real.log (((i+N:ℕ):ℝ))) ^ (-6:ℝ) / (((i+N:ℕ):ℝ))) := hcmp
    _ = K * (∑' i : ℕ, (Real.log (((i+N:ℕ):ℝ))) ^ (-6:ℝ) / (((i+N:ℕ):ℝ))) := tsum_mul_left
    _ ≤ K * (C0 * (Real.log (N:ℝ)) ^ (-5:ℝ)) :=
        mul_le_mul_of_nonneg_left htail hK
    _ = C0 * K * (Real.log (N:ℝ)) ^ (-5:ℝ) := by ring

/-- **Abel rate lemma.**  If the partial sums of a sequence `a` decay like `K (log y)^{-6}`,
then `∑_{d ≤ N} a d · log d` converges, with the explicit rate `O(K (log N)^{-5})` and
limit `−∑_d A d · log((d+1)/d)` where `A d = ∑_{e ≤ d} a e`. -/
theorem sum_mul_log_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ y : ℕ, 2 ≤ y → |∑ d ∈ Finset.Icc 1 y, a d| ≤ K * (Real.log (y:ℝ)) ^ (-6:ℝ)) →
      ∃ F : ℝ, F = ∑' d : ℕ, (∑ e ∈ Finset.Icc 1 d, a e) * Real.log (((d:ℝ)+1)/(d:ℝ)) ∧
        ∀ N : ℕ, 2 ≤ N →
          |(∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) + F| ≤ C * K * (Real.log (N:ℝ)) ^ (-5:ℝ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := abel_tail_bound
  refine ⟨1 + C1, by linarith, ?_⟩
  intro a K hK hA
  set B : ℕ → ℝ := fun d => (∑ e ∈ Finset.Icc 1 d, a e) * Real.log (((d:ℝ)+1)/(d:ℝ)) with hB
  have hsum : Summable B := hC1 (fun d => ∑ e ∈ Finset.Icc 1 d, a e) K hK hA |>.1
  refine ⟨∑' d, B d, rfl, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hB0 : B 0 = 0 := by simp [hB]
  have hrange : (∑ i ∈ Finset.range N, B i) = ∑ d ∈ Finset.Icc 1 (N-1), B d := by
    have hins : Finset.range N = insert 0 (Finset.Icc 1 (N-1)) := by
      ext d; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc]), hB0, zero_add]
  have hF : (∑' d, B d) = (∑ d ∈ Finset.Icc 1 (N-1), B d) + ∑' i : ℕ, B (i+N) := by
    rw [← hsum.sum_add_tsum_nat_add N, hrange]
  have habel := Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel a N
  have key : (∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) + (∑' d, B d)
      = (∑ d ∈ Finset.Icc 1 N, a d) * Real.log (N:ℝ) + ∑' i : ℕ, B (i+N) := by
    rw [habel, hF]; ring
  have hAN : |(∑ d ∈ Finset.Icc 1 N, a d) * Real.log (N:ℝ)| ≤ K * (Real.log (N:ℝ)) ^ (-5:ℝ) := by
    have h1 : 0 ≤ Real.log (N:ℝ) := hlogN.le
    rw [abs_mul, abs_of_nonneg h1]
    have h2 := hA N hN
    have hkey2 : (Real.log (N:ℝ)) ^ (-6:ℝ) * Real.log (N:ℝ) = (Real.log (N:ℝ)) ^ (-5:ℝ) := by
      rw [show (-6:ℝ) = -5 + (-1) by norm_num, Real.rpow_add hlogN, Real.rpow_neg_one,
        mul_assoc, inv_mul_cancel₀ (ne_of_gt hlogN), mul_one]
    calc |∑ d ∈ Finset.Icc 1 N, a d| * Real.log (N:ℝ)
        ≤ (K * (Real.log (N:ℝ)) ^ (-6:ℝ)) * Real.log (N:ℝ) :=
          mul_le_mul_of_nonneg_right h2 h1
      _ = K * (Real.log (N:ℝ)) ^ (-5:ℝ) := by rw [mul_assoc, hkey2]
  have htailN : |∑' i : ℕ, B (i+N)| ≤ C1 * K * (Real.log (N:ℝ)) ^ (-5:ℝ) :=
    (hC1 (fun d => ∑ e ∈ Finset.Icc 1 d, a e) K hK hA).2 N hN
  calc |(∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) + (∑' d, B d)|
      = |(∑ d ∈ Finset.Icc 1 N, a d) * Real.log (N:ℝ) + ∑' i : ℕ, B (i+N)| := by rw [key]
    _ ≤ |(∑ d ∈ Finset.Icc 1 N, a d) * Real.log (N:ℝ)| + |∑' i : ℕ, B (i+N)| := abs_add_le _ _
    _ ≤ K * (Real.log (N:ℝ)) ^ (-5:ℝ) + C1 * K * (Real.log (N:ℝ)) ^ (-5:ℝ) :=
        add_le_add hAN htailN
    _ = (1 + C1) * K * (Real.log (N:ℝ)) ^ (-5:ℝ) := by ring

/-- The Friedlander–Iwaniec prime-sum asymptotic `(2.7)` is preserved when the density is
modified by setting `g p = 0` on the primes dividing a squarefree integer `ν`. -/
private lemma h9_coprime_restrict {g : ℕ → ℝ} (hg0 : ∀ p : ℕ, Nat.Prime p → 0 ≤ g p)
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ)))
    {ν : ℕ} (hν : Squarefree ν) :
    ∃ c' C' : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (if Nat.Coprime p ν then g p else 0))
        - Real.log (Real.log y) - c'| ≤ C' * (Real.log y) ^ (-(10 : ℤ)) := by
  obtain ⟨c, C, h9c⟩ := h9
  have hconv : ∀ t : ℝ, t ^ (-(10:ℤ)) = t ^ (-10:ℝ) := by
    intro t; rw [← Real.rpow_intCast]; norm_num
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `C ≥ 0` is forced since the left side is nonnegative.
  have hCnn : 0 ≤ C := by
    have h := h9c 2 (by norm_num)
    rw [hconv] at h
    have hlog2 : (0:ℝ) < (Real.log 2) ^ (-10:ℝ) := Real.rpow_pos_of_pos hlog2pos _
    have hnn := abs_nonneg ((∑ p ∈ (Finset.Icc 2 ⌊(2:ℝ)⌋₊).filter Nat.Prime, g p)
      - Real.log (Real.log 2) - c)
    nlinarith [h, hlog2, hnn]
  have hνne : ν ≠ 0 := hν.ne_zero
  set cn : ℝ := ∑ p ∈ ν.primeFactors, g p with hcndef
  have hcn0 : 0 ≤ cn :=
    Finset.sum_nonneg (fun p hp => hg0 p (Nat.prime_of_mem_primeFactors hp))
  refine ⟨c - cn, max C ((C * (Real.log 2) ^ (-10:ℝ) + cn) * (Real.log ν) ^ (10:ℝ)), ?_⟩
  intro y hy
  have hy2 : (2:ℝ) ≤ y := hy
  have hypos : 0 < y := by linarith
  have hfloor2 : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy2)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogy_nn : 0 ≤ (Real.log y) ^ (-10:ℝ) := Real.rpow_nonneg hlogy.le _
  rw [hconv (Real.log y)]
  set Dd : ℝ := ∑ p ∈ (ν.primeFactors).filter (fun p => p ≤ ⌊y⌋₊), g p with hDddef
  -- The two index sets agree.
  have hset : ((Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime).filter (fun p => p ∣ ν)
      = (ν.primeFactors).filter (fun p => p ≤ ⌊y⌋₊) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨⟨h2, hle⟩, hpp⟩, hdvd⟩
      exact ⟨⟨hpp, hdvd, hνne⟩, hle⟩
    · rintro ⟨⟨hpp, hdvd, _⟩, hle⟩
      exact ⟨⟨⟨hpp.two_le, hle⟩, hpp⟩, hdvd⟩
  have hSl : (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (if Nat.Coprime p ν then g p else 0))
      = (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Dd := by
    have hDd_eq : Dd
        = ∑ p ∈ ((Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime).filter (fun p => p ∣ ν), g p := by
      rw [hDddef, hset]
    rw [hDd_eq]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hpp : Nat.Prime p
    · have hcp := hpp.coprime_iff_not_dvd (n := ν)
      by_cases hd : p ∣ ν
      · have hnc : ¬ Nat.Coprime p ν := by rw [hcp]; exact fun hh => hh hd
        rw [if_pos hpp, if_neg hnc, if_pos hpp, if_pos hpp, if_pos hd]
        ring
      · have hc : Nat.Coprime p ν := by rw [hcp]; exact hd
        rw [if_pos hpp, if_pos hc, if_pos hpp, if_pos hpp, if_neg hd]
        ring
    · rw [if_neg hpp, if_neg hpp, if_neg hpp]; ring
  have hDd0 : 0 ≤ Dd := by
    rw [hDddef]
    exact Finset.sum_nonneg (fun p hp =>
      hg0 p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
  have hDle : Dd ≤ cn := by
    rw [hDddef, hcndef]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro p hp _
    exact hg0 p (Nat.prime_of_mem_primeFactors hp)
  have hDcn : ν ≤ ⌊y⌋₊ → Dd = cn := by
    intro hle
    rw [hDddef, hcndef]
    rw [Finset.filter_true_of_mem]
    intro p hp
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hνne)
      (Nat.dvd_of_mem_primeFactors hp)) hle
  have hmain : |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime,
          (if Nat.Coprime p ν then g p else 0)) - Real.log (Real.log y) - (c - cn)|
      ≤ C * (Real.log y) ^ (-10:ℝ) + (cn - Dd) := by
    have heq : (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (if Nat.Coprime p ν then g p else 0))
          - Real.log (Real.log y) - (c - cn)
        = ((∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c)
          + (cn - Dd) := by
      rw [hSl]; ring
    rw [heq]
    refine le_trans (abs_add_le _ _) ?_
    have h1 := h9c y hy
    rw [hconv] at h1
    have h2 : |cn - Dd| = cn - Dd := abs_of_nonneg (by linarith)
    rw [h2]
    exact add_le_add h1 le_rfl
  refine le_trans hmain ?_
  set T : ℝ := (C * (Real.log 2) ^ (-10:ℝ) + cn) * (Real.log ν) ^ (10:ℝ) with hTdef
  by_cases hcase : ν ≤ ⌊y⌋₊
  · have hD : Dd = cn := hDcn hcase
    rw [hD, sub_self, add_zero]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlogy_nn
  · have hcase' : ⌊y⌋₊ < ν := Nat.lt_of_not_le hcase
    have hyν : y < (ν:ℝ) := (Nat.floor_lt hypos.le).mp hcase'
    have hν1 : (1:ℝ) < (ν:ℝ) := by
      have h3 : 3 ≤ ν := by omega
      exact_mod_cast (show 1 < ν by omega)
    have hlogν : 0 < Real.log ν := Real.log_pos hν1
    have hstep1 : C * (Real.log y) ^ (-10:ℝ) ≤ C * (Real.log 2) ^ (-10:ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hlog2pos (Real.log_le_log (by norm_num) hy2)
          (by norm_num)) hCnn
    have hstep2 : (Real.log ν) ^ (-10:ℝ) ≤ (Real.log y) ^ (-10:ℝ) :=
      Real.rpow_le_rpow_of_nonpos hlogy (Real.log_le_log hypos hyν.le) (by norm_num)
    have hkey : (Real.log ν) ^ (10:ℝ) * (Real.log ν) ^ (-10:ℝ) = 1 := by
      rw [← Real.rpow_add hlogν]; norm_num
    have hA0 : 0 ≤ C * (Real.log 2) ^ (-10:ℝ) + cn := by
      have := Real.rpow_pos_of_pos hlog2pos (-10:ℝ)
      nlinarith
    have hb : (1:ℝ) ≤ (Real.log ν) ^ (10:ℝ) * (Real.log y) ^ (-10:ℝ) := by
      calc (1:ℝ) = (Real.log ν) ^ (10:ℝ) * (Real.log ν) ^ (-10:ℝ) := hkey.symm
        _ ≤ (Real.log ν) ^ (10:ℝ) * (Real.log y) ^ (-10:ℝ) :=
            mul_le_mul_of_nonneg_left hstep2 (Real.rpow_nonneg hlogν.le _)
    have hTexp : T * (Real.log y) ^ (-10:ℝ)
        = (C * (Real.log 2) ^ (-10:ℝ) + cn)
          * ((Real.log ν) ^ (10:ℝ) * (Real.log y) ^ (-10:ℝ)) := by rw [hTdef]; ring
    have hge : C * (Real.log 2) ^ (-10:ℝ) + cn ≤ max C T * (Real.log y) ^ (-10:ℝ) := by
      have h1 : T * (Real.log y) ^ (-10:ℝ) ≤ max C T * (Real.log y) ^ (-10:ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlogy_nn
      have h2 : C * (Real.log 2) ^ (-10:ℝ) + cn ≤ T * (Real.log y) ^ (-10:ℝ) := by
        rw [hTexp]
        calc C * (Real.log 2) ^ (-10:ℝ) + cn
            = (C * (Real.log 2) ^ (-10:ℝ) + cn) * 1 := (mul_one _).symm
          _ ≤ (C * (Real.log 2) ^ (-10:ℝ) + cn)
                * ((Real.log ν) ^ (10:ℝ) * (Real.log y) ^ (-10:ℝ)) :=
              mul_le_mul_of_nonneg_left hb hA0
      exact le_trans h2 h1
    calc C * (Real.log y) ^ (-10:ℝ) + (cn - Dd)
        ≤ C * (Real.log y) ^ (-10:ℝ) + cn := by linarith [hDd0]
      _ ≤ C * (Real.log 2) ^ (-10:ℝ) + cn := by linarith
      _ ≤ max C T * (Real.log y) ^ (-10:ℝ) := hge

/-- For a squarefree `ν`, the Möbius-weighted `log`-sum restricted to integers coprime to `ν`
converges to `−Hν` with `Hν > 0`.  This is the positivity input for the rate estimate: it is
obtained by applying the general density theorem to the density `n ↦ g n` if `(n, ν) = 1`
and `0` otherwise. -/
theorem coprime_sum_pos_limit {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ)))
    {ν : ℕ} (hν : Squarefree ν) :
    ∃ Hν : ℝ, 0 < Hν ∧
      Filter.Tendsto (fun N : ℕ =>
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
            (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-Hν)) := by
  set gν : ℕ → ℝ := fun n => if Nat.Coprime n ν then g n else 0 with hgνdef
  have hgνmul : ∀ m n : ℕ, Nat.Coprime m n → gν (m * n) = gν m * gν n := by
    intro m n hmn
    by_cases hc : Nat.Coprime (m * n) ν
    · have hm : Nat.Coprime m ν := Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_right m n) hc
      have hn : Nat.Coprime n ν := Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_left n m) hc
      simp only [hgνdef, if_pos hc, if_pos hm, if_pos hn]
      exact hmul m n hmn
    · have hkey : ¬ (Nat.Coprime m ν ∧ Nat.Coprime n ν) := by
        rintro ⟨hm, hn⟩
        exact hc (Nat.Coprime.mul_left hm hn)
      simp only [hgνdef, if_neg hc]
      rcases not_and_or.mp hkey with hm | hn
      · rw [if_neg hm]; ring
      · rw [if_neg hn]; ring
  have hgν1 : gν 1 = 1 := by
    simp only [hgνdef]
    rw [if_pos (Nat.coprime_one_left ν), hg1]
  have hgνp : ∀ p : ℕ, p.Prime → 0 ≤ gν p ∧ gν p < 1 := by
    intro p hpp
    simp only [hgνdef]
    by_cases hc : Nat.Coprime p ν
    · simp only [if_pos hc]; exact hp p hpp
    · simp only [if_neg hc]; exact ⟨le_refl 0, zero_lt_one⟩
  have hgνbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → gν p ≤ C / (p : ℝ) := by
    obtain ⟨C, hC⟩ := hbound
    refine ⟨max C 1, fun p hpp => ?_⟩
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    by_cases hc : Nat.Coprime p ν
    · simp only [hgνdef, if_pos hc]
      calc g p ≤ C / (p:ℝ) := hC p hpp
        _ ≤ max C 1 / (p:ℝ) := div_le_div_of_nonneg_right (le_max_left _ _) hp0.le
    · simp only [hgνdef, if_neg hc]
      exact div_nonneg (le_trans zero_le_one (le_max_right C 1)) hp0.le
  have hgν9 := h9_coprime_restrict (fun p hpp => (hp p hpp).1) h9 hν
  obtain ⟨Hν, hHνpos, hHνlim, _⟩ :=
    sum_mu_mul_density_mul_log_tendsto hgνmul hgν1 hgνp hgνbound hgν9
  refine ⟨Hν, hHνpos, ?_⟩
  refine hHνlim.congr (fun N => ?_)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  simp only [hgνdef]
  by_cases hd : Nat.Coprime d ν
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd]; ring

/-- **The coprimality-restricted rate of convergence of `∑ μ(d) g(d) log d`.**

For a multiplicative density `g` with `0 ≤ g(p) < 1`, `g(p) ≪ 1/p` and the
Friedlander–Iwaniec prime-sum asymptotic `(2.7)`, the full Möbius–`log` sum converges to a
negative constant `−H` with `H > 0`, and for every squarefree `ν` the sum restricted to
`(d, ν) = 1` converges to `−Hν` with `Hν > 0`, at the rate
`|∑_{d ≤ N, (d,ν)=1} μ(d) g(d) log d + Hν| ≤ C β_ν (log N)^{-5}`,
where `β_ν = ∏_{p ∣ ν} (1 + p^{-1/2})`. -/
theorem sum_mu_g_log_coprime_rate {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-H)) ∧
      ∀ ν : ℕ, Squarefree ν → ∃ Hν : ℝ, 0 < Hν ∧
        Filter.Tendsto (fun N : ℕ =>
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
              (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-Hν)) ∧
        ∀ N : ℕ, 2 ≤ N →
          |(∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
              (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) + Hν|
            ≤ C * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
                * (Real.log (N : ℝ)) ^ (-(5 : ℤ)) := by
  obtain ⟨H, hHpos, hHlim, _⟩ :=
    sum_mu_mul_density_mul_log_tendsto hmul hg1 hp hbound h9
  obtain ⟨C0, hC0pos, hC0⟩ := moebius_density_sum_le hmul hg1 hp hbound h9
  obtain ⟨Cr, hCrpos, hCr⟩ := sum_mul_log_rate
  have hconv5 : ∀ t : ℝ, t ^ (-(5:ℤ)) = t ^ (-5:ℝ) := by
    intro t; rw [← Real.rpow_intCast]; norm_num
  have hconv6 : ∀ t : ℝ, t ^ (-(6:ℤ)) = t ^ (-6:ℝ) := by
    intro t; rw [← Real.rpow_intCast]; norm_num
  refine ⟨Cr * C0, H, mul_pos hCrpos hC0pos, hHpos, hHlim, ?_⟩
  intro ν hν
  obtain ⟨Hν, hHνpos, hHνlim⟩ := coprime_sum_pos_limit hmul hg1 hp hbound h9 hν
  have hνne : ν ≠ 0 := hν.ne_zero
  have hν1 : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr hνne
  set β : ℝ := ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) with hβ
  have hβpos : 0 < β := by
    rw [hβ]
    exact Finset.prod_pos (fun p _ => by positivity)
  set a : ℕ → ℝ := fun d => if Nat.Coprime d ν then (ArithmeticFunction.moebius d : ℝ) * g d else 0
    with ha
  have hA : ∀ y : ℕ, 2 ≤ y → |∑ d ∈ Finset.Icc 1 y, a d| ≤ (C0 * β) * (Real.log (y:ℝ)) ^ (-6:ℝ) := by
    intro y hy
    have hb := hC0 ν y hν1 hy
    have heq : (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Nat.Coprime d ν),
          (ArithmeticFunction.moebius d : ℝ) * g d) = ∑ d ∈ Finset.Icc 1 y, a d := by
      simp only [Finset.sum_filter, ha]
    rw [heq, ← hβ, hconv6 (Real.log (y:ℝ))] at hb
    exact hb
  obtain ⟨F, hFdef, hFb⟩ := hCr a (C0 * β) (mul_nonneg hC0pos.le hβpos.le) hA
  have hS : ∀ N : ℕ, (∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
        (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d)
      = ∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ) := by
    intro N
    simp only [Finset.sum_filter, ha]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : Nat.Coprime d ν
    · rw [if_pos hd, if_pos hd]
    · rw [if_neg hd, if_neg hd]; ring
  have hboundS : ∀ N : ℕ, 2 ≤ N →
      |(∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) + F| ≤ Cr * (C0 * β) * (Real.log (N:ℝ)) ^ (-5:ℝ) :=
    fun N hN => hFb N hN
  have hmaj : Filter.Tendsto (fun N : ℕ => Cr * (C0 * β) * (Real.log (N:ℝ)) ^ (-5:ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (Real.log (N:ℝ)) ^ (-5:ℝ)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using h1.const_mul (Cr * (C0 * β))
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      ‖(∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) - (-F)‖
        ≤ Cr * (C0 * β) * (Real.log (N:ℝ)) ^ (-5:ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs, show (∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) - (-F)
        = (∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) + F by ring]
    exact hboundS N hN
  have hSlim : Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ))
      Filter.atTop (nhds (-F)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall (fun N => norm_nonneg _)) hev hmaj)
  have hFlim : Filter.Tendsto (fun N : ℕ =>
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-F)) :=
    hSlim.congr (fun N => (hS N).symm)
  have hFH : F = Hν := by
    have h1 : -F = -Hν := tendsto_nhds_unique hFlim hHνlim
    linarith
  refine ⟨F, by rw [hFH]; exact hHνpos, hFlim, ?_⟩
  intro N hN
  rw [hS N, hconv5 (Real.log (N:ℝ))]
  calc |(∑ d ∈ Finset.Icc 1 N, a d * Real.log (d:ℝ)) + F|
      ≤ Cr * (C0 * β) * (Real.log (N:ℝ)) ^ (-5:ℝ) := hboundS N hN
    _ = Cr * C0 * β * (Real.log (N:ℝ)) ^ (-5:ℝ) := by ring

end

end Commons.NumberTheory.Sieve
