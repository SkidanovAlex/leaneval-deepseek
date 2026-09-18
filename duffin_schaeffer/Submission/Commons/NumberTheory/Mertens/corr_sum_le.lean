import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.Real.log_le_half_sub_inv
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- For `n ≥ 2`, the correction term `log(n/(n-1)) - 1/n` is at most `1/(2 n (n-1))`.
This follows from `log u ≤ (u - u⁻¹)/2` for `u = n/(n-1) ≥ 1`. -/
private lemma corrTerm_le_half_inv {n : ℕ} (hn : 2 ≤ n) :
    corrTerm n ≤ 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hu : 1 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hnm1]; linarith
  have hlog := Commons.Analysis.Real.log_le_half_sub_inv hu
  have hinv : ((n : ℝ) / ((n : ℝ) - 1))⁻¹ = ((n : ℝ) - 1) / (n : ℝ) := by
    rw [inv_div]
  have hval : ((n : ℝ) / ((n : ℝ) - 1) - ((n : ℝ) - 1) / (n : ℝ)) / 2
      = (2 * (n : ℝ) - 1) / (2 * ((n : ℝ)) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  have hlog' : Real.log ((n : ℝ) / ((n : ℝ) - 1))
      ≤ (2 * (n : ℝ) - 1) / (2 * ((n : ℝ)) * ((n : ℝ) - 1)) := by
    rw [← hval, ← hinv]
    exact hlog
  have hlast : (2 * (n : ℝ) - 1) / (2 * ((n : ℝ)) * ((n : ℝ) - 1)) - 1 / (n : ℝ)
      = 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  rw [corrTerm]
  rw [← hlast]
  exact sub_le_sub_right hlog' _

private lemma corrTerm_two_le : corrTerm 2 ≤ 0.1931472 := by
  have h : corrTerm 2 = Real.log 2 - 1 / 2 := by
    rw [corrTerm]; norm_num
  rw [h]
  have := Real.log_two_lt_d9
  linarith

private lemma corrTerm_three_le : corrTerm 3 ≤ 0.0721318 := by
  have h : corrTerm 3 = Real.log 3 - Real.log 2 - 1 / 3 := by
    have harg : (↑(3:ℕ) : ℝ) / ((↑(3:ℕ):ℝ) - 1) = 3/2 := by norm_num
    rw [corrTerm, harg, Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  rw [h]
  have h1 := Real.log_three_lt_d9
  have h2 := Real.log_two_gt_d9
  linarith

private lemma corrTerm_five_le : corrTerm 5 ≤ 0.0231436 := by
  have h : corrTerm 5 = Real.log 5 - 2 * Real.log 2 - 1 / 5 := by
    have harg : (↑(5:ℕ) : ℝ) / ((↑(5:ℕ):ℝ) - 1) = 5/4 := by norm_num
    rw [corrTerm, harg, Real.log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have h1 := Real.log_five_lt_d9
  have h2 := Real.log_two_gt_d9
  linarith

/-- The explicit finset of all primes in `[7,400]`. -/
private def Pbig : Finset ℕ := {7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397}

set_option maxRecDepth 200000 in
private lemma Pbig_eq : Pbig = (Finset.Icc 7 400).filter Nat.Prime := by decide

private lemma Pbig_sum_le :
    (∑ p ∈ Pbig, (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1))) ≤ 2807/100000 := by
  norm_num [Pbig]

/-- Telescoping estimate: `Σ_{N < n ≤ M} 1/(n(n-1)) ≤ 1/N` for `N ≥ 1`. -/
private lemma sum_Icc_inv_pred_le (N M : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc (N+1) M, (1:ℝ)/((n:ℝ)*((n:ℝ)-1))) ≤ 1/(N:ℝ) := by
  rcases lt_or_ge N M with hM | hM
  · have hset : Finset.Icc (N+1) M = Finset.Ico (N+1) (M+1) := by
      ext n; simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hlen : M + 1 - (N + 1) = M - N := by omega
    rw [hlen]
    have hcongr : (∑ k ∈ Finset.range (M - N),
          (1:ℝ)/((((N+1)+k : ℕ):ℝ) * ((((N+1)+k : ℕ):ℝ) - 1)))
        = ∑ k ∈ Finset.range (M - N),
            ((1:ℝ)/((N:ℝ)+(k:ℝ)) - (1:ℝ)/((N:ℝ)+((k+1:ℕ):ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hcast : (((N+1)+k : ℕ):ℝ) = (N:ℝ) + k + 1 := by push_cast; ring
      rw [hcast]
      have hsub : (N:ℝ) + k + 1 - 1 = (N:ℝ) + k := by ring
      rw [hsub]
      have hcast2 : ((k+1:ℕ):ℝ) = (k:ℝ)+1 := by push_cast; ring
      rw [hcast2]
      have hpk : (N:ℝ) + k ≠ 0 := by positivity
      have hpk1 : (N:ℝ) + k + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hcongr]
    rw [Finset.sum_range_sub' (f := fun k => (1:ℝ)/((N:ℝ)+(k:ℝ))) (n := M - N)]
    simp only [Nat.cast_zero, add_zero]
    rw [Nat.cast_sub hM.le]
    have hNM : (N:ℝ) + ((M:ℝ) - (N:ℝ)) = (M:ℝ) := by ring
    rw [hNM]
    have hMpos : (0:ℝ) < (M:ℝ) := by
      have : 0 < M := by omega
      exact_mod_cast this
    have : 0 ≤ 1/(M:ℝ) := by positivity
    linarith
  · have hset : Finset.Icc (N+1) M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hset]
    simp

/-- Bound for the "correction" sum in the Euler product for the primes:
`Σ_{p ≤ y} (log (p/(p-1)) - 1/p) ≤ 0.318` for every `y`.

Each summand is `δ_p = Σ_{k ≥ 2} 1/(k p^k) ≥ 0`, and the key per-prime estimate is
`log (p/(p-1)) - 1/p ≤ 1/(2p(p-1))` (for `p ≥ 2`), which follows from
`log u ≤ (u - u⁻¹)/2` for `u = p/(p-1) ≥ 1` (commons `Commons.Analysis.Real.log_le_half_sub_inv`).
We single out `2,3,5` with the explicit decimal bounds on `log 2, log 3, log 5`, keep the
primes in `[7,400]` in an explicit finset (evaluated by `norm_num`), and telescope the tail. -/
theorem corr_sum_le (y : ℕ) :
    (∑ p ∈ Nat.primesLE y, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / (p : ℝ))) ≤ 0.318 := by
  change (∑ p ∈ Nat.primesLE y, corrTerm p) ≤ 0.318
  set A : Finset ℕ := Nat.primesLE y with hA
  -- split off the primes ≤ 5
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun p => p ≤ 5) corrTerm
  rw [← hsplit]
  have hsecond_eq : (∑ p ∈ A.filter (fun p => ¬ p ≤ 5), corrTerm p)
      = ∑ p ∈ A.filter (fun p => 5 < p), corrTerm p := by
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro p _
      exact not_le
    · intro p _; rfl
  rw [hsecond_eq]
  -- small primes bound
  have h235 : ({2,3,5} : Finset ℕ) = (Finset.Icc 2 5).filter Nat.Prime := by decide
  have hsmall_sub : A.filter (fun p => p ≤ 5) ⊆ ({2,3,5} : Finset ℕ) := by
    rw [hA]; intro p hp
    rw [h235, Finset.mem_filter]
    rw [Finset.mem_filter] at hp
    exact ⟨Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp.1).2.two_le, hp.2⟩,
      (Nat.mem_primesLE.mp hp.1).2⟩
  have hsum_small : (∑ p ∈ A.filter (fun p => p ≤ 5), corrTerm p)
      ≤ 0.1931472 + 0.0721318 + 0.0231436 := by
    have h1 : (∑ p ∈ A.filter (fun p => p ≤ 5), corrTerm p)
        ≤ ∑ p ∈ ({2,3,5} : Finset ℕ), corrTerm p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsmall_sub (by
        intro x hx _
        have hx' : x = 2 ∨ x = 3 ∨ x = 5 := by simpa using hx
        rcases hx' with rfl | rfl | rfl <;> exact corrTerm_nonneg (by decide))
    have h2 : (∑ p ∈ ({2,3,5} : Finset ℕ), corrTerm p)
        = corrTerm 2 + corrTerm 3 + corrTerm 5 := by
      rw [Finset.sum_insert (by decide : (2:ℕ) ∉ ({3,5} : Finset ℕ)),
          Finset.sum_insert (by decide : (3:ℕ) ∉ ({5} : Finset ℕ)),
          Finset.sum_singleton]
      ring
    calc (∑ p ∈ A.filter (fun p => p ≤ 5), corrTerm p)
        ≤ ∑ p ∈ ({2,3,5} : Finset ℕ), corrTerm p := h1
      _ = corrTerm 2 + corrTerm 3 + corrTerm 5 := h2
      _ ≤ 0.1931472 + 0.0721318 + 0.0231436 := by
          have a := corrTerm_two_le
          have b := corrTerm_three_le
          have c := corrTerm_five_le
          linarith
  -- large primes bound
  have hstep1 : (∑ p ∈ A.filter (fun p => 5 < p), corrTerm p)
      ≤ ∑ p ∈ A.filter (fun p => 5 < p), (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [hA] at hp
    have hpprime : Nat.Prime p := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    exact corrTerm_le_half_inv hpprime.two_le
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (A.filter (fun p => 5 < p))
    (fun p => p ≤ 400) (fun p => (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)))
  have hsubP : (A.filter (fun p => 5 < p)).filter (fun p => p ≤ 400) ⊆ Pbig := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp2, hp400⟩ := hp
    rw [Finset.mem_filter] at hp2
    obtain ⟨hpA, hp5⟩ := hp2
    rw [hA] at hpA
    obtain ⟨hpy, hpprime⟩ := Nat.mem_primesLE.mp hpA
    have hp7 : 7 ≤ p := by
      have h6 : p ≠ 6 := by rintro rfl; exact (by decide : ¬ Nat.Prime 6) hpprime
      omega
    rw [Pbig_eq, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp7, hp400⟩, hpprime⟩
  have hfirst : (∑ p ∈ (A.filter (fun p => 5 < p)).filter (fun p => p ≤ 400),
      (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1))) ≤ 2807/100000 := by
    have hle : (∑ p ∈ (A.filter (fun p => 5 < p)).filter (fun p => p ≤ 400),
        (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)))
        ≤ ∑ p ∈ Pbig, (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubP (by
      intro x hx _
      rw [Pbig_eq, Finset.mem_filter, Finset.mem_Icc] at hx
      have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
      have hx1 : (0:ℝ) < (x:ℝ) - 1 := by
        have : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
        linarith
      positivity)
    exact hle.trans Pbig_sum_le
  have hsubT : (A.filter (fun p => 5 < p)).filter (fun p => ¬ p ≤ 400) ⊆ Finset.Icc 401 y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp2, hp400⟩ := hp
    rw [Finset.mem_filter] at hp2
    obtain ⟨hpA, _⟩ := hp2
    rw [hA] at hpA
    obtain ⟨hpy, _⟩ := Nat.mem_primesLE.mp hpA
    rw [Finset.mem_Icc]
    exact ⟨by omega, hpy⟩
  have hsecond : (∑ p ∈ (A.filter (fun p => 5 < p)).filter (fun p => ¬ p ≤ 400),
      (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1))) ≤ 1/800 := by
    have hle : (∑ p ∈ (A.filter (fun p => 5 < p)).filter (fun p => ¬ p ≤ 400),
        (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)))
        ≤ ∑ n ∈ Finset.Icc 401 y, (1:ℝ)/(2*(n:ℝ)*((n:ℝ)-1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubT (by
      intro x hx _
      rw [Finset.mem_Icc] at hx
      have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
      have hx1 : (0:ℝ) < (x:ℝ) - 1 := by
        have : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
        linarith
      positivity)
    refine hle.trans ?_
    have htel : (∑ n ∈ Finset.Icc ((400:ℕ)+1) y, (1:ℝ)/((n:ℝ)*((n:ℝ)-1))) ≤ 1/(400:ℝ) :=
      sum_Icc_inv_pred_le 400 y (by norm_num)
    have hrw : (∑ n ∈ Finset.Icc 401 y, (1:ℝ)/(2*(n:ℝ)*((n:ℝ)-1)))
        = (1/2) * ∑ n ∈ Finset.Icc 401 y, (1:ℝ)/((n:ℝ)*((n:ℝ)-1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 401 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hnm1 : (0:ℝ) < (n:ℝ) - 1 := by
        have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
        linarith
      field_simp
    rw [hrw]
    have := mul_le_mul_of_nonneg_left htel (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  have hmid : (∑ p ∈ A.filter (fun p => 5 < p), (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)))
      ≤ 2807/100000 + 1/800 := by
    rw [← hsplit2]
    exact add_le_add hfirst hsecond
  have hbig : (∑ p ∈ A.filter (fun p => 5 < p), corrTerm p) ≤ 2807/100000 + 1/800 :=
    hstep1.trans hmid
  have htotal : (∑ p ∈ A.filter (fun p => p ≤ 5), corrTerm p)
      + (∑ p ∈ A.filter (fun p => 5 < p), corrTerm p) ≤ 0.318 := by
    have hkey : (0.1931472 : ℝ) + 0.0721318 + 0.0231436 + (2807/100000 + 1/800) ≤ 0.318 := by
      norm_num
    linarith [hsum_small, hbig, hkey]
  exact htotal

end

end Commons.NumberTheory.Mertens