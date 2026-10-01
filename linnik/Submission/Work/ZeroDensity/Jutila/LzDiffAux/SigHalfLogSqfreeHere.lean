/-
# `Σ_{t squarefree ≤ T} σ_{-1/2}(t)/κ(t)·(1 + |log(T/t)|) ≪ (log T)²`

The summand is `σ_{-1/2}(t)/κ(t) = (Σ_{d | t} d^{-1/2}) / ∏_{p | t}(p+1)`.

For squarefree `t`, `κ(t) = ∏_{p | t}(p+1) ≥ ∏_{p | t} p = t`, so the summand is at most
`σ_{-1/2}(t)/t`; extending the sum to all `t ≤ N` (the terms are non-negative) and swapping
divisors gives
`Σ_{t ≤ N} σ_{-1/2}(t)/t = Σ_{d ≤ N} (d√d)^{-1} · Σ_{m ≤ N/d} 1/m ≤ 6(1 + log N)`
(the inner harmonic sum is `≤ 1 + log(N/d) ≤ 1 + log N`, and `Σ_{d ≤ N} 1/(d√d) ≤ 6`).
Finally `1 + |log(T/t)| = 1 + log(T/t) ≤ 1 + log T` for `1 ≤ t ≤ T`, and `⌊T⌋₊ ≤ T`.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.Density4.BzBilinDefs
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le
import Submission.Work.ZeroDensity.Jutila.S3SmHarmonic

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

noncomputable section

/-- For squarefree `t`, `κ(t) = ∏_{p | t}(p + 1) ≥ ∏_{p | t} p = t`. -/
private lemma kap_ge_self_of_squarefree (t : ℕ) (ht : Squarefree t) :
    (t : ℝ) ≤ Work.ZeroDensity.Jutila.kap t := by
  have hle : (∏ p ∈ t.primeFactors, (p : ℝ)) ≤ ∏ p ∈ t.primeFactors, ((p : ℝ) + 1) :=
    Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => by linarith)
  have hprod : (∏ p ∈ t.primeFactors, (p : ℝ)) = (t : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ht]
  rw [Work.ZeroDensity.Jutila.kap, ← hprod]
  exact hle

/-- Divisor-swap identity: writing `t = d·(t/d)`,
`Σ_{t ≤ N} σ_{-1/2}(t)/t = Σ_{d ≤ N} (d·√d)^{-1} · Σ_{m ≤ N/d} 1/m`. -/
private lemma sum_sigmaHalf_div_swap (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf n / (n : ℝ))
      = ∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          ∑ m ∈ Finset.Icc 1 (N / d), (1 / (m : ℝ)) := by
  have h := Work.LinnikAreas.Density4.sum_Icc_div_reindex N (fun _ => True)
      (fun d m => (1 / Real.sqrt (d : ℝ)) * (1 / ((d : ℝ) * (m : ℝ))))
  simp only [Finset.filter_true] at h
  have hB : (∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf n / (n : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (1 / Real.sqrt (d : ℝ)) * (1 / ((d : ℝ) * ((n / d : ℕ) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Work.LinnikAreas.Density4.sigmaHalf, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hmain : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    rw [div_eq_mul_inv, one_div, one_div, hmain]
  have hA : (∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          ∑ m ∈ Finset.Icc 1 (N / d), (1 / (m : ℝ)))
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          (1 / Real.sqrt (d : ℝ)) * (1 / ((d : ℝ) * (m : ℝ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hs : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
    field_simp
  exact hB.trans (h.symm.trans hA.symm)

/-- `Σ_{t ≤ N} σ_{-1/2}(t)/t ≤ 6 (1 + log N)` for `N ≥ 1`. -/
private lemma sum_sigmaHalf_div_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf n / (n : ℝ)
      ≤ 6 * (1 + Real.log (N : ℝ)) := by
  rw [sum_sigmaHalf_div_swap N]
  have hstep1 : (∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
        ∑ m ∈ Finset.Icc 1 (N / d), (1 / (m : ℝ)))
      ≤ ∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          (1 + Real.log (((N / d : ℕ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro d hd
    have hdle : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hd0 : 0 < d := by
      have h1 := (Finset.mem_Icc.mp hd).1
      omega
    have hNd : 1 ≤ N / d := (Nat.one_le_div_iff hd0).mpr hdle
    exact mul_le_mul_of_nonneg_left (Work.ZeroDensity.Jutila.S3SmHarmonic (N / d) hNd)
      (by positivity)
  have hstep2 : (∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          (1 + Real.log (((N / d : ℕ) : ℝ))))
      ≤ ∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          (1 + Real.log (N : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hdle : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hd0 : 0 < d := by
      have h1 := (Finset.mem_Icc.mp hd).1
      omega
    have hNd : 1 ≤ N / d := (Nat.one_le_div_iff hd0).mpr hdle
    have hpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hNd
    have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_le_self N d
    have hlog : Real.log (((N / d : ℕ) : ℝ)) ≤ Real.log (N : ℝ) := Real.log_le_log hpos hle
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hstep3 : (∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          (1 + Real.log (N : ℝ)))
      = (1 + Real.log (N : ℝ)) *
          ∑ d ∈ Finset.Icc 1 N, 1 / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
    rw [← Finset.sum_mul, mul_comm]
  have hstep4 : (1 + Real.log (N : ℝ)) *
        ∑ d ∈ Finset.Icc 1 N, 1 / ((d : ℝ) * Real.sqrt (d : ℝ))
      ≤ (1 + Real.log (N : ℝ)) * 6 := by
    apply mul_le_mul_of_nonneg_left (Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le N)
    have h1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  calc (∑ d ∈ Finset.Icc 1 N, (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) *
          ∑ m ∈ Finset.Icc 1 (N / d), (1 / (m : ℝ)))
      ≤ (1 + Real.log (N : ℝ)) * 6 := hstep1.trans (hstep2.trans (hstep3.le.trans hstep4))
    _ = 6 * (1 + Real.log (N : ℝ)) := by ring

theorem SigHalfLogSqfreeHere : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
    ∑ t ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun t => Squarefree t),
        ((∑ d ∈ t.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Work.ZeroDensity.Jutila.kap t)
          * (1 + |Real.log (T/(t:ℝ))|)
      ≤ C * (1 + Real.log T)^2 := by
  refine ⟨6, by norm_num, fun T hT => ?_⟩
  set N : ℕ := ⌊T⌋₊ with hN
  have hN1 : 1 ≤ N := by
    have h : 0 < ⌊T⌋₊ := Nat.floor_pos.mpr hT
    omega
  have hNT : (N : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hlogT0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hlogN : Real.log (N : ℝ) ≤ Real.log T := by
    apply Real.log_le_log
    · have h : 0 < N := by omega
      exact_mod_cast h
    · exact hNT
  have hpt : ∀ t ∈ (Finset.Icc 1 N).filter (fun t => Squarefree t),
      ((∑ d ∈ t.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Work.ZeroDensity.Jutila.kap t)
        * (1 + |Real.log (T/(t:ℝ))|)
      ≤ (Work.LinnikAreas.Density4.sigmaHalf t / (t:ℝ)) * (1 + Real.log T) := by
    intro t ht
    have htIcc : t ∈ Finset.Icc 1 N := (Finset.mem_filter.mp ht).1
    have hsf : Squarefree t := (Finset.mem_filter.mp ht).2
    have htN : t ≤ N := (Finset.mem_Icc.mp htIcc).2
    have ht0 : (0 : ℝ) < (t : ℝ) := by
      have h1 := (Finset.mem_Icc.mp htIcc).1
      exact_mod_cast (by omega : 0 < t)
    have htT : (t : ℝ) ≤ T := le_trans (by exact_mod_cast htN) hNT
    have hTt : (1 : ℝ) ≤ T / (t : ℝ) := by
      rw [le_div_iff₀ ht0]
      linarith
    have hlogTt : (0 : ℝ) ≤ Real.log (T / (t : ℝ)) := Real.log_nonneg hTt
    have habs : |Real.log (T/(t:ℝ))| = Real.log (T/(t:ℝ)) := abs_of_nonneg hlogTt
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp htIcc).1
    have hlogle : Real.log (T/(t:ℝ)) ≤ Real.log T := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ ht0]
      nlinarith [hT, ht1]
    have hkap : (t : ℝ) ≤ Work.ZeroDensity.Jutila.kap t := kap_ge_self_of_squarefree t hsf
    have h1 : Work.LinnikAreas.Density4.sigmaHalf t / Work.ZeroDensity.Jutila.kap t
        ≤ Work.LinnikAreas.Density4.sigmaHalf t / (t : ℝ) :=
      div_le_div_of_nonneg_left (Work.LinnikAreas.Density4.sigmaHalf_nonneg t) ht0 hkap
    rw [show (∑ d ∈ t.divisors, (1:ℝ)/Real.sqrt (d:ℝ))
          = Work.LinnikAreas.Density4.sigmaHalf t from rfl, habs]
    exact mul_le_mul h1 (by linarith) (by linarith)
      (div_nonneg (Work.LinnikAreas.Density4.sigmaHalf_nonneg t) ht0.le)
  have hg : ∀ t ∈ Finset.Icc 1 N,
      0 ≤ (Work.LinnikAreas.Density4.sigmaHalf t / (t:ℝ)) * (1 + Real.log T) := by
    intro t ht
    have ht0 : (0 : ℝ) < (t : ℝ) := by
      have h1 := (Finset.mem_Icc.mp ht).1
      exact_mod_cast (by omega : 0 < t)
    have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
    exact mul_nonneg (div_nonneg (Work.LinnikAreas.Density4.sigmaHalf_nonneg t) ht0.le)
      (by linarith)
  calc ∑ t ∈ (Finset.Icc 1 N).filter (fun t => Squarefree t),
        ((∑ d ∈ t.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Work.ZeroDensity.Jutila.kap t)
          * (1 + |Real.log (T/(t:ℝ))|)
      ≤ ∑ t ∈ (Finset.Icc 1 N).filter (fun t => Squarefree t),
          (Work.LinnikAreas.Density4.sigmaHalf t / (t:ℝ)) * (1 + Real.log T) :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ t ∈ Finset.Icc 1 N,
          (Work.LinnikAreas.Density4.sigmaHalf t / (t:ℝ)) * (1 + Real.log T) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi _ => hg i hi)
    _ = (1 + Real.log T) *
          ∑ t ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf t / (t:ℝ) := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ (1 + Real.log T) * (6 * (1 + Real.log (N:ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_sigmaHalf_div_le N hN1) (by linarith)
    _ ≤ (1 + Real.log T) * (6 * (1 + Real.log T)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
    _ = 6 * (1 + Real.log T)^2 := by ring

end

end Work.ZeroDensity.Jutila.LzDiffAux
