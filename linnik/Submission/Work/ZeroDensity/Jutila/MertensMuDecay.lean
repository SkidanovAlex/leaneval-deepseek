import Mathlib
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Commons.Analysis.Abel.summation_by_parts
import Submission.Work.LinnikAreas.Density4.BzHard.sum_exp_neg_sqrtlog_le

namespace Work.ZeroDensity.Jutila

open Finset

/-- **Abel summation identity for the Mertens function.**
`Σ_{n ≤ T} μ(n) = T · Σ_{n ≤ T} μ(n)/n − Σ_{n ≤ T−1} Σ_{m ≤ n} μ(m)/m`. -/
lemma mertens_mu_abel (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (ArithmeticFunction.moebius n : ℝ))
      = (T : ℝ) * Commons.NumberTheory.Moebius.muRecipSum T
        - ∑ m ∈ Finset.Icc 1 (T - 1), Commons.NumberTheory.Moebius.muRecipSum m := by
  have hLHS : (∑ n ∈ Finset.Icc 1 T, (ArithmeticFunction.moebius n : ℝ))
      = ∑ m ∈ Finset.Icc 1 T,
          ((m : ℝ) * ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ))) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      exact ne_of_gt this
    field_simp
  have hAb := Commons.Analysis.Abel.summation_by_parts
      (fun m : ℕ => (m : ℝ))
      (fun m : ℕ => (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)) T
  rw [hLHS, hAb]
  unfold Commons.NumberTheory.Moebius.muRecipSum
  rw [show (∑ m ∈ Finset.Icc 1 (T - 1),
        ((m : ℝ) - ((m + 1 : ℕ) : ℝ)) *
          (∑ k ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)))
      = - ∑ n ∈ Finset.Icc 1 (T - 1),
          ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) from by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    have : ((m : ℝ) - ((m + 1 : ℕ) : ℝ)) = -1 := by push_cast; ring
    rw [this, neg_one_mul]]
  ring

/-- **Mertens function bound with power-saving decay**: `|Σ_{n ≤ N} μ(n)| ≤ C·N·exp(−c√(log N))`.

This is the classical bound for the summatory Möbius function (Korobov–Vinogradov zero-free
region strength), i.e. the non-reciprocal companion of
`Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay`
(`|Σ_{n ≤ x} μ(n)/n| ≤ C·exp(−c√(log x))`, sorry-free, importable as
`import Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay`).

Route: Abel summation `Σ_{n≤T}μ(n) = T·Σ_{n≤T}μ(n)/n − Σ_{m≤T−1}Σ_{n≤m}μ(n)/n`
(`import Submission.Commons.Analysis.Abel.summation_by_parts`) plus the decay of the reciprocal
partial sums, converting the log-power saving into `exp(−c√log)` by
`exp(−c√(log x)) ≤ C_A·(log x)^(−A)`.  A worked proof of the closely related statement
`mertens_int_decay A hA : |Σ_{n≤x}μ(n)| ≤ C·x·(log(2+x))^{−A}` (for real `x`, with floors) is in
`Submission/Work/LinnikAreas/Density4/BzHard/mertens_mu_sum_decay.lean`; that file is currently
unbuildable only because one of its imports,
`Density4/BzHard/exp_neg_sqrtlog_le_log_rpow`, is missing, and the exp-form statement above
follows from its log-power form since `exp(−c√log x)` dominates every fixed log-power.
`BzHard/sum_exp_neg_sqrtlog_le.lean` (sorry-free, in the import list) supplies the companion
summation bound.

This bound is the standard `μ`-cancellation input for the `S₃` analysis of the hard-range
`B_z²` estimate, where signed sums `Σ_r μ(r)f(r)` are bounded by partial summation against a
decaying Mertens function. -/
theorem MertensMuDecay :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ)|
        ≤ C * (N : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (N : ℝ)))) := by
  obtain ⟨c, C0, hc, hC0, hdecay⟩ :=
    Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  have hCd := Commons.NumberTheory.Moebius.muRecipSum_decay hc hC0 hdecay
  obtain ⟨CB, hCBpos, hB⟩ :=
    Work.LinnikAreas.Density4.BzHard.sum_exp_neg_sqrtlog_le hc
  set M : ℝ := max C0 1 with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  refine ⟨M * (1 + CB), c / 4, by positivity, by linarith, ?_⟩
  intro N hN
  rcases eq_or_lt_of_le hN with h1 | h2
  · subst h1
    have hsum : (∑ n ∈ Finset.Icc 1 1, (ArithmeticFunction.moebius n : ℝ)) = 1 := by
      rw [Finset.Icc_self]; simp
    rw [hsum, abs_one]
    simp only [Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero,
      mul_one]
    nlinarith [hM1, hCBpos]
  · have hN1 : 1 ≤ N := by omega
    have hN2 : 2 ≤ N := by omega
    have hNcast : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hexp_le : Real.exp (-(c * Real.sqrt (Real.log (N : ℝ))))
        ≤ Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hspos : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
      nlinarith [mul_nonneg hc.le hspos]
    have hterm1 : |(N : ℝ) * Commons.NumberTheory.Moebius.muRecipSum N|
        ≤ (N : ℝ) * (M * Real.exp (-(c * Real.sqrt (Real.log (N : ℝ))))) := by
      rw [abs_mul, abs_of_nonneg hNcast]
      exact mul_le_mul_of_nonneg_left (hCd N hN1) hNcast
    have hterm2 :
        |∑ m ∈ Finset.Icc 1 (N - 1), Commons.NumberTheory.Moebius.muRecipSum m|
        ≤ M * (CB * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ)))) := by
      calc |∑ m ∈ Finset.Icc 1 (N - 1), Commons.NumberTheory.Moebius.muRecipSum m|
          ≤ ∑ m ∈ Finset.Icc 1 (N - 1), |Commons.NumberTheory.Moebius.muRecipSum m| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (N - 1),
              M * Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))) := by
            apply Finset.sum_le_sum
            intro m hm
            exact hCd m (Finset.mem_Icc.mp hm).1
        _ = M * ∑ m ∈ Finset.Icc 1 (N - 1),
              Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))) := by
            rw [Finset.mul_sum]
        _ ≤ M * (CB * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ)))) :=
            mul_le_mul_of_nonneg_left (hB N hN2) hMpos.le
    rw [mertens_mu_abel N]
    calc |(N : ℝ) * Commons.NumberTheory.Moebius.muRecipSum N
            - ∑ m ∈ Finset.Icc 1 (N - 1), Commons.NumberTheory.Moebius.muRecipSum m|
        ≤ |(N : ℝ) * Commons.NumberTheory.Moebius.muRecipSum N|
            + |∑ m ∈ Finset.Icc 1 (N - 1), Commons.NumberTheory.Moebius.muRecipSum m| :=
          abs_sub _ _
      _ ≤ (N : ℝ) * (M * Real.exp (-(c * Real.sqrt (Real.log (N : ℝ)))))
            + M * (CB * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ)))) :=
          add_le_add hterm1 hterm2
      _ ≤ (N : ℝ) * (M * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))))
            + M * (CB * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ)))) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp_le hMpos.le) hNcast
          · exact le_refl _
      _ = M * (1 + CB) * (N : ℝ) * Real.exp (-(c / 4) * Real.sqrt (Real.log (N : ℝ))) := by
          ring
      _ = M * (1 + CB) * (N : ℝ) * Real.exp (-((c / 4) * Real.sqrt (Real.log (N : ℝ)))) := by
          rw [← neg_mul]

end Work.ZeroDensity.Jutila
