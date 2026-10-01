import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.LogSqLeFourN
import Submission.Work.ZeroDensity.Jutila.MixedSumLe
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selSum_expansion
import Submission.Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
import Submission.Work.LinnikAreas.Density4.prime_log_gap_sum
import Submission.Work.LinnikAreas.Density4.vonMangoldt_mul_Bz_sum

namespace Work.ZeroDensity.Jutila

open Finset

/-- **Sharp second moment of the truncated von Mangoldt sum, case `N < z*z`**, reduced to the
hard `B_z²` input.

Writing `Λ_z = Λ + B_z` (`Bz_eq_LambdaR_sub_vonMangoldt`), `selSum_expansion` gives
`Σ_{n≤N} Λ_z(n)² = log²z + ΣΛ² + 2ΣΛ·B_z + ΣB_z²`, and the three sharp inputs
`vonMangoldt_sq_sum_bound`, `vonMangoldt_mul_Bz_sum` (+ `prime_log_gap_sum`) and the hypothesis
`hB` below assemble to `N·log z + C·N` (using `log²z ≤ 4N`, which holds because `z ≤ N`).
This is exactly `case2_bound` of `Submission/Work/LinnikAreas/Density4/selberg_LambdaR_sq_sharp.lean`
with `ε = 0` and with `Bz_sq_sum_bound_hard` passed in as the hypothesis `hB`
(the constant produced there, `C1 + 2*C2 + C3 + 4`, does not depend on `ε`).

The hypothesis `hB` is the statement of `Submission/Work/LinnikAreas/Density4/Bz_sq_sum_bound_hard`
(whose source exists but whose import chain is currently broken: files under
`Density4/BzS3/` are missing). -/
theorem LzSqIntBad
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      (∑ n ∈ Finset.Icc 1 N, (LinnikAreas.Density4.Bz z n) ^ 2) ≤
        (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)) + C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      (∑ n ∈ Finset.Icc 1 N, (Lz (z : ℝ) n) ^ 2) ≤
        (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ) := by
  -- The three sharp analytic inputs.
  obtain ⟨C1, _hC1, hLam⟩ := Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
  obtain ⟨C2, _hC2, hPr⟩ := Work.LinnikAreas.Density4.prime_log_gap_sum
  obtain ⟨C3, _hC3, hBz⟩ := hB
  refine ⟨C1 + 2 * C2 + C3 + 4, by positivity, ?_⟩
  intro z N hz hzN hNz
  have hz1 : 1 ≤ z := by omega
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hlogz : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast hz1)
  have hlogdiv : Real.log ((N : ℝ) / (z : ℝ)) = Real.log (N : ℝ) - Real.log (z : ℝ) :=
    Real.log_div (ne_of_gt hNpos) (ne_of_gt hzpos)
  -- The Selberg weight `Λ_z` of `bvDefs` is the truncated Selberg sum `Σ_{d ∣ n, d ≤ z} λ_d`.
  have hbridge : ∀ n : ℕ, Lz (z : ℝ) n
      = ∑ d ∈ n.divisors.filter (fun d => d ≤ z), Work.LinnikAreas.Density4.selLam z d := by
    intro n
    simp only [Lz, Work.LinnikAreas.Density4.selLam, Nat.cast_le]
  -- (1) von Mangoldt second moment, restricted to `[2,N]`.
  have hS1 : (∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
      ≤ (N : ℝ) * Real.log (N : ℝ) + C1 * (N : ℝ) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hLam N hN1)
    · intro x hx
      obtain ⟨h2x, hxN⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, hxN⟩
    · intro i _ _
      positivity
  -- (2) mixed sum, via `prime_log_gap_sum`.
  have hS2 : 2 * (∑ n ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt n * LinnikAreas.Density4.Bz z n)
      ≤ -2 * ((N : ℝ) * (Real.log (N : ℝ) - Real.log (z : ℝ))) + 2 * C2 * (N : ℝ) :=
    MixedSumLe C2 hPr z N hz hzN hNz
  -- (3) the hard `B_z²` input, restricted to `[2,N]` (`B_z(1) = 0`).
  have hS3 : (∑ n ∈ Finset.Icc 2 N, (LinnikAreas.Density4.Bz z n) ^ 2)
      ≤ (N : ℝ) * (Real.log (N : ℝ) - Real.log (z : ℝ)) + C3 * (N : ℝ) := by
    have h := hBz z N hz hzN hNz
    rw [hlogdiv] at h
    refine le_trans ?_ h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨h2x, hxN⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, hxN⟩
    · intro i _ _
      positivity
  -- (4) `log² z ≤ 4N`.
  have hsq : (Real.log (z : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := LogSqLeFourN z N hz1 hzN
  rw [Finset.sum_congr rfl (fun n _ => by rw [hbridge n]),
    Work.LinnikAreas.Density4.selSum_expansion z N hz hN1]
  nlinarith [hS1, hS2, hS3, hsq, hNpos, hlogz]

end Work.ZeroDensity.Jutila
