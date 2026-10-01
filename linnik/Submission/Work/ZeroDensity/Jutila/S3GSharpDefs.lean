/-
# Shared definitions for the sharp `s3G` estimate

This module collects the objects used by `Work.ZeroDensity.Jutila.S3GAbelSharp` and by the
pieces it is assembled from:

* `s3Sig c = Σ_{d ∣ c} 1/√d`, the `σ_{-1/2}` factor of the target bound;
* `s3Count c M = Σ_{m ≤ M, (m,c)=1} μ²(m)`, the squarefree-coprime counting function;
* `s3Delta c M = s3Count c M − C_c·M`, the Abel difference sequence, where
  `C_c = ζ(2)⁻¹ ∏_{p ∣ c} p/(p+1)` is the density `s3c c` of `BzS3/S3InnerDefs.lean`.

The estimate of `s3Delta` (with the sharp power-saving error `σ_{-1/2}`) is proved here from
`BzS3.sqfree_coprime_count_main`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3GAuxDefs
import Submission.Work.LinnikAreas.Density4.BzS3.sqfree_coprime_count_main

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- `σ_{-1/2}(c) = Σ_{d ∣ c} 1/√d`. -/
def s3Sig (c : ℕ) : ℝ := ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)

/-- The squarefree-coprime counting function `Σ_{m ≤ M, (m,c)=1} μ²(m)`. -/
def s3Count (c M : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m c),
    ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2

/-- The Abel difference sequence `Δ(M) = Σ_{m ≤ M, (m,c)=1} μ²(m) − C_c·M`, where
`C_c = ζ(2)⁻¹∏_{p ∣ c} p/(p+1)` is `BzS3.s3c c`. -/
def s3Delta (c M : ℕ) : ℝ := s3Count c M - LinnikAreas.Density4.BzS3.s3c c * (M : ℝ)

lemma s3Sig_nonneg (c : ℕ) : 0 ≤ s3Sig c :=
  Finset.sum_nonneg (fun d _ => by positivity)

lemma s3Sig_one_le (c : ℕ) (hc : 1 ≤ c) : 1 ≤ s3Sig c := by
  have hmem : (1 : ℕ) ∈ c.divisors := Nat.one_mem_divisors.mpr (by omega)
  have h := Finset.single_le_sum (s := c.divisors)
    (f := fun d : ℕ => (1 : ℝ) / Real.sqrt (d : ℝ)) (fun d _ => by positivity) hmem
  simpa [s3Sig] using h

/-- The squarefree-coprime count as a sum of the indicator `μ²(m)·[m ⟂ c]`. -/
lemma s3Count_eq_sum_ite (c M : ℕ) :
    s3Count c M
      = ∑ m ∈ Finset.Icc 1 M,
          (if Nat.Coprime m c then ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 else 0) := by
  rw [s3Count, Finset.sum_filter]

/-- **The squarefree-coprime count with the sharp `σ_{-1/2}` error term.** -/
theorem s3Delta_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (c M : ℕ), 1 ≤ c → 1 ≤ M →
      |s3Delta c M| ≤ C * s3Sig c * Real.sqrt (M : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := Work.LinnikAreas.Density4.BzS3.sqfree_coprime_count_main
  refine ⟨C, hC, ?_⟩
  intro c M hc hM
  have h := hcount M c hM hc
  have hmain : (M : ℝ) * (∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) / (Real.pi ^ 2 / 6)
      = LinnikAreas.Density4.BzS3.s3c c * (M : ℝ) := by
    rw [LinnikAreas.Density4.BzS3.s3c]
    ring
  rw [hmain] at h
  rw [s3Delta, s3Count, s3Sig]
  have h' : C * Real.sqrt (M : ℝ) * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))
      = (C * (∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ))) * Real.sqrt (M : ℝ) := by ring
  rw [h'] at h
  exact h

end

end Work.ZeroDensity.Jutila
