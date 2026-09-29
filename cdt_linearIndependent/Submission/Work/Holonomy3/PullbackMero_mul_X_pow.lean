import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

open Submission.CDTPlan

/-- **Reindexing a series with finitely many leading zeros.** If the series `a` has been shifted by
`n` places and the terms `a 0, …, a (n-1)` all vanish, then the shifted series and the original
series have the same sum. Stated for an arbitrary topological additive commutative group so that it
applies to `ℂ`. -/
private lemma hasSum_nat_sub_of_hasSum {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {a : ℕ → E} {S : E} (n : ℕ)
    (h : HasSum (fun m => a (m + n)) S) (h0 : ∀ i < n, a i = 0) : HasSum a S := by
  have hpartial : ∑ i ∈ Finset.range n, a i = 0 :=
    Finset.sum_eq_zero fun i hi => h0 i (Finset.mem_range.mp hi)
  have h' : HasSum (fun m => a (m + n)) (S - ∑ i ∈ Finset.range n, a i) := by
    rw [hpartial, sub_zero]; exact h
  exact (hasSum_nat_add_iff' n).mp h'

/-- **Closure of `PullbackMero` under multiplication by `x^n`.** The auxiliary function of the paper
is a `Q(x)`-combination of the `f_i` times monomials, so the meromorphicity of its pullback is
assembled from the meromorphicity of the pullbacks of the `f_i` together with the holomorphy of the
pullbacks of the polynomial coefficients. -/
theorem PullbackMero_mul_X_pow {f : PowerSeries ℚ} {φ : ℂ → ℂ}
    (hf : Submission.CDTPlan.PullbackMero f φ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1))
    (n : ℕ) :
    Submission.CDTPlan.PullbackMero (f * PowerSeries.X ^ n) φ := by
  obtain ⟨P, N, hP0, hN, hsum⟩ := hf
  -- the new denominator is the same `P`, and the new numerator is `φ^n · N`
  refine ⟨P, fun z => φ z ^ n * N z, hP0, (hφ.pow n).mul hN, ?_⟩
  filter_upwards [hsum] with z hz
  -- `hz` is the convergence of the pullback of `f`; multiply it by `φ z ^ n` and reindex
  have h1 : HasSum (fun m => ((PowerSeries.coeff m f : ℚ) : ℂ) * φ z ^ (m + n))
      (φ z ^ n * (N z / P.eval z)) := by
    have h2 := hz.mul_left (φ z ^ n)
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using h2
  -- `d` is the summand of the pullback of `f * X^n`, with the finitely many vanished terms kept
  set d : ℕ → ℂ := fun k => if n ≤ k then ((PowerSeries.coeff (k - n) f : ℚ) : ℂ) * φ z ^ k else 0
    with hddef
  have hdshift : HasSum (fun m => d (m + n)) (φ z ^ n * (N z / P.eval z)) :=
    h1.congr_fun fun m => by
      simp only [hddef]
      rw [if_pos (Nat.le_add_left n m), Nat.add_sub_cancel]
  have hdzero : ∀ i < n, d i = 0 := by
    intro i hi
    simp only [hddef]
    rw [if_neg (Nat.not_le.mpr hi)]
  have hd : HasSum d (φ z ^ n * (N z / P.eval z)) := hasSum_nat_sub_of_hasSum n hdshift hdzero
  rw [mul_div_assoc]
  refine hd.congr_fun fun k => ?_
  by_cases hk : n ≤ k
  · simp [hddef, PowerSeries.coeff_mul_X_pow' f n k, hk]
  · simp [hddef, PowerSeries.coeff_mul_X_pow' f n k, hk]

end Work.Holonomy3
