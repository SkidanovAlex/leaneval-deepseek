import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# Concavity of `Hfam`: `∑ k, c k * Hfam (μs k) A ≤ Hfam (∑ k, ofReal (c k) • μs k) A`

`Work.EKLContract.Hfam μ P = ∑ i, Real.negMulLog (μ (P i)).toReal` is the Shannon entropy of the
finite family `P` (with respect to a possibly non-probability measure `μ`, values through
`ENNReal.toReal`).  Since `Real.negMulLog` is concave on `[0,∞)` and vanishes at `0`, a weighted
average of entropies with weights `c k ≥ 0`, `∑ k, c k ≤ 1` is bounded by the entropy of the
corresponding (sub-probability) convex combination `∑ k, ofReal (c k) • μs k` of the measures.

Two elementary ingredients are isolated as helper lemmas:

* `sum_mul_negMulLog_le`: the weighted concavity inequality for `Real.negMulLog` on `[0,∞)`
  with total weight at most `1` (the deficit `1 - ∑ c k` is compensated by the `0` value of
  `negMulLog`).
* `sum_smul_apply_toReal`: the value of a finite `ℝ≥0∞`-weighted sum of measures on a set,
  passed through `ENNReal.toReal`.

The proof of `Hfam_sum_le` then exchanges the two finite sums and applies the concavity inequality
pointwise to the real numbers `((μs k) (A i)).toReal`.
-/

namespace Work.Misiurewicz

open MeasureTheory

/-- Weighted concavity inequality for `Real.negMulLog` with total weight at most `1`:

`∑ k, c k * negMulLog (x k) ≤ negMulLog (∑ k, c k * x k)` for `c k ≥ 0`, `∑ k, c k ≤ 1`,
`x k ≥ 0`.  The deficit in the total weight is spent on the point `0`, where `negMulLog` vanishes. -/
lemma sum_mul_negMulLog_le {κ : Type*} [Fintype κ] (c x : κ → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hx : ∀ k, 0 ≤ x k) (hc1 : ∑ k, c k ≤ 1) :
    ∑ k, c k * Real.negMulLog (x k) ≤ Real.negMulLog (∑ k, c k * x k) := by
  have hmem : ∀ k ∈ (Finset.univ : Finset κ), x k ∈ Set.Ici (0 : ℝ) :=
    fun k _ => Set.mem_Ici.mpr (hx k)
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have hv : 0 ≤ 1 - ∑ k, c k := by linarith
  have h1 : (1 - ∑ k, c k) + ∑ k ∈ (Finset.univ : Finset κ), c k = 1 := by simp
  have h := Real.concaveOn_negMulLog.map_add_sum_le (t := (Finset.univ : Finset κ))
    (w := c) (p := x) (v := 1 - ∑ k, c k) (q := 0) (fun k _ => hc k) h1 hmem hv h0
  simpa using h

/-- The value on a set of a finite `ℝ≥0∞`-weighted sum of probability measures, through
`ENNReal.toReal`.  The probability hypothesis is used only to guarantee finiteness, so that
`ENNReal.toReal_sum` applies. -/
lemma sum_smul_apply_toReal {κ : Type*} [Fintype κ] {X : Type*} [MeasurableSpace X]
    (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) (μs : κ → Measure X)
    (hμ : ∀ k, μs k Set.univ = 1) (B : Set X) :
    ((∑ k, ENNReal.ofReal (c k) • μs k) B).toReal = ∑ k, c k * (μs k B).toReal := by
  have hsum : (∑ k, ENNReal.ofReal (c k) • μs k) B
      = ∑ k, ENNReal.ofReal (c k) * (μs k B) := by
    rw [Measure.finsetSum_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [Measure.smul_apply, smul_eq_mul])
  rw [hsum, ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl (fun k _ => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc k)])
  · intro k _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (by rw [hμ k]; exact ENNReal.one_ne_top)
        (MeasureTheory.measure_mono (Set.subset_univ B)))

theorem Hfam_sum_le {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι]
    (A : ι → Set Work.EKLContract.X3) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hc1 : ∑ k, c k ≤ 1) (μs : κ → MeasureTheory.Measure Work.EKLContract.X3)
    [∀ k, MeasureTheory.IsProbabilityMeasure (μs k)] :
    ∑ k, c k * Work.EKLContract.Hfam (μs k) A ≤
      Work.EKLContract.Hfam (∑ k, ENNReal.ofReal (c k) • μs k) A := by
  have hmu : ∀ k, μs k Set.univ = 1 := fun k => IsProbabilityMeasure.measure_univ
  have key : ∀ i, ∑ k, c k * Real.negMulLog ((μs k) (A i)).toReal
      ≤ Real.negMulLog (((∑ k, ENNReal.ofReal (c k) • μs k) (A i)).toReal) := by
    intro i
    rw [sum_smul_apply_toReal c hc μs hmu (A i)]
    exact sum_mul_negMulLog_le c (fun k => ((μs k) (A i)).toReal) hc
      (fun _ => ENNReal.toReal_nonneg) hc1
  simp only [Work.EKLContract.Hfam]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => key i)

end Work.Misiurewicz
