import Mathlib

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Work.EKLC6Core

/-- Borel–Cantelli with a geometric bound: if the measures of a sequence of sets are bounded by
`ofReal (c * e^{-β n})` with `β > 0` and `c ≥ 0`, then the limsup of the sets is null. -/
theorem measure_iInter_iUnion_exp_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (A : ℕ → Set α) {c β : ℝ} (hc : 0 ≤ c) (hβ : 0 < β)
    (h : ∀ n : ℕ, μ (A n) ≤ ENNReal.ofReal (c * Real.exp (-(β * n)))) :
    μ (⋂ N : ℕ, ⋃ n ≥ N, A n) = 0 := by
  have hr_nn : 0 ≤ Real.exp (-β) := Real.exp_nonneg _
  have hr_lt : Real.exp (-β) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  -- the dominated geometric majorant is summable
  have hsumm : Summable (fun n : ℕ => c * Real.exp (-β) ^ n) :=
    (summable_geometric_of_lt_one hr_nn hr_lt).mul_left c
  have hnonneg : ∀ n : ℕ, 0 ≤ c * Real.exp (-β) ^ n := fun n =>
    mul_nonneg hc (pow_nonneg hr_nn n)
  have hrew : ∀ n : ℕ, c * Real.exp (-(β * n)) = c * Real.exp (-β) ^ n := fun n => by
    rw [show -(β * n) = (n : ℝ) * (-β) by ring, Real.exp_nat_mul]
  -- total mass of the majorant is finite
  have hkey : ∑' n : ℕ, ENNReal.ofReal (c * Real.exp (-(β * n)))
      = ENNReal.ofReal (∑' n : ℕ, c * Real.exp (-β) ^ n) := by
    simp_rw [hrew]
    exact (ENNReal.ofReal_tsum_of_nonneg hnonneg hsumm).symm
  have hfin : ∑' n : ℕ, ENNReal.ofReal (c * Real.exp (-(β * n))) < ∞ := by
    rw [hkey]; exact ENNReal.ofReal_lt_top
  -- hence the total measure of the sequence is finite, so Borel–Cantelli applies
  have hne : ∑' n : ℕ, μ (A n) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_of_lt hfin) (ENNReal.tsum_le_tsum h)
  have hlim : limsup A atTop = ⋂ N : ℕ, ⋃ n ≥ N, A n := by
    rw [limsup_eq_iInf_iSup_of_nat]
    rfl
  rw [← hlim, measure_limsup_atTop_eq_zero hne]

end Work.EKLC6Core
