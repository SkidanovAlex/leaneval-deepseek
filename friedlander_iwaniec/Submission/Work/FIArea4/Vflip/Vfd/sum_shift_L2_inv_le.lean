import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Vflip.Vfd.shift_sum_inv_le

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

/-- The `ρ`-weighted `L²`-energies of the shifted arrays `(r,s) ↦ β (ρ*r) s` are dominated by
`(log (2R) + 1)` times the `L²`-energy of `β`.  Interchanging the `ρ`- and `s`-sums reduces the
statement, for each fixed `s`, to `shift_sum_inv_le` applied to `F n = ‖β n s‖²`, whose support
on `n ≤ 2R` is `hβ`.  The `s`-sum is then absorbed by `Finset.sum_le_sum`. -/
theorem sum_shift_L2_inv_le (R S : ℕ) (β : ℕ → ℕ → ℂ) (hR : 1 ≤ R)
    (hβ : ∀ r s, β r s ≠ 0 → r ≤ 2*R) :
    ∑ ρ ∈ Finset.Icc 1 (2*R),
        ((ρ:ℝ))⁻¹ * Work.FIArea4.p14L2 R S (Work.FIArea4.Vflip.Vfd.shiftCoef ρ β)
      ≤ (Real.log (2*R) + 1) * Work.FIArea4.p14L2 R S β := by
  have hcast : (2 : ℝ) * (R : ℝ) = ((2*R : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have hR2 : 1 ≤ 2*R := by omega
  have key : ∀ s ∈ Finset.Icc 1 (2*S),
      ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * ∑ r ∈ Finset.Icc 1 (2*R), Complex.normSq (β (ρ*r) s)
        ≤ (Real.log ((2*R : ℕ) : ℝ) + 1) * ∑ n ∈ Finset.Icc 1 (2*R), Complex.normSq (β n s) := by
    intro s _
    exact shift_sum_inv_le hR2 (fun n => Complex.normSq (β n s))
      (fun n => Complex.normSq_nonneg _)
      (fun n hn => by
        rw [Complex.normSq_eq_zero]
        by_contra h
        exact (not_le.mpr hn) (hβ n s h))
  simp only [Work.FIArea4.p14L2, Work.FIArea4.Vflip.Vfd.shiftCoef_apply]
  calc ∑ ρ ∈ Finset.Icc 1 (2*R), (ρ:ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β (ρ*r) s)
      = ∑ ρ ∈ Finset.Icc 1 (2*R), (ρ:ℝ)⁻¹ * ∑ s ∈ Finset.Icc 1 (2*S), ∑ r ∈ Finset.Icc 1 (2*R), Complex.normSq (β (ρ*r) s) := by
          apply Finset.sum_congr rfl; intro ρ _
          rw [Finset.sum_comm]
    _ = ∑ ρ ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), (ρ:ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 (2*R), Complex.normSq (β (ρ*r) s) := by
          apply Finset.sum_congr rfl; intro ρ _
          rw [Finset.mul_sum]
    _ = ∑ s ∈ Finset.Icc 1 (2*S), ∑ ρ ∈ Finset.Icc 1 (2*R), (ρ:ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 (2*R), Complex.normSq (β (ρ*r) s) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ s ∈ Finset.Icc 1 (2*S), (Real.log ((2*R : ℕ) : ℝ) + 1) * ∑ n ∈ Finset.Icc 1 (2*R), Complex.normSq (β n s) := by
          apply Finset.sum_le_sum; intro s hs; exact key s hs
    _ = (Real.log ((2*R : ℕ) : ℝ) + 1) * ∑ s ∈ Finset.Icc 1 (2*S), ∑ n ∈ Finset.Icc 1 (2*R), Complex.normSq (β n s) := by
          rw [Finset.mul_sum]
    _ = (Real.log ((2*R : ℕ) : ℝ) + 1) * ∑ n ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β n s) := by
          rw [Finset.sum_comm]

end Work.FIArea4.Vflip.Vfd
