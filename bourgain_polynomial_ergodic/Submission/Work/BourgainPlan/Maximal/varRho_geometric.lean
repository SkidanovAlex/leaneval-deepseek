import Mathlib
import Submission.Work.BourgainPlan.Maximal.varRho_le_sum_increments

/-!
# The variation of a geometrically decaying family (KMSZ (6.17))

Kosz–Mirek–Słomian–Zhang (arXiv:2606.12663), the summation step (6.17) of the minor-arc half of
the assembly: a family `(a_n)` whose norms decay geometrically in the scale has bounded
`ρ`-variation over every index window, with a bound depending only on the decay rate.

The proof is the landed comparison `varRho_le_sum_increments` (`V^ρ ≤ V^1`, i.e. the `ρ`-variation
is bounded by the total variation of the consecutive increments) followed by the telescoping of the
geometric series.

Consumers: (6.17) of the assembly, where `a_n = A_{N_n}(f − Π_{≤l(N_n),≤−dL(N_n)}f)` and the
per-scale estimate (6.16) supplies `‖a_n‖_{ℓ^p} ≲ N_n^{−c_p}‖f‖_{ℓ^p}` with `N_n = ⌊τ^{n+1}⌋`.
-/

open Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Maximal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **The `ρ`-variation of a geometrically decaying family.**  If `‖a k‖ ≤ C r^k` with `0 ≤ r < 1`,
then over the index window `[lo, hi]` the `ρ`-variation is at most
`C (1 + r) r^{lo} / (1 - r)`. -/
theorem varRho_le_of_geometric {ρ C r : ℝ} (hρ : 1 ≤ ρ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {a : ℕ → E} (ha : ∀ k, ‖a k‖ ≤ C * r ^ k) (lo hi : ℕ) :
    varRho ρ lo hi a ≤ ENNReal.ofReal (C * (1 + r) * (1 - r)⁻¹ * r ^ lo) := by
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have hsummable : Summable fun k : ℕ => r ^ k := summable_geometric_of_norm_lt_one hrnorm
  have htsum : (∑' k : ℕ, r ^ k) = (1 - r)⁻¹ := tsum_geometric_of_norm_lt_one hrnorm
  have hpow : ∀ j : ℕ, r ^ (j + lo) = r ^ lo * r ^ j := by
    intro j; rw [pow_add]; ring
  have hsum2 : Summable fun j : ℕ => r ^ (j + lo) := by
    rw [show (fun j : ℕ => r ^ (j + lo)) = fun j : ℕ => r ^ lo * r ^ j from funext hpow]
    exact hsummable.mul_left _
  have hshift : (∑' j : ℕ, r ^ (j + lo)) = r ^ lo * (1 - r)⁻¹ := by
    rw [show (fun j : ℕ => r ^ (j + lo)) = fun j : ℕ => r ^ lo * r ^ j from funext hpow]
    rw [tsum_mul_left, htsum]
  -- each consecutive increment is bounded by the geometric weight
  have hincr : ∀ k : ℕ, ‖a (k + 1) - a k‖ₑ ≤ ENNReal.ofReal (C * (1 + r) * r ^ k) := by
    intro k
    have h1 : ‖a (k + 1)‖ ≤ C * r ^ k * r := by
      have h := ha (k + 1)
      rw [pow_succ] at h
      simpa only [mul_assoc] using h
    have h2 : ‖a k‖ ≤ C * r ^ k := ha k
    have h3 : ‖a (k + 1) - a k‖ ≤ C * (1 + r) * r ^ k := by
      refine le_trans (norm_sub_le _ _) ?_
      have h4 : C * r ^ k * r + C * r ^ k = C * (1 + r) * r ^ k := by ring
      linarith [h4 ▸ add_le_add h1 h2]
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h3
  -- the geometric tail
  have hgeo : (∑ k ∈ Finset.Ico lo hi, C * (1 + r) * r ^ k)
      ≤ C * (1 + r) * (1 - r)⁻¹ * r ^ lo := by
    rw [← Finset.mul_sum]
    have hle : (∑ k ∈ Finset.Ico lo hi, r ^ k) ≤ (1 - r)⁻¹ * r ^ lo := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [Finset.sum_congr rfl (fun j _ => by rw [Nat.add_comm])]
      calc ∑ j ∈ Finset.range (hi - lo), r ^ (j + lo)
          ≤ ∑' j : ℕ, r ^ (j + lo) :=
            Summable.sum_le_tsum _ (fun j _ => pow_nonneg hr0 _) hsum2
        _ = r ^ lo * (1 - r)⁻¹ := hshift
        _ = (1 - r)⁻¹ * r ^ lo := by ring
    calc C * (1 + r) * (∑ k ∈ Finset.Ico lo hi, r ^ k)
        ≤ C * (1 + r) * ((1 - r)⁻¹ * r ^ lo) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = C * (1 + r) * (1 - r)⁻¹ * r ^ lo := by ring
  calc varRho ρ lo hi a
      ≤ ∑ k ∈ Finset.Ico lo hi, ‖a (k + 1) - a k‖ₑ := varRho_le_sum_increments hρ a
    _ ≤ ∑ k ∈ Finset.Ico lo hi, ENNReal.ofReal (C * (1 + r) * r ^ k) :=
        Finset.sum_le_sum fun k _ => hincr k
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico lo hi, C * (1 + r) * r ^ k) :=
        (ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)).symm
    _ ≤ ENNReal.ofReal (C * (1 + r) * (1 - r)⁻¹ * r ^ lo) := ENNReal.ofReal_le_ofReal hgeo

end

end Work.BourgainPlan.Maximal
