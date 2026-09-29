import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# Definitions for the cleared-Taylor step (STEP 3 of the fine holonomy bound)

The target `Work.Holonomy3.cleared_taylor` identifies the Taylor expansion of the cleared composite
`clearedFun Q ψ N P` with the explicit composition series
`uPoly P * diagComp Φ (auxSeriesC f Q)`.

The passage from the *multivariate* composition series `diagComp Φ (auxSeriesC f Q)` to
*univariate* assertions about each factor `f_{i_s} ∘ Φ_s` needs the univariate formal composition of
power series over `ℂ`; it is defined here by its coefficient formula
`(compPS Φ F).coeff m = ∑_{k ≤ m} F_k · (Φ^k).coeff m`, which is exactly the formula produced by
`coeff_subst` for the substitution `X ↦ Φ` (the terms `k > m` vanish because `Φ` has vanishing
constant coefficient).
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open Filter Topology
open scoped BigOperators

noncomputable section

/-- **Formal composition of univariate power series** `F ∘ Φ = ∑_n F_n · Φ^n`, with the
coefficient of `X^m` written as the (finite) sum over `k ≤ m`. -/
def compPS (Φ F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => ∑ k ∈ Finset.range (m + 1),
    PowerSeries.coeff k F * PowerSeries.coeff m (Φ ^ k)

@[simp]
lemma compPS_coeff (Φ F : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (compPS Φ F) =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k F * PowerSeries.coeff m (Φ ^ k) :=
  PowerSeries.coeff_mk m _

/-- Composition by the zero series: `F ∘ 0 = F(0)`. -/
lemma compPS_zero (F : PowerSeries ℂ) :
    compPS 0 F = PowerSeries.C (PowerSeries.constantCoeff F) := by
  ext m
  rw [compPS_coeff]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  · rw [PowerSeries.coeff_C_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)]
    rw [Finset.sum_eq_single (a := 0) (fun k hk hk0 => by
      simp [zero_pow hk0]) (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h)]
    simp [PowerSeries.coeff_one, if_neg (Nat.pos_iff_ne_zero.mp hm)]

/-- The `m`-th coefficient of `Φ^k` vanishes when `m < k`, for a series `Φ` with vanishing
constant coefficient. -/
lemma coeff_pow_eq_zero_of_lt {Φ : PowerSeries ℂ} (hΦ : PowerSeries.coeff 0 Φ = 0) :
    ∀ {k m : ℕ}, m < k → PowerSeries.coeff m (Φ ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpadd : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rcases Nat.eq_zero_or_pos p.2 with h2 | h2
    · rw [h2, hΦ, mul_zero]
    · have : p.1 < k := by omega
      rw [ih this, zero_mul]

end

end Work.Holonomy3
