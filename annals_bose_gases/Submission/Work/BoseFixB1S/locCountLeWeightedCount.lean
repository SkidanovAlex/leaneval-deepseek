import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.integrableOn_phi_sq_indicator
import Submission.Work.BoseFixB1S.qInd_pInd_sq_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.locCountLeWeightedCount` — the localised cutoff count against `n₀ + n₊`

The target of this file is the FS count passage at the level of the *smooth* cutoff
`χ_{B(u)}` with a **set** `A` carrying the hypothesis that `χ_{B(u)}` is dominated by
`K·1_A`:

    Σ_i ∫_{abox N ℓ} Φ² · χ_{B(u)}(x i)  ≤  K · (S + Q) ,      S = boxFlatCount,  Q = boxQCount.

The mathematics is one line of Hilbert-space geometry.  The two box projections
`P_i = boxPInd volA A i` and `Q_i = boxQInd volA A i = 1_A(x i)·Φ − P_i` are *complementary*
orthogonal projections of the multiplication operator `M_i : Φ ↦ 1_A(x i)·Φ`, so

    ∫ (1_A(x i)·Φ)²  =  ∫ (P_iΦ)²  +  ∫ (Q_iΦ)²          (`qInd_pInd_sq_split`),

i.e. the box-localised mass of the `i`-th slot splits *without loss* into its condensate and
excited parts.  Summing over `i` and using the pointwise domination `χ ≤ K·1_A` (multiplied by
`Φ² ≥ 0`) gives the statement.  The hypothesis `hK : 0 ≤ K` is not needed for the inequality but
is part of the requested interface.

This file contains the *assembly* (`locCountLeWeightedCount_of_split`), which takes the
per-slot splitting identity and the integrability of the dominating function as hypotheses, and
the final theorem constructed from `Work.BoseFixB1S.qInd_pInd_sq_split` and
`Work.BoseFixB1S.integrableOn_phi_sq_indicator`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- Pointwise: the squared cutoff `(1_A(x i)·Φ x)²` is `(Φ x)²·1_A(x i)` (the indicator takes
only the values `0` and `1`). -/
theorem indicator_mul_phi_sq {N : ℕ} (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
      = (Φ x) ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i) := by
  by_cases h : x i ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- **Assembly.**  From (i) the per-slot projection splitting
`∫(Q_iΦ)² + ∫(P_iΦ)² = ∫(1_A(x i)·Φ)²` and (ii) the integrability of the dominating function
`Φ²·(K·1_A(x i))`, the cutoff count is bounded by `K·(boxFlatCount + boxQCount)`. -/
theorem locCountLeWeightedCount_of_split {N : ℕ} {ℓ volA K : ℝ} (hℓ : 0 < ℓ)
    (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {M : ℕ} {d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hK : 0 ≤ K)
    (hχ : ∀ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ K * A.indicator (fun _ => (1 : ℝ)) x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsplit : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
    (hint : ∀ i : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (K * A.indicator (fun _ => (1 : ℝ)) (x i)))
      (Submission.BoseGases.abox N ℓ)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ K * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          + Work.BoseFixB1S.boxQCount volA ℓ A Φ) := by
  have hper : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ K * ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            + (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) := by
    intro i
    have hmono : (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * (K * A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ))
        (f := fun x : Submission.BoseGases.X N =>
          (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
        (g := fun x : Submission.BoseGases.X N =>
          (Φ x) ^ 2 * (K * A.indicator (fun _ => (1 : ℝ)) (x i)))
        (ae_of_all _ fun x => mul_nonneg (sq_nonneg _)
          (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i)))
        (hint i)
        (ae_of_all _ fun x => mul_le_mul_of_nonneg_left (hχ (x i)) (sq_nonneg _))
    calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x) ^ 2 * (K * A.indicator (fun _ => (1 : ℝ)) (x i)) := hmono
      _ = K * ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x) ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i) := by
          rw [← MeasureTheory.integral_const_mul]
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = K * ∫ x in Submission.BoseGases.abox N ℓ,
            (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
          congr 1
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
            (indicator_mul_phi_sq A i Φ x).symm)
      _ = K * ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            + (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) := by
          rw [hsplit i]
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ∑ i : Fin N, K * ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) :=
        Finset.sum_le_sum fun i _ => hper i
    _ = K * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          + Work.BoseFixB1S.boxQCount volA ℓ A Φ) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount,
          Finset.sum_add_distrib]
        exact add_comm _ _

theorem locCountLeWeightedCount {N : ℕ} {ℓ volA K : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {M : ℕ} {d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hK : 0 ≤ K)
    (hχ : ∀ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ K * A.indicator (fun _ => (1 : ℝ)) x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ K * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          + Work.BoseFixB1S.boxQCount volA ℓ A Φ) :=
  locCountLeWeightedCount_of_split hℓ hvol hA hvolA hAc hK hχ hΦc
    (fun i => qInd_pInd_sq_split hℓ hvol hA hvolA hAc i hΦc)
    (fun i => integrableOn_phi_sq_indicator hℓ hA hAc i hΦc)

end Work.BoseFixB1S
