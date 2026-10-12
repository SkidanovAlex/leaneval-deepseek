import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.pairDevPerPair_le
import Submission.Work.BoseB1Cube.wSmallPair_ne_zero_imp_mem_dlBox
import Submission.Work.BoseFixB1S.sum_pairSet_fst_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.cubeDenseDev_le_pairQCount` — the pair deviation is paid by the excited count

The pair deviation of the dense band arm (`Work.BoseB1Cube.cubeDenseDev`)

    D̃ = ∑_{p ∈ pairSet n} ∫_{abox n ℓ} (Φ − P_{p₁}P_{p₂}Φ)²·w_{B(u)}(x_{p₁},x_{p₂})

at the FS box projections `Pᵢ = Work.UBBInputs8.boxPInd (boxMass) (dlBox) i` is dominated by the
excited count `Σᵢ∫(QᵢΦ)² = boxQCount (boxMass) ℓ (dlBox) Φ`, with the crude constant `4·Kw`:

    D̃ ≤ 4·Kw·((n:ℝ) − 1)·Σᵢ∫(QᵢΦ)²      (|w_{B(u)}| ≤ Kw).

The constant is the exact one of the crude argument: per **ordered** pair `(i,j)` the two-term
split `Φ − P_iP_jΦ = Q_iΦ + P_i(Φ − P_jΦ)` (valid on `{x i ∈ B(u)} ∩ {x j ∈ B(u)}`, which is
a.e. the support of the localised kernel `wSmallPair`), `(a+b)² ≤ 2a² + 2b²`, `|w| ≤ Kw` and the
`L²`-contraction `‖Pᵢψ‖ ≤ ‖ψ‖` give `2·Kw·(∫(QᵢΦ)² + ∫(QⱼΦ)²)`; each index occurs in exactly
`2(n−1)` ordered pairs, so the sum is `2·Kw·2(n−1)·boxQCount`.

This is the "deviation is bounded by the excited count" half of the razor arm: combined with
`Work.BoseFixB1S.deviationLargeOfNotFlatArm`, a large deviation *forces* a large excited count.

The heart is the per-pair estimate `Work.BoseB1Cube.pairDevPerPair_le` and the support statement
`Work.BoseB1Cube.wSmallPair_ne_zero_imp_mem_dlBox`; the summation bookkeeping is
`sum_pairSet_add_eq` below.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The pair-set summation bookkeeping -/

/-- The sum of `g` over the second coordinate of the ordered pair set equals
`(N − 1)·∑ i, g i`. -/
theorem sum_pairSet_snd_eq {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g p.2) = ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  change (∑ x : Fin N, ∑ y : Fin N, (if x ≠ y then g y else 0))
    = ((N : ℝ) - 1) * ∑ i : Fin N, g i
  rw [Finset.sum_comm]
  simp only [ne_comm]
  simp_rw [Work.BoseFixB1S.sum_ite_ne_eq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun y _ => mul_comm (g y) ((N : ℝ) - 1))

/-- Membership in the ordered pair set means the two indices differ. -/
theorem pairSet_ne_of_mem {N : ℕ} {p : Fin N × Fin N}
    (hp : p ∈ Submission.BoseGases.pairSet N) : p.1 ≠ p.2 := by
  simpa [Submission.BoseGases.pairSet, Finset.mem_filter] using hp

/-- **The exact pair-set bookkeeping**: each index occurs in exactly `2(N−1)` ordered pairs, so
`∑_{p ∈ pairSet N} (f p.1 + f p.2) = 2(N−1)·∑ i, f i`. -/
theorem sum_pairSet_add_eq {N : ℕ} (f : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, (f p.1 + f p.2))
      = 2 * ((N : ℝ) - 1) * ∑ i : Fin N, f i := by
  rw [Finset.sum_add_distrib, Work.BoseFixB1S.sum_pairSet_fst_eq f, sum_pairSet_snd_eq f]
  ring

theorem cubeDenseDev_le_pairQCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} {ℓ d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    (hℓ : 0 < ℓ) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) {Kw : ℝ} (hKw : 0 ≤ Kw)
    (hw : ∀ x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmallPair M ℓ d u v x y| ≤ Kw)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hInt : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ)) :
    Work.BoseB1Cube.cubeDenseDev v M ℓ d u n Φ
      ≤ 4 * Kw * ((n : ℝ) - 1)
        * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  rw [Work.BoseB1Cube.cubeDenseDev]
  -- the per-pair estimate (the heart of the argument)
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet n,
      (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
            * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        ≤ 2 * Kw * ((∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 Φ x) ^ 2)
            + (∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ x) ^ 2)) := by
    intro p hp
    exact pairDevPerPair_le (V := Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u) (Φ := Φ)
      (W := Submission.BoseGases.wSmallPair M ℓ d u v)
      hℓ hV (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      hΦc Kw hKw hw
      (fun x y h => wSmallPair_ne_zero_imp_mem_dlBox hℓ hV h)
      (pairSet_ne_of_mem hp)
      (hInt p hp)
  -- the summation bookkeeping, in the exact syntactic shape of the goal
  have hQ : (∑ p ∈ Submission.BoseGases.pairSet n,
        ((∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ x) ^ 2)))
      = 2 * ((n : ℝ) - 1)
        * ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 :=
    sum_pairSet_add_eq (fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
  calc (∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
            * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
      ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
          2 * Kw * ((∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ x) ^ 2)
              + (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ x) ^ 2)) :=
        Finset.sum_le_sum hpair
    _ = 2 * Kw * (∑ p ∈ Submission.BoseGases.pairSet n,
          ((∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ x) ^ 2)
              + (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ x) ^ 2))) :=
        (Finset.mul_sum (Submission.BoseGases.pairSet n)
          (fun p : Fin n × Fin n => ((∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ x) ^ 2)
              + (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ x) ^ 2)))
          (2 * Kw)).symm
    _ = 2 * Kw * (2 * ((n : ℝ) - 1)
          * ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
        rw [hQ]
    _ = 4 * Kw * ((n : ℝ) - 1)
        * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
        rw [Work.BoseFixB1S.boxQCount]
        ring

end Work.BoseB1Cube
