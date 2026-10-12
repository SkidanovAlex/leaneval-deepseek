import ChallengeDeps
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_hopAmgmB1
import Submission.Work.BoseFixB1.Q1FibBound
import Submission.Work.BoseFixB1S.boxCompT_fibrePeelAeB1
import Submission.Work.BoseFixB1S.hopPsideSupplyB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.a0A2QJointHopPeelSumGen` — the weighted hop peel sum

The hopping layer writes the crossing term of the sliding box as a sum over the hopping edges
`p ∈ hopPairSet i` (the disjoint pairs `(S,T)` with `i ∈ S`).  The present lemma is the *weighted*
version of the peel identity of that layer: with an arbitrary coefficient
`H : Finset (Fin N) × Finset (Fin N) → ℝ` on the edges,

    Σᵢ Σ_{p ∈ hopPairSet i} H p · ∫_{abox} (ψ_p)²·fib(xᵢ)
      = (M₁/V) · Σ_{p ∈ disjPairs N} |p.1| · H p · ∫_{abox} (ψ_p)² ,

`ψ_p = boxCompT V A p.1 p.2 Φ`, `V = boxMass ℓ d u`, `A = dlBox ℓ d u`,
`fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u)`, `M₁ = boxM1 ℓ A (wSmall1Pair h M ℓ d u)`.

The mathematics is two lines:

* **the peel** `Work.BoseFixB1S.boxCompT_fibrePeelAeB1`: for `i ∈ p.1` the component `ψ_p` is
  `P_{A,i}`-fixed, so the slot-`i` fibre acts as its box average `κ = M₁/V`:
  `∫_{abox} ψ_p²·fib(xᵢ) = κ·∫_{abox} ψ_p²`;
* **the exchange** `Work.BoseFixB1S.hopSwapSum`: `Σᵢ Σ_{p ∋ i} = Σ_p Σ_{i ∈ p.1}`, and each of the
  `|p.1|` slots contributes the same amount.

Everything reduces to the fibre regularity supplied by `Work.BoseFixB1.q1Fib_aem_bound` (a.e.
strong measurability of the localised fibre on `acube ℓ` plus a uniform bound), which is exactly
the hypothesis pair of the peel.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The edge-sum exchange, with the cardinality of the `P`-part**: for a summand that does not
depend on the slot, the double sum `Σᵢ Σ_{p ∋ i}` is the single sum over the pairs weighted by
`|p.1|`. -/
theorem hopSwapSumCard {N : ℕ} (H : Finset (Fin N) × Finset (Fin N) → ℝ)
    (c : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ i : Fin N, ∑ p ∈ hopPairSet i, H p * c p)
      = ∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * H p * c p := by
  rw [hopSwapSum (f := fun p i => H p * c p)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

theorem a0A2QJointHopPeelSumGen {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
      (H : Finset (Fin N) × Finset (Fin N) → ℝ),
      (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          H p * ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        = (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * H p
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦc H
  -- ## the fibre regularity supplied by the corpus
  obtain ⟨-, ⟨hFibAesm, Cf, hCfnn, hCfb⟩⟩ :=
    Work.BoseFixB1.q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad h (M := M) hM
      hℓ hd hR hRχ u
  have hFibAesm' : MeasureTheory.AEStronglyMeasurable
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    simpa only [Work.BoseFixB1.q1Fib1] using hFibAesm
  have hCfb' : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z| ≤ Cf :=
    fun z _ => by simpa only [Work.BoseFixB1.q1Fib1] using hCfb z
  -- ## the box data
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- ## the peel, edge by edge
  have hpeel : ∀ (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)), p ∈ hopPairSet i →
      (∫ x in Submission.BoseGases.abox N ℓ,
          (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        = (boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ x in Submission.BoseGases.abox N ℓ,
              (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
    intro i p hp
    have hpi : i ∈ p.1 := (mem_hopPairSet.mp hp).2
    have hST : Disjoint p.1 p.2 :=
      Work.BoseFixB1.mem_disjPairs.mp (mem_hopPairSet.mp hp).1
    exact boxCompT_fibrePeelAeB1 (ℓ := ℓ) (V := Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (fib := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Cf := Cf)
      (M1 := boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      hℓ hvol hAmeas hVeq hAc hFibAesm' hCfb' rfl hΦc i hpi hST
  -- ## the assembly
  calc
    (∑ i : Fin N, ∑ p ∈ hopPairSet i,
        H p * ∫ x in Submission.BoseGases.abox N ℓ,
          (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      = ∑ i : Fin N, ∑ p ∈ hopPairSet i,
          H p * ((boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p hp => ?_))
        rw [hpeel i p hp]
    _ = (boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∑ i : Fin N, ∑ p ∈ hopPairSet i,
              H p * ∫ x in Submission.BoseGases.abox N ℓ,
                (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
    _ = (boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * H p
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
        rw [hopSwapSumCard H (fun p => ∫ x in Submission.BoseGases.abox N ℓ,
            (boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2)]

end Work.BoseFixB1S
