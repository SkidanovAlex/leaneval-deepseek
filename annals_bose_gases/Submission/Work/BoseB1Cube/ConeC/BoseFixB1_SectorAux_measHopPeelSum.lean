import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_a0A2QJointHopPeelSumGen
import Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.measHopPeelSum` — the weighted hop peel sum at *measurable* states

The hopping layer of the sliding box writes its crossing term as a sum over the hopping edges
`p ∈ hopPairSet i` (the disjoint pairs `(S,T)` with `i ∈ S`).  The present lemma is the weighted
peel identity of that layer for a state `Φ` that is only *measurable and bounded on the box*
(instead of continuous, which is what `Work.BoseFixB1S.a0A2QJointHopPeelSumGen` assumes):

    Σᵢ Σ_{p ∈ hopPairSet i} H p · ∫_{abox} (ψ_p)²·fib(xᵢ)
      = (M₁/V) · Σ_{p ∈ disjPairs N} |p.1| · H p · ∫_{abox} (ψ_p)² ,

`ψ_p = boxCompT V A p.1 p.2 Φ`, `V = boxMass ℓ d u`, `A = dlBox ℓ d u`,
`fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u)`, `M₁ = boxM1 ℓ A (wSmall1Pair h M ℓ d u)`.

The mathematics is two lines:

* **the peel**: for `i ∈ p.1` the component `ψ_p` is `P_{A,i}`-fixed, so the slot-`i` fibre acts
  as its box average `κ = M₁/V`, i.e. `∫_{abox} ψ_p²·fib(xᵢ) = κ·∫_{abox} ψ_p²`.  The whole
  content of the passage from `Continuous Φ` to `Measurable Φ` + box bound is that the corpus's
  eigenvector rule `boxPInd_boxCompT` is only ever fed the state class
  `GoodState ℓ Φ = Measurable Φ ∧ ∃ C, ∀ x ∈ abox N ℓ, |Φ x| ≤ C`;
  the `GoodState` form `boxPInd_boxCompT_good` is already available (from
  `Work.BoseFixB1.SectorAux.boxCompTOrthMeas`), and `goodState_boxCompT`,
  `peelSlotIndicator` and the integrability of a bounded fibre carry no continuity hypothesis.
* **the exchange** `Work.BoseFixB1S.hopSwapSumCard`: `Σᵢ Σ_{p ∋ i} = Σ_p Σ_{i ∈ p.1}`, and each
  of the `|p.1|` slots contributes the same amount.

The fibre regularity is supplied by `Work.BoseFixB1.q1Fib_aem_bound` (a.e. strong measurability of
the localised fibre on `acube ℓ` plus a uniform bound), which is exactly the hypothesis pair of
the peel.
-/

namespace Work.BoseFixB1.SectorAux

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Integrability of a bounded a.e.-strongly-measurable fibre against the indicator of `A`.**
For `A ⊆ acube ℓ` with `A` measurable (so `A` has finite volume) and `f` a.e. strongly measurable
on the cube and bounded there by `C`, the function `1_A · f` is integrable for the restricted cube
measure.  This is exactly the `hg` hypothesis of `Work.BoseFixB1S.peelSlotIndicator`. -/
private theorem integrable_Aind_mul_of_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A)
    {f : E3 → ℝ} (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ C) :
    Integrable (fun z => Work.BoseFixB1S.Aind A z * f z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  refine Integrable.of_bound ?_ (max C 0) ?_
  · exact (measurable_const.indicator hA).aestronglyMeasurable.mul hfm
  · rw [ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ)]
    apply Filter.Eventually.of_forall
    intro z hz
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hzA : z ∈ A
    · rw [Work.BoseFixB1S.Aind, Set.indicator_of_mem hzA, abs_one, one_mul]
      exact le_trans (hb z hz) (le_max_left _ _)
    · rw [Work.BoseFixB1S.Aind, Set.indicator_of_notMem hzA, abs_zero, zero_mul]
      exact le_max_right _ _

/-- **The (PEEL) identity at the box projections for a `GoodState`.**  This is
`Work.BoseFixB1S.boxCompT_fibrePeelAeB1` with the hypothesis `Continuous Φ` weakened to
`GoodState ℓ Φ` (measurable plus bounded on the box), which is all that the proof consumes. -/
theorem boxCompT_fibrePeelGood {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ)
    {S T : Finset (Fin N)} (i : Fin N) (hi : i ∈ S) (hST : Disjoint S T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A S T Φ x) ^ 2 * fib (x i))
      = (M1 / V) * ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A S T Φ x) ^ 2 := by
  -- `N ≠ 0` and `N = n + 1`, so that the peel `peelSlotIndicator` applies
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- `A` is nonempty, since it has positive volume `V`
  have hAne : A.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, MeasureTheory.measure_empty, ENNReal.toReal_zero] at hVeq
    linarith
  obtain ⟨a₀, ha₀⟩ := hAne
  -- the joint component, as `G`
  set G : Submission.BoseGases.X (n + 1) → ℝ := Work.BoseFixB1S.boxCompT V A S T Φ with hG
  obtain ⟨hGm, CG, hGb⟩ :=
    Work.BoseFixB1S.goodState_boxCompT hℓ hV hA hVeq hAc S T hΦ
  -- the bound `G² ≤ (max CG 0)²` on the box, and measurability of `G²`
  have hCnn : 0 ≤ (max CG 0) ^ 2 := sq_nonneg _
  have hKb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      |(fun x => G x ^ 2) x| ≤ (max CG 0) ^ 2 := by
    intro x hx
    have h1 : |G x| ≤ max CG 0 := le_trans (hGb x hx) (le_max_left _ _)
    show |G x ^ 2| ≤ (max CG 0) ^ 2
    rw [abs_of_nonneg (sq_nonneg (G x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hKm : AEStronglyMeasurable (fun x => G x ^ 2)
      (volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) :=
    (hGm.pow_const 2).aestronglyMeasurable
  -- the fibre is integrable on `A ⊆ acube ℓ`
  have hg1 : Integrable (fun z => Work.BoseFixB1S.Aind A z * fib z)
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    integrable_Aind_mul_of_bound hℓ hA hfibm hfibb
  have hg2 : Integrable (fun z => Work.BoseFixB1S.Aind A z * (1 : ℝ))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    integrable_Aind_mul_of_bound (C := 1) (f := fun _ : E3 => (1 : ℝ)) hℓ hA
      aestronglyMeasurable_const (fun z hz => by simp)
  -- the two peels: against the fibre, and against the constant `1`
  have hpeel1 := Work.BoseFixB1S.peelSlotIndicator (n := n) hℓ hA hAc i
    (g := fib) (K := fun x => G x ^ 2) hg1 hCnn hKm hKb
  have hpeel2 := Work.BoseFixB1S.peelSlotIndicator (n := n) hℓ hA hAc i
    (g := fun _ : E3 => (1 : ℝ)) (K := fun x => G x ^ 2) hg2 hCnn hKm hKb
  -- `G` vanishes where the slot `i` lies outside `A`
  have hzero : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, x i ∉ A → G x = 0 := by
    intro x hx hxi
    have hfix := boxPInd_boxCompT_good hℓ hV hA hVeq hAc S T hΦ i x hx
    rw [if_pos hi] at hfix
    rw [Work.BoseFixB1S.boxPInd_eq V A i G x, Work.BoseFixB1S.Aind,
      Set.indicator_of_notMem hxi, zero_mul] at hfix
    exact hfix.symm
  -- on the peeled configuration the value of `G` is independent of the slot-`i` variable in `A`
  have hconst : ∀ (t : E3), t ∈ A → ∀ r ∈ Submission.BoseGases.abox n ℓ,
      G (Submission.BoseGases.kcInsN n i (t, r))
        = G (Submission.BoseGases.kcInsN n i (a₀, r)) := by
    intro t ht r hr
    have key : ∀ u ∈ A, G (Submission.BoseGases.kcInsN n i (u, r))
        = (1 / V) * ∫ z in A, G (Submission.BoseGases.kcInsN n i (z, r)) := by
      intro u hu
      have hx := Work.BoseFixB1S.kcInsN_mem_abox hAc i hu hr
      have hfix := boxPInd_boxCompT_good hℓ hV hA hVeq hAc S T hΦ i _ hx
      rw [if_pos hi] at hfix
      rw [Work.BoseFixB1S.boxPInd_eq V A i G _,
        Submission.BoseGases.kc_insN_apply_same, Work.BoseFixB1S.Aind,
        Set.indicator_of_mem hu, one_mul, Work.BoseFixB1S.oneMean] at hfix
      have hcongr : (∫ z in A, G (Function.update (Submission.BoseGases.kcInsN n i (u, r)) i z))
          = ∫ z in A, G (Submission.BoseGases.kcInsN n i (z, r)) := by
        apply setIntegral_congr_fun hA
        intro z hz
        simp only [Submission.BoseGases.update_kcInsN]
      rw [hcongr] at hfix
      exact hfix.symm
    rw [key t ht, key a₀ ha₀]
  -- the slotted mass `K2`
  set K2 : ℝ := ∫ r in Submission.BoseGases.abox n ℓ,
    G (Submission.BoseGases.kcInsN n i (a₀, r)) ^ 2 with hK2
  have hK2eq : ∀ t ∈ A, (∫ r in Submission.BoseGases.abox n ℓ,
      G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2) = K2 := by
    intro t ht
    rw [hK2]
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    intro r hr
    simp only [hconst t ht r hr]
  -- the fibre peel, evaluated
  have hfibre : (∫ t in A, fib t * (∫ r in Submission.BoseGases.abox n ℓ,
        G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2)) = M1 * K2 := by
    calc (∫ t in A, fib t * (∫ r in Submission.BoseGases.abox n ℓ,
          G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2))
        = ∫ t in A, fib t * K2 := by
          apply setIntegral_congr_fun hA
          intro t ht
          simp only [hK2eq t ht]
      _ = (∫ t in A, fib t) * K2 := MeasureTheory.integral_mul_const K2 _
      _ = M1 * K2 := by rw [← hM1]
  -- the flat identity
  have hflat : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x ^ 2) = V * K2 := by
    have hL : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x ^ 2)
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (1 : ℝ) * G x ^ 2 := by
      apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable (n + 1) ℓ)
      intro x hx
      by_cases hxi : x i ∈ A
      · show G x ^ 2 = A.indicator (fun _ => (1 : ℝ)) (x i) * (1 : ℝ) * G x ^ 2
        rw [Set.indicator_of_mem hxi]; ring
      · show G x ^ 2 = A.indicator (fun _ => (1 : ℝ)) (x i) * (1 : ℝ) * G x ^ 2
        rw [Set.indicator_of_notMem hxi, hzero x hx hxi]; ring
    rw [hL, hpeel2]
    have h2 : (∫ t in A, (1 : ℝ) * (∫ r in Submission.BoseGases.abox n ℓ,
          G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2)) = ∫ t in A, K2 := by
      apply setIntegral_congr_fun hA
      intro t ht
      show (1 : ℝ) * (∫ r in Submission.BoseGases.abox n ℓ,
        G (Submission.BoseGases.kcInsN n i (t, r)) ^ 2) = K2
      rw [one_mul, hK2eq t ht]
    rw [h2, MeasureTheory.setIntegral_const, smul_eq_mul, hVeq]
    rfl
  -- rewrite the left-hand side as the peel's left-hand side
  have hLHS : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x ^ 2 * fib (x i))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i) * G x ^ 2 := by
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable (n + 1) ℓ)
    intro x hx
    by_cases hxi : x i ∈ A
    · show G x ^ 2 * fib (x i)
          = A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i) * G x ^ 2
      rw [Set.indicator_of_mem hxi]; ring
    · show G x ^ 2 * fib (x i)
          = A.indicator (fun _ => (1 : ℝ)) (x i) * fib (x i) * G x ^ 2
      rw [Set.indicator_of_notMem hxi, hzero x hx hxi]; ring
  rw [hLHS, hpeel1, hfibre, hflat]
  rw [← mul_assoc, div_mul_cancel₀ M1 (ne_of_gt hV)]

/-- **The peel for measurable, box-bounded states**: the form in which the hop sum consumes it.
The `GoodState` input is manufactured from the two hypotheses at hand. -/
theorem measFibrePeelAux {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {M1 : ℝ} (hM1 : M1 = ∫ z in A, fib z)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
    {S T : Finset (Fin N)} (i : Fin N) (hi : i ∈ S) (hST : Disjoint S T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A S T Φ x) ^ 2 * fib (x i))
      = (M1 / V) * ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A S T Φ x) ^ 2 :=
  boxCompT_fibrePeelGood hℓ hV hA hVeq hAc hfibm hfibb hM1
    ⟨hΦm, Cb, hΦb⟩ i hi hST

/-- **The weighted hop peel sum at measurable states.**

    Σᵢ Σ_{p ∈ hopPairSet i} H p · ∫_{abox} (ψ_p)²·fib(xᵢ)
      = (M₁/V) · Σ_{p ∈ disjPairs N} |p.1| · H p · ∫_{abox} (ψ_p)²

with `ψ_p = boxCompT V A p.1 p.2 Φ`, `V = boxMass ℓ d u`, `A = dlBox ℓ d u`,
`fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u)`, `M₁ = boxM1 ℓ A (wSmall1Pair h M ℓ d u)`.

Each edge `(i,p)` with `i ∈ p.1` contributes `κ·∫ψ_p²` (`measFibrePeelAux`), and the exchange
`hopSwapSumCard` reorganises the double sum over `(i,p)` into the single sum over the pairs with
the multiplicity `|p.1|`. -/
theorem measHopPeelSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
      (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
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
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦm Cb hΦb H
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
  have hpeel : ∀ (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)), p ∈ Work.BoseFixB1S.hopPairSet i →
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        = (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
    intro i p hp
    have hpi : i ∈ p.1 := (Work.BoseFixB1S.mem_hopPairSet.mp hp).2
    have hST : Disjoint p.1 p.2 :=
      Work.BoseFixB1.mem_disjPairs.mp (Work.BoseFixB1S.mem_hopPairSet.mp hp).1
    exact measFibrePeelAux (ℓ := ℓ) (V := Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (fib := Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Cf := Cf)
      (M1 := Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      hℓ hvol hAmeas hVeq hAc hFibAesm' hCfb' rfl hΦm hΦb i hpi hST
  -- ## the assembly
  calc
    (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
        H p * ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          H p * ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p hp => ?_))
        rw [hpeel i p hp]
    _ = (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
              H p * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
    _ = (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * H p
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2 := by
        rw [Work.BoseFixB1S.hopSwapSumCard H (fun p =>
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) ^ 2)]

end Work.BoseFixB1.SectorAux
