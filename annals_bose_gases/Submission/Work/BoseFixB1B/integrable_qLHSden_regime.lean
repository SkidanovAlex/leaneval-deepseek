import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.integrableOn_sectorPiece_sq_qLHSden_regime
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.integrable_qLHSden_regime`

The dilute-regime integrability of the (unweighted) weighted `qLHSword` diagonal density
`x ↦ qLHSden k ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u)` over the centred box
`abox k ℓ`.

This is the constant-weight (`S ≡ 1`) specialisation of the `hden` step inside
`Work.BoseFixB1.integrableOn_sectorPiece_sq_qLHSden_regime`, exposed as a standalone lemma.
The density splits as the sum of its one-body and two-body halves:

* one-body: each fibre `x ↦ w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)` is *uniformly* bounded
  under the paper's regime (`Work.BoseFixB1B.w1Fibre_bdd`) and a.e. strongly measurable
  (`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre` lifted to the configuration space by
  `Submission.BoseGases.aem_comp_coord'`), so it is integrable over the (finite-measure) box;
* two-body: each slot pair is `Work.BoseFixB1.integrableOn_slot_wSmallPair` at the constant
  weight `S ≡ 1`.

No hypothesis is dropped relative to the paper: the assumptions are exactly the regime's.
-/

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem integrable_qLHSden_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d μ R0 : ℝ}
    (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hv1 : MeasureTheory.MemLp v 1) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hdR : R0 ≤ ℓ * d / 16) (hdRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {k : ℕ} :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X k =>
        Submission.BoseGases.qLHSden k ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) x)
      (Submission.BoseGases.abox k ℓ) := by
  -- ## 1. Each one-body fibre is integrable over the box
  have hvint : Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : E3, R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  have hfibre : ∀ i : Fin k,
      IntegrableOn (fun x : X k => w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) (abox k ℓ) := by
    intro i
    obtain ⟨Cf, _hCf0, hCfb⟩ :=
      Work.BoseFixB1B.w1Fibre_bdd (v := v) h hR0 hv_supp hM hℓ hd hdR hdRχ u
    have hg0 : AEMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
      (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
    have hFm : AEStronglyMeasurable (fun z : E3 => w1Fibre ℓ (wSmall1Pair h M ℓ d u) z)
        (volume.restrict (acube ℓ)) := by
      have hh := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
      simpa only [wSmall1Pair, w1Fibre] using hh
    exact IntegrableOn.of_bound (abox_lt_top k ℓ hℓ.le)
      (Submission.BoseGases.aem_comp_coord' (N := k) (ℓ := ℓ) i hFm) Cf
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact hCfb (x i)))
  -- ## 2. Each two-body slot term is integrable over the box
  have hpair : ∀ p ∈ pairSet k,
      IntegrableOn (fun x : X k => wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox k ℓ) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have h1 := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := k) (ℓ := ℓ) (d := d) (R := R0)
      hℓ hd hvint hvsupp hM hdR hdRχ u hne (S := fun _ : X k => (1 : ℝ))
      aestronglyMeasurable_const (B := 1) zero_le_one
      (Filter.Eventually.of_forall (fun x => by simp))
    simpa using h1
  -- ## 3. The unweighted diagonal density is integrable over the box
  have hsum1 : IntegrableOn (fun x : X k =>
      ∑ i : Fin k, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) (abox k ℓ) :=
    integrable_finsetSum Finset.univ (fun i _ => hfibre i)
  have hsum2 : IntegrableOn (fun x : X k =>
      ∑ p ∈ pairSet k, wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox k ℓ) :=
    integrable_finsetSum (pairSet k) (fun p hp => hpair p hp)
  have hden : IntegrableOn (fun x : X k =>
      qLHSden k ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) x) (abox k ℓ) := by
    have hcomb := (hsum1.const_mul (-μ)).add (hsum2.const_mul (1 / 2 : ℝ))
    refine hcomb.congr ?_
    filter_upwards with x
    simp only [qLHSden, Pi.add_apply]
  exact hden

end Work.BoseFixB1B
