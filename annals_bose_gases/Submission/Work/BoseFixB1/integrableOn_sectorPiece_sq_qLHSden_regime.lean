import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1B.potGapAdditivityStratum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrableOn_sectorPiece_sq_qLHSden_regime`

The dilute-regime integrability of the sector-piece weighted `qLHSword` diagonal density
`x ↦ qLHSden · (sectorPiece B k Φ)²` over the centred box `abox n ℓ`, where

* `B = dlBox ℓ d u` is the sliding small box,
* `qLHSden n ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u)` is the parenthesised diagonal
  density of FS's localised potential word `qLHSwordB`,
* `sectorPiece B k Φ = 1_{sectorSet B k}·Φ` is the count-`k` sector piece of the state.

This is the `sectorPiece` analogue of the integrability hypothesis (★) of
`Work.BoseFixB1B.potGapAdditivityRegime` (there the weight is the stratum indicator `1_S Φ`); it
is the integrability input needed to split a *signed* multiplication form into its sector
pieces.

## The proof

The weight `(sectorPiece B k Φ)²` is bounded and measurable on the box (the sector set is
measurable, `Work.FockBridge.sectorSet_measurable`, and `Φ` is continuous), so it suffices to
show that the *unweighted* diagonal density `qLHSden` is integrable over the box; multiplying an
`L¹` function by a bounded measurable one preserves integrability
(`MeasureTheory.Integrable.bdd_mul`).

The density splits as the sum of its one-body and two-body halves:

* one-body: each fibre `x ↦ w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)` is *uniformly* bounded under
  the paper's regime (`Work.BoseFixB1B.w1Fibre_bdd`) and a.e. strongly measurable
  (`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre` lifted to the configuration space by
  `Submission.BoseGases.aem_comp_coord'`), so it is integrable over the (finite-measure) box;
* two-body: each slot pair is `Work.BoseFixB1.integrableOn_slot_wSmallPair` at the constant
  weight `S ≡ 1`.

No hypothesis is dropped relative to the request: the assumptions are exactly the paper's.
-/

namespace Work.BoseFixB1

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- A continuous function is bounded on the centred box. -/
private lemma abox_abs_bound_regime {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox n ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

theorem integrableOn_sectorPiece_sq_qLHSden_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} (hM : 1 ≤ M) {ℓ d μ R0 : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hv1 : MeasureTheory.MemLp v 1) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hdR : R0 ≤ ℓ * d / 16) (hdRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    ∀ k : ℕ, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.qLHSden n ℓ μ (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
        * (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ)
    := by
  intro k
  -- ## 1. Each one-body fibre is integrable over the box
  have hvint : Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : E3, R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  have hfibre : ∀ i : Fin n,
      IntegrableOn (fun x : X n => w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) (abox n ℓ) := by
    intro i
    obtain ⟨Cf, _hCf0, hCfb⟩ :=
      Work.BoseFixB1B.w1Fibre_bdd (v := v) h hR0 hv_supp hM hℓ hd hdR hdRχ u
    have hg0 : AEMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
      (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
    have hFm : AEStronglyMeasurable (fun z : E3 => w1Fibre ℓ (wSmall1Pair h M ℓ d u) z)
        (volume.restrict (acube ℓ)) := by
      have hh := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
      simpa only [wSmall1Pair, w1Fibre] using hh
    exact IntegrableOn.of_bound (abox_lt_top n ℓ hℓ.le)
      (Submission.BoseGases.aem_comp_coord' (N := n) (ℓ := ℓ) i hFm) Cf
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact hCfb (x i)))
  -- ## 2. Each two-body slot term is integrable over the box
  have hpair : ∀ p ∈ pairSet n,
      IntegrableOn (fun x : X n => wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox n ℓ) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have h1 := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := n) (ℓ := ℓ) (d := d) (R := R0)
      hℓ hd hvint hvsupp hM hdR hdRχ u hne (S := fun _ : X n => (1 : ℝ))
      aestronglyMeasurable_const (B := 1) zero_le_one
      (Filter.Eventually.of_forall (fun x => by simp))
    simpa using h1
  -- ## 3. The unweighted diagonal density is integrable over the box
  have hsum1 : IntegrableOn (fun x : X n =>
      ∑ i : Fin n, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) (abox n ℓ) :=
    integrable_finsetSum Finset.univ (fun i _ => hfibre i)
  have hsum2 : IntegrableOn (fun x : X n =>
      ∑ p ∈ pairSet n, wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox n ℓ) :=
    integrable_finsetSum (pairSet n) (fun p hp => hpair p hp)
  have hden : IntegrableOn (fun x : X n =>
      qLHSden n ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) x) (abox n ℓ) := by
    have hcomb := (hsum1.const_mul (-μ)).add (hsum2.const_mul (1 / 2 : ℝ))
    refine hcomb.congr ?_
    filter_upwards with x
    simp only [qLHSden, Pi.add_apply]
  -- ## 4. The sector piece and its square are measurable and bounded on the box
  obtain ⟨C, hC0, hCb⟩ := abox_abs_bound_regime (n := n) hℓ hΦc
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hWm : Measurable (sectorPiece (dlBox ℓ d u) k Φ) :=
    hΦc.measurable.indicator (sectorSet_measurable (dlBox ℓ d u) hA k)
  have hWb : ∀ x ∈ abox n ℓ, |sectorPiece (dlBox ℓ d u) k Φ x| ≤ C := by
    intro x hx
    by_cases hxs : x ∈ sectorSet (dlBox ℓ d u) k
    · rw [sectorPiece, Set.indicator_of_mem hxs]
      exact hCb x hx
    · rw [sectorPiece, Set.indicator_of_notMem hxs, abs_zero]
      exact hC0
  have hW2m : AEStronglyMeasurable
      (fun x : X n => (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2)
      (volume.restrict (abox n ℓ)) :=
    (hWm.pow_const 2).aestronglyMeasurable
  have hW2b : ∀ᵐ x ∂(volume.restrict (abox n ℓ)),
      |(sectorPiece (dlBox ℓ d u) k Φ x) ^ 2| ≤ C ^ 2 := by
    rw [ae_restrict_iff' (abox_measurable n ℓ)]
    apply ae_of_all
    intro x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2
        = |sectorPiece (dlBox ℓ d u) k Φ x| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hWb x hx) 2
  -- ## 5. Multiply the integrable density by the bounded measurable sector weight
  have hprod : Integrable (fun x : X n =>
      (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2
        * qLHSden n ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) x)
      (volume.restrict (abox n ℓ)) :=
    hden.bdd_mul hW2m hW2b
  refine hprod.congr ?_
  filter_upwards with x
  ring

end Work.BoseFixB1
