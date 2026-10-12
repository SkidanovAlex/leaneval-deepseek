import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.box_avg`

FS `eq:Quav` at the level of an arbitrary integrable density: averaging the integral over the
moving box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` over all translation parameters `u` recovers the full
integral, `∫_u ∫_{Λ(u)} F = ∫ F`, and `u ↦ ∫_{Λ(u)} F` is integrable.

The point is the exact normalisation: for each fixed `z` the set of `u` with `z ∈ Λ(u)` is a
translate-scaled copy of the centred cube `acube ℓ`, and it has Lebesgue measure exactly `1`
(`z - ℓu ∈ acube ℓ` ⟺ `u ∈ (-ℓ)⁻¹ • (z - acube ℓ)`, scaled volume `(ℓ³)⁻¹ · ℓ³ = 1`), so the
`u`-average of the box indicator is `1` and Fubini–Tonelli gives the claim.

## Contents

* `measurableSet_lamBox`, `measurableSet_tube` — measurability of the moving box and of its
  `u`-tube at a point;
* `volume_tube`, `tube_indicator_integral` — the `u`-tube of a point has volume (and
  indicator integral) exactly `1`;
* `indicator_box_eq`, `norm_indicator_box_eq`, `integral_indicator_lamBox`,
  `integrable_tube_indicator` — the pointwise/`u`-integral bookkeeping;
* `box_avg` — the theorem.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

/-! ## 1. Measurability of the moving box and of its `u`-tube -/

private lemma measurableSet_lamBox (ℓ : ℝ) (u : ℝ³) :
    MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
  have h : Work.BoseKinLoc.lamBox ℓ u = (fun z : ℝ³ => z - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

private lemma measurableSet_tube (ℓ : ℝ) (z : ℝ³) :
    MeasurableSet {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u} := by
  have h : {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u}
      = (fun u : ℝ³ => z - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

/-! ## 2. The `u`-tube of a point has volume exactly one -/

/-- For `z` fixed, the set of translation parameters `u` whose moving box `Λ(u)` contains `z` is
a translate-scaled copy of the centred cube of side `ℓ`, hence has Lebesgue measure `1`. -/
private lemma volume_tube {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ³) :
    (volume : Measure ℝ³) {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u} = 1 := by
  have hset : {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u}
      = (fun u : ℝ³ => (-ℓ) • u) ⁻¹' ((fun w : ℝ³ => w + z) ⁻¹' acube ℓ) := by
    ext u
    show z - ℓ • u ∈ acube ℓ ↔ (-ℓ) • u + z ∈ acube ℓ
    rw [sub_eq_add_neg, neg_smul, add_comm z (-(ℓ • u))]
  rw [hset, Measure.addHaar_preimage_smul]
  · rw [show Module.finrank ℝ ℝ³ = 3 by simp]
    rw [measure_preimage_add_right, acube_volume ℓ (le_of_lt hℓ)]
    have h3 : ((-ℓ : ℝ)) ^ 3 = -(ℓ ^ 3) := by ring
    rw [h3, abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < ℓ ^ 3)]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((ℓ : ℝ) ^ 3)⁻¹)]
    rw [inv_mul_cancel₀ (by positivity : (ℓ : ℝ) ^ 3 ≠ 0), ENNReal.ofReal_one]
  · exact neg_ne_zero.mpr (ne_of_gt hℓ)

/-- The `u`-integral of the tube indicator is `1`. -/
private lemma tube_indicator_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ³) :
    (∫ u : ℝ³, (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z) = 1 := by
  have hfun : (fun u : ℝ³ => (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z)
      = ({u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u}).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ u
    · rw [Set.indicator_of_mem h (fun _ => (1 : ℝ)),
        Set.indicator_of_mem (show u ∈ {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u} from h)
          (fun _ => (1 : ℝ))]
    · rw [Set.indicator_of_notMem h (fun _ => (1 : ℝ)),
        Set.indicator_of_notMem (show u ∉ {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u} from h)
          (fun _ => (1 : ℝ))]
  rw [hfun]
  exact (integral_indicator_one (measurableSet_tube ℓ z)).trans (by
    rw [Measure.real_def, volume_tube hℓ z, ENNReal.toReal_one])

/-- The tube indicator is integrable (its support has measure `1`). -/
private lemma integrable_tube_indicator {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ³) :
    Integrable (fun u : ℝ³ => (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z) := by
  have hfun : (fun u : ℝ³ => (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z)
      = ({u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u}).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ u
    · rw [Set.indicator_of_mem h (fun _ => (1 : ℝ)),
        Set.indicator_of_mem (show u ∈ {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u} from h)
          (fun _ => (1 : ℝ))]
    · rw [Set.indicator_of_notMem h (fun _ => (1 : ℝ)),
        Set.indicator_of_notMem (show u ∉ {u : ℝ³ | z ∈ Work.BoseKinLoc.lamBox ℓ u} from h)
          (fun _ => (1 : ℝ))]
  rw [hfun, integrable_indicator_iff (measurableSet_tube ℓ z)]
  exact integrableOn_const (C := (1 : ℝ)) (by rw [volume_tube hℓ z]; exact ENNReal.one_ne_top)

/-! ## 3. Pointwise bookkeeping -/

private lemma indicator_box_eq (ℓ : ℝ) (F : ℝ³ → ℝ) (u z : ℝ³) :
    (Work.BoseKinLoc.lamBox ℓ u).indicator F z
      = F z * (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z := by
  by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ u
  · rw [Set.indicator_of_mem h F, Set.indicator_of_mem h (fun _ => (1 : ℝ)), mul_one]
  · rw [Set.indicator_of_notMem h F, Set.indicator_of_notMem h (fun _ => (1 : ℝ)), mul_zero]

private lemma norm_indicator_box_eq (ℓ : ℝ) (F : ℝ³ → ℝ) (u z : ℝ³) :
    ‖(Work.BoseKinLoc.lamBox ℓ u).indicator F z‖
      = ‖F z‖ * (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z := by
  by_cases h : z ∈ Work.BoseKinLoc.lamBox ℓ u
  · rw [Set.indicator_of_mem h F, Set.indicator_of_mem h (fun _ => (1 : ℝ)), mul_one]
  · rw [Set.indicator_of_notMem h F, Set.indicator_of_notMem h (fun _ => (1 : ℝ)), mul_zero,
      norm_zero]

/-- The `u`-integral of the box-indicator against `F` is `F z`. -/
private lemma integral_indicator_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ³ → ℝ) (z : ℝ³) :
    (∫ u : ℝ³, (Work.BoseKinLoc.lamBox ℓ u).indicator F z) = F z := by
  have hfun : (fun u : ℝ³ => (Work.BoseKinLoc.lamBox ℓ u).indicator F z)
      = fun u : ℝ³ => F z * (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z :=
    funext (fun u => indicator_box_eq ℓ F u z)
  rw [hfun, integral_const_mul, tube_indicator_integral hℓ z, mul_one]

/-! ## 4. The theorem -/

theorem box_avg {ℓ : ℝ} (hℓ : 0 < ℓ) (F : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ z in Work.BoseKinLoc.lamBox ℓ u, F z) ∧
      (∫ u : EuclideanSpace ℝ (Fin 3), ∫ z in Work.BoseKinLoc.lamBox ℓ u, F z) =
        ∫ z : EuclideanSpace ℝ (Fin 3), F z := by
  classical
  set G : ℝ³ × ℝ³ → ℝ := fun p => (Work.BoseKinLoc.lamBox ℓ p.1).indicator F p.2 with hG
  -- joint a.e.-strong measurability of `(u,z) ↦ 1_{Λ(u)}(z) F z`
  have hG_meas : AEStronglyMeasurable G ((volume : Measure ℝ³).prod volume) := by
    have hpt : G = fun p : ℝ³ × ℝ³ =>
        (acube ℓ).indicator (fun _ => (1 : ℝ)) (p.2 - ℓ • p.1) * F p.2 := by
      funext p
      rw [hG]
      change (Work.BoseKinLoc.lamBox ℓ p.1).indicator F p.2
        = (acube ℓ).indicator (fun _ => (1 : ℝ)) (p.2 - ℓ • p.1) * F p.2
      by_cases h : p.2 - ℓ • p.1 ∈ acube ℓ
      · rw [Set.indicator_of_mem h (fun _ => (1 : ℝ)),
          Set.indicator_of_mem (show p.2 ∈ Work.BoseKinLoc.lamBox ℓ p.1 from h) F, one_mul]
      · rw [Set.indicator_of_notMem h (fun _ => (1 : ℝ)),
          Set.indicator_of_notMem (show p.2 ∉ Work.BoseKinLoc.lamBox ℓ p.1 from h) F, zero_mul]
    rw [hpt]
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((measurable_const.indicator (acube_measurable ℓ)).comp
        (by fun_prop : Measurable fun p : ℝ³ × ℝ³ => p.2 - ℓ • p.1)).aestronglyMeasurable
    · exact hF.aestronglyMeasurable.comp_snd
  -- joint integrability, via the `z`-first form of the Fubini criterion
  have hG_int : Integrable G ((volume : Measure ℝ³).prod volume) := by
    rw [integrable_prod_iff' (f := G) hG_meas]
    constructor
    · filter_upwards with z
      have hfun : (fun u : ℝ³ => G (u, z))
          = fun u : ℝ³ =>
              F z * (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z := by
        funext u
        rw [hG]
        exact indicator_box_eq ℓ F u z
      rw [hfun]
      exact (integrable_tube_indicator hℓ z).const_mul (F z)
    · have hfun : (fun z : ℝ³ => ∫ u : ℝ³, ‖G (u, z)‖) = fun z : ℝ³ => ‖F z‖ := by
        funext z
        have h2 : (fun u : ℝ³ => ‖G (u, z)‖)
            = fun u : ℝ³ =>
                ‖F z‖ * (Work.BoseKinLoc.lamBox ℓ u).indicator (fun _ => (1 : ℝ)) z := by
          funext u
          rw [hG]
          exact norm_indicator_box_eq ℓ F u z
        rw [h2, integral_const_mul, tube_indicator_integral hℓ z, mul_one]
      rw [hfun]
      exact hF.norm
  -- Fubini: the two iterated integrals agree
  have hswap : (∫ u : ℝ³, ∫ z : ℝ³, G (u, z)) = ∫ z : ℝ³, ∫ u : ℝ³, G (u, z) :=
    (integral_prod G hG_int).symm.trans (integral_prod_symm G hG_int)
  refine ⟨?_, ?_⟩
  · refine hG_int.integral_prod_left.congr ?_
    filter_upwards with u
    rw [hG]
    exact integral_indicator (measurableSet_lamBox ℓ u)
  · calc (∫ u : ℝ³, ∫ z in Work.BoseKinLoc.lamBox ℓ u, F z)
        = ∫ u : ℝ³, ∫ z : ℝ³, G (u, z) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          rw [hG]
          exact (integral_indicator (measurableSet_lamBox ℓ u)).symm
      _ = ∫ z : ℝ³, ∫ u : ℝ³, G (u, z) := hswap
      _ = ∫ z : ℝ³, F z := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          rw [hG]
          exact integral_indicator_lamBox hℓ F z

end Work.BoseKinLoc.NeuFrac
