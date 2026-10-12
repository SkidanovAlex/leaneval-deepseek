import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.latPer_bdd_of_norm_le
import Submission.Work.BoseBoxFock.pinQDl_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxAvgAux` — helpers for the box-average forms of the limit rows

The limit rows `pinQDl` (and their siblings) of the FS §8 pair kernel are computed in
`pinQLimDefs` as **lattice sums** of Fourier samples, and in `pinQDl_eq_const` as `ℓ`-lattice sums
of double integrals.  The *word matching* of the `Q₂` row (`FINDING_PotPairRows_exists.md` §9.14)
needs a third, *position-space* form: the average over the centred box `Λ(ℓ) = acube ℓ` of the
window `χ_ℓ` against the **periodisation** `latPer3`.

This module collects the elementary ingredients of that comparison:

* the geometry of the centred cube (`acube ℓ ⊆ ball 0 (√3 ℓ/2)`, so the difference of two points
  of the cube has norm at most `√3 ℓ`, the validity range of `latPer_eq_sum_finset_of_norm_le`);
* the pointwise expansion `latPer3 ℓ W z = ↑(ℓ³) Σ_{m ∈ latFinSet ℓ R} ↑(W (z + ℓ•latVec m))`
  inside that range;
* the substitution `∫ y, f (c - y) = ∫ y, f y` (reflection about `c/2`, a measure preserving
  isometry);
* the measurability of the *shifted* weight `(w, y) ↦ W (w - y + c)` on the product `ℝ³ × ℝ³`
  (via the quasi-measure-preserving map `(w,y) ↦ w - y + c`, whose one-variable slices are
  measure preserving homeomorphisms);
* the integrability on a product of a bounded function supported in a product of balls
  (the `ℝ³ × ℝ³` analogue of `integrable_of_bdd_of_supp` of `pinQDl_eq_const`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Evenness of the scaled bump -/

/-- The scaled bump `χ_ℓ` is even. -/
lemma chiScale_neg (ℓ : ℝ) (z : E3) :
    Submission.BoseGases.chiScale ℓ (-z) = Submission.BoseGases.chiScale ℓ z := by
  simp only [Submission.BoseGases.chiScale]
  rw [smul_neg, Submission.BoseGases.chi_even]

/-! ## 2. The geometry of the centred cube -/

/-- The centred cube of side `ℓ` is contained in the ball of radius `√3 ℓ / 2`. -/
lemma norm_le_sqrt3_half_of_mem_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : E3}
    (hz : z ∈ Submission.BoseGases.acube ℓ) : ‖z‖ ≤ Real.sqrt 3 * ℓ / 2 := by
  rw [EuclideanSpace.norm_eq]
  have h2 : ∑ i, ‖z.ofLp i‖ ^ 2 ≤ 3 * (ℓ / 2) ^ 2 := by
    calc ∑ i, ‖z.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : ‖z.ofLp i‖ ≤ ℓ / 2 := by
            have h := (Submission.BoseGases.mem_acube_iff ℓ z).mp hz i
            rw [Real.norm_eq_abs]
            exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
          exact pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = 3 * (ℓ / 2) ^ 2 := by simp [Finset.sum_const, Fintype.card_fin]
  calc Real.sqrt (∑ i, ‖z.ofLp i‖ ^ 2) ≤ Real.sqrt (3 * (ℓ / 2) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt 3 * ℓ / 2 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (by positivity)]
        ring

/-- The difference of two points of the centred cube has norm at most `√3 ℓ`. -/
lemma norm_sub_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {w y : E3}
    (hw : w ∈ Submission.BoseGases.acube ℓ) (hy : y ∈ Submission.BoseGases.acube ℓ) :
    ‖w - y‖ ≤ Real.sqrt 3 * ℓ := by
  have h1 := norm_le_sqrt3_half_of_mem_acube hℓ hw
  have h2 := norm_le_sqrt3_half_of_mem_acube hℓ hy
  have h3 : ‖w - y‖ ≤ ‖w‖ + ‖y‖ := norm_sub_le _ _
  linarith

/-- The scaled bump vanishes off the centred cube of side `ℓ`. -/
lemma chiScale_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiScale ℓ z = 0 := by
  refine chiScale_eq_zero_of_half_lt hℓ ?_
  by_contra h
  exact hz (Submission.BoseGases.mem_acube_of_norm_le hℓ.le (le_of_not_gt h))

/-! ## 3. The finite expansion of the periodisation -/

/-- Inside the validity range `‖z‖ ≤ √3 ℓ` the periodisation is the finite sum over
`LatFourier.latFinSet ℓ R`. -/
lemma latPer3_eq_sum_latFinSet {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hW : ∀ z, R < ‖z‖ → W z = 0) {z : E3} (hz : ‖z‖ ≤ Real.sqrt 3 * ℓ) :
    latPer3 ℓ W z
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ LatFourier.latFinSet ℓ R,
          ((W (z + ℓ • latVec m) : ℝ) : ℂ) := by
  rw [latPer3, latPer_eq_sum_finset_of_norm_le hℓ hW hz]

/-! ## 4. The reflection substitution -/

/-- `∫ y, f (c - y) = ∫ y, f y`: the reflection `y ↦ c - y` of `ℝ³` preserves Lebesgue measure. -/
lemma integral_comp_const_sub {c : E3} (f : E3 → ℂ) :
    (∫ y, f (c - y)) = ∫ y, f y := by
  have h1 : (∫ y : E3, f (c - y)) = ∫ y : E3, (fun t => f (-t)) (y - c) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp [sub_eq_add_neg]
  rw [h1]
  trans ∫ t : E3, f (-t)
  · exact integral_sub_right_eq_self (fun t : E3 => f (-t)) c
  · exact integral_neg_eq_self f volume

/-! ## 5. Measurability of the shifted weight on the product -/

/-- The shifted weight `(w, y) ↦ W (w - y + c)` is a.e. strongly measurable on the product
`ℝ³ × ℝ³` as soon as `W` is a.e. strongly measurable on `ℝ³`.

The map `(w,y) ↦ w - y + c` is quasi-measure-preserving: every one-variable slice
`y ↦ w - y + c` is a composition of a translation and a reflection of `ℝ³`, hence measure
preserving (`QuasiMeasurePreserving.prod_of_right`). -/
lemma aestronglyMeasurable_comp_sub_prod {W : E3 → ℝ} (hWm : AEStronglyMeasurable W volume)
    (c : E3) :
    AEStronglyMeasurable (fun p : E3 × E3 => W (p.1 - p.2 + c)) (volume.prod volume) := by
  have hcmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2 + c)
      (volume.prod volume) volume := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_right
      (f := fun p : E3 × E3 => p.1 - p.2 + c) (by fun_prop) ?_
    filter_upwards with w
    have h1 : Measure.QuasiMeasurePreserving (fun y : E3 => -y) volume volume :=
      (Measure.measurePreserving_neg (volume : Measure E3)).quasiMeasurePreserving
    have h2 : Measure.QuasiMeasurePreserving (fun z : E3 => z + (w + c)) volume volume :=
      (measurePreserving_add_right (volume : Measure E3) (w + c)).quasiMeasurePreserving
    have h3 : (fun y : E3 => w - y + c) = (fun z : E3 => z + (w + c)) ∘ (fun y : E3 => -y) := by
      funext y; simp [sub_eq_add_neg]; abel
    rw [h3]; exact h2.comp h1
  exact hWm.comp_quasiMeasurePreserving hcmp

/-! ## 6. Integrability on the product of a bounded, compactly supported function -/

/-- A bounded a.e. strongly measurable function on `ℝ³ × ℝ³` vanishing outside the ball of
radius `ρ` in its first variable and outside the ball of radius `σ` in its second variable is
integrable.  (The `ℝ³ × ℝ³` analogue of `integrable_of_bdd_of_supp` of `pinQDl_eq_const`.) -/
lemma integrable_prod_of_bdd_of_supp {f : E3 × E3 → ℂ} {ρ σ : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.prod volume))
    (hb : ∃ C, ∀ p, ‖f p‖ ≤ C)
    (hs1 : ∀ p, ρ < ‖p.1‖ → f p = 0) (hs2 : ∀ p, σ < ‖p.2‖ → f p = 0) :
    Integrable f (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hb
  have hsupp : Function.support f ⊆
      Metric.closedBall (0 : E3) ρ ×ˢ Metric.closedBall (0 : E3) σ := by
    intro p hp
    rw [Set.mem_prod]
    constructor
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      by_contra h
      exact hp (hs1 p (lt_of_not_ge h))
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      by_contra h
      exact hp (hs2 p (lt_of_not_ge h))
  have hcomp : HasCompactSupport f :=
    IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : E3) ρ).prod (isCompact_closedBall (0 : E3) σ))
      (isClosed_tsupport f)
      (closure_minimal hsupp (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall))
  have hmemLp : MemLp f 2 (volume.prod volume) :=
    hcomp.memLp_of_bound hmeas (max C 0)
      (Filter.Eventually.of_forall (fun p => le_trans (hC p) (le_max_left C 0)))
  haveI :
      IsFiniteMeasure ((volume.prod volume).restrict
        (Metric.closedBall (0 : E3) ρ ×ˢ Metric.closedBall (0 : E3) σ)) := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top measure_closedBall_lt_top measure_closedBall_lt_top).ne
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    ((hmemLp.restrict _).integrable (q := 2) (by norm_num))

end Work.BoseBoxFock
