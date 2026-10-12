import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseB1Cube.fibSumFibreAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseB1Cube

/-- **The fibre-restriction inequality at a fixed `z`** (the pointwise-in-the-coordinate version of
the target `Work.BoseB1Cube.fibSumFibreGood`): the `u`-integral over the complement of
`goodSet ℓ d μ` of the `(u,y)`-double integral of the localised kernel is dominated by three times
the same quantity with the `u`-integral over the boundary layer
`goodSet ℓ d μ \ interiorSet ℓ d μ` (FS's `m(u) = 4` layer).

Recipe (all ingredients available in `Submission/Work/BoseB1Cube/fibSumFibreAux.lean`):
`Work.BoseB1Cube.uy_swap` turns both sides into `∫ y in acube ℓ, ∫ u in s, wSmall1Pair …`, then
`integral_mono_of_nonneg` in the `y`-variable with
* a.e. nonnegativity of the minorant: `∫ u in Gᶜ, wSmall1Pair … = Kf · ∫ u in Gᶜ, Bl` with
  `0 ≤ Kf h M ℓ d z y` a.e. in `y` (`Work.BoseB1Cube.ae_Kf_nonneg`) and `0 ≤ Bl` everywhere
  (`Work.BoseB1Cube.Bl_nonneg`);
* the pointwise a.e. bound `∫ u in Gᶜ, wSmall1Pair … ≤ 3 * ∫ u in G\I, wSmall1Pair …`, which is
  `Work.BoseB1Cube.uint_le_of_hF1` for `y ∈ acube ℓ` (the case `‖z − y‖ < R` gives the coordinate
  hypothesis `|(z−y)_j| ≤ ℓd/16`, and for `‖z − y‖ ≥ R` the common factor `Kf` vanishes by
  `Work.BoseB1Cube.Kf_eq_zero_of_R_le`);
* integrability of the majorant `y ↦ 3 * ∫ u in G\I, wSmall1Pair h M ℓ d u z y` over
  `volume.restrict (acube ℓ)`: dominate by the integrable function
  `y ↦ 3 * (2 * chiSupAbs^2) * |g0 v h (z - y)|` (`Work.BoseB1Cube.abs_uint_le`), using
  `Integrable.mono'` with the a.e. strong measurability `Work.BoseB1Cube.aestronglyMeasurable_uint_y`
  and `Submission.BoseGases.g0_integrable` pulled back along the measure-preserving `y ↦ z - y`. -/
theorem uint_uint_le_z {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRd : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hF1 : ∀ z y : EuclideanSpace ℝ (Fin 3), z ∈ Submission.BoseGases.acube ℓ →
      y ∈ Submission.BoseGases.acube ℓ →
      (∀ j : Fin 3, |(z - y).ofLp j| ≤ ℓ * d / 16) →
      (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, Work.BoseB1Cube.Bl M ℓ d u z y)
        ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                        \ Work.SmallBoxSliding.interiorSet ℓ d μ),
            Work.BoseB1Cube.Bl M ℓ d u z y))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ Submission.BoseGases.acube ℓ) :
    (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
          ∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u z y) := by
  -- a.e. nonnegativity of the `u`-independent factor (pulled back to the restricted measure)
  have hKfae : ∀ᵐ y ∂((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ)), 0 ≤ Kf h M ℓ d z y :=
    MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self
      (ae_Kf_nonneg hv hvrad hR hv_supp h z)
  -- the Fubini exchanges, on both sides
  have hswap1 := uy_swap hv_supp hR h hM hℓ hd hRd hRχ
    ((Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ) z
  have hswap2 := uy_swap hv_supp hR h hM hℓ hd hRd hRχ
    (Work.SmallBoxSliding.goodSet ℓ d μ \ Work.SmallBoxSliding.interiorSet ℓ d μ) z
  rw [hswap1, hswap2, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · -- nonnegativity of the minorant
    filter_upwards [hKfae] with y hy
    rw [uint_eq h M ℓ d ((Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ) z y]
    exact mul_nonneg hy (integral_nonneg (fun u => Bl_nonneg M ℓ d u z y))
  · -- integrability of the majorant, by domination by `3·2χ²|g₀(z−y)|`
    have hg := Submission.BoseGases.g0_integrable hR hv_supp h
    have hdom : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        3 * (2 * Submission.BoseGases.chiSupAbs ^ 2)
          * |Submission.BoseGases.g0 v h (z - y)|)
        ((volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)) :=
      (((hg.abs.comp_sub_left z).integrableOn).const_mul
        (3 * (2 * Submission.BoseGases.chiSupAbs ^ 2)))
    refine Integrable.mono' hdom ?_ ?_
    · exact ((aestronglyMeasurable_uint_y h hM
          (Work.SmallBoxSliding.goodSet ℓ d μ \ Work.SmallBoxSliding.interiorSet ℓ d μ)
          z).mono_measure MeasureTheory.Measure.restrict_le_self).const_mul 3
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      calc 3 * |∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
              \ Work.SmallBoxSliding.interiorSet ℓ d μ),
            Submission.BoseGases.wSmall1Pair h M ℓ d u z y|
          ≤ 3 * (2 * Submission.BoseGases.chiSupAbs ^ 2
              * |Submission.BoseGases.g0 v h (z - y)|) :=
            mul_le_mul_of_nonneg_left
              (abs_uint_le hv_supp hR h hM hℓ hd hRd hRχ
                (Work.SmallBoxSliding.goodSet ℓ d μ \ Work.SmallBoxSliding.interiorSet ℓ d μ)
                z y) (by norm_num)
        _ = 3 * (2 * Submission.BoseGases.chiSupAbs ^ 2)
              * |Submission.BoseGases.g0 v h (z - y)| := by ring
  · -- the pointwise a.e. fibre bound
    filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.acube_measurable ℓ), hKfae] with y hyA hyK
    exact uint_le_of_hF1 h hF1 hRd hv_supp hz hyA hyK

end Work.BoseB1Cube
