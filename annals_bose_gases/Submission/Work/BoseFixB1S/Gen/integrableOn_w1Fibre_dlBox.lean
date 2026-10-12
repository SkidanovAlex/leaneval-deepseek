import ChallengeDeps
import Submission.Work.BoseFixB1.Q1FibBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.Gen.integrableOn_w1Fibre_dlBox`

The `w₁`-fibre of the localised small-box kernel, restricted to the small box, is integrable:

    z ↦ w1Fibre ℓ (wSmall1Pair h M ℓ d u) z = ∫_{acube ℓ} w_{B(u)}(z,y) dy ,

where `w_{B(u)} = wSmallPair M ℓ d u (g₀ v h)` is the localised two-body kernel.

The route is the *uniform* fibre bound `Work.BoseFixB1.wSmall1Pair_fibre_abs_le`: its right-hand
side is the `L¹`-mass `8π·a v` of `g₀`, smeared by the two cutoff factors, and it is
**independent of `z`** (the `z`-dependent cutoff factor `χ_M((ℓd)⁻¹•z − u)` is bounded by its
global sup `chiSmallDecay M`).  Together with the finiteness of the small-box measure
(`Work.SmallBoxSliding.volume_dlBox_lt_top`, which supplies the `IsFiniteMeasure` instance of
`Integrable.of_bound`), this gives integrability.  Strong measurability is
`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`, on `acube ℓ`, transported to the smaller
set `dlBox ℓ d u ⊆ acube ℓ` by monotonicity of the restricted measure.
-/

namespace Work.BoseFixB1S.Gen

open MeasureTheory

theorem integrableOn_w1Fibre_dlBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Submission.BoseGases.dlBox ℓ d u) := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  -- finiteness of the small-box measure (the `IsFiniteMeasure` instance needed by `of_bound`)
  have hfin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.dlBox ℓ d u)) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))
  -- a.e. strong measurability of the fibre on the small box, obtained from `acube ℓ`
  have hmeas : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.dlBox ℓ d u)) := by
    have h0 := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      hg0.aemeasurable
    refine (h0.mono_measure (Measure.restrict_mono
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) le_rfl)).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair])
  -- the uniform fibre bound closes the goal
  refine MeasureTheory.Integrable.of_bound hmeas
    ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M)
        * (8 * Real.pi * _root_.BoseGases.a v)))
    (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, Submission.BoseGases.w1Fibre]
  simpa only [Submission.BoseGases.wSmall1Pair] using
    Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z

end Work.BoseFixB1S.Gen
