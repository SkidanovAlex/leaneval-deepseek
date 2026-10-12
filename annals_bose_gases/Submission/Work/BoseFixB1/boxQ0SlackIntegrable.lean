import ChallengeDeps
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1.integrableOn_wSmallPair_cube
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

/-- **Integrability of the two `q₀`-slack kernels over the sliding small box.**

Both statements are consequences of the two pointwise domination lemmas of the
dilute regime:

* `wSmallPair M ℓ d u (g₂ v h)` is dominated by a *constant* times
  `|g₂ v h (x−y)|` (`abs_wSmallPair_le` + the global bound `χ_M ≤ chiSmallDecay M`),
  and `|g₂ v h (x−y)|` is integrable over the product of two finite Lebesgue
  restrictions (`integrable_comp_sub_prod`); this is the content of
  `integrableOn_wSmallPair_cube` on `acube ℓ ×ˢ acube ℓ`, and `dlBox ℓ d u` is a
  subset of `acube ℓ`, so restricting the measure gives the product `dlBox ×ˢ dlBox`;
* the `y`-fibre of `wSmall1Pair h M ℓ d u` over `acube ℓ` is *uniformly* bounded by
  the constant of `wSmall1Pair_fibre_abs_le`, so `w1Fibre ℓ (wSmall1Pair h M ℓ d u)`
  is integrable on the finite-measure set `dlBox ℓ d u` by `Integrable.mono'` against
  the constant function; a.e. strong measurability comes from
  `aestronglyMeasurable_wSmallPairFibre` (the fibre integral of an a.e. measurable
  numerator). -/
theorem boxQ0SlackIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u))
    ∧ MeasureTheory.IntegrableOn
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
        (Submission.BoseGases.dlBox ℓ d u) MeasureTheory.volume := by
  have hg2int : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  have hg2supp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  have hboxsub : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    fun x hx => hx.1
  refine ⟨?_, ?_⟩
  · -- pair kernel: integrable on the centred cube product, hence on the sliding box product
    have hbig : MeasureTheory.IntegrableOn
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
      integrableOn_wSmallPair_cube (f := Submission.BoseGases.g2 v h)
        hg2int hg2supp hM hℓ hd hR hRχ u
    refine MeasureTheory.Integrable.mono_measure hbig ?_
    exact Measure.restrict_mono
      (Set.prod_mono Set.inter_subset_left Set.inter_subset_left) le_rfl
  · -- one-body fibre: uniform bound + a.e. strong measurability on the finite set `dlBox`
    change MeasureTheory.Integrable
        (fun z : EuclideanSpace ℝ (Fin 3) => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.dlBox ℓ d u))
    have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    have hle : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.dlBox ℓ d u)
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ) :=
      Measure.restrict_mono hboxsub le_rfl
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.dlBox ℓ d u)) :=
      (aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
        hg0int.aemeasurable).mono_measure hle
    have hfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
      lt_of_le_of_lt (measure_mono hboxsub)
        (Submission.BoseGases.acube_lt_top ℓ (le_of_lt hℓ))
    haveI : IsFiniteMeasure
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.dlBox ℓ d u)) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hfin⟩
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z : EuclideanSpace ℝ (Fin 3),
        |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| ≤ C :=
      ⟨_, fun z => wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
        hM hℓ hd hR hRχ u z⟩
    refine MeasureTheory.Integrable.of_bound haesm C ?_
    filter_upwards with z
    simpa only [Real.norm_eq_abs] using hC z

end Work.BoseFixB1
