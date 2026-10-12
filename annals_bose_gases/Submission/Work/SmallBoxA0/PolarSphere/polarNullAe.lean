import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxBridge.Kernel.lintegralPolarR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0.PolarSphere

open MeasureTheory
open scoped ENNReal Pointwise

/-- The `volume.toSphere`-measure of the spherical slice `r⁻¹ M` of a set `M ⊆ ℝ³`. -/
noncomputable def polarSlice (M : Set (EuclideanSpace ℝ (Fin 3))) (r : ℝ) : ℝ≥0∞ :=
  (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere
    {ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      (r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)) ∈ M}

/-- For a measurable `M` the spherical-slice measure `r ↦ polarSlice M r` is a measurable
function of the radius: it is the `Prod.mk`-section of the measurable set
`{(r, ω) | r • ω ∈ M} ⊆ ℝ × S²`. -/
lemma measurable_polarSlice (M : Set (EuclideanSpace ℝ (Fin 3))) (hM : MeasurableSet M) :
    Measurable (polarSlice M) := by
  have hP : MeasurableSet {q : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      (q.1 : ℝ) • (q.2 : EuclideanSpace ℝ (Fin 3)) ∈ M} :=
    hM.preimage (by fun_prop)
  have hm := measurable_measure_prodMk_left
    (ν := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) hP
  exact hm

/-- **Polar Fubini, positive radii.**  If `M ⊆ ℝ³` is measurable and Lebesgue-null, then for
almost every radius `r > 0` the spherical slice `r⁻¹ M` has zero `volume.toSphere`-measure.

This is the Fubini statement for the polar-coordinate decomposition
`volume = volume.toSphere ⊗ volumeIoiPow 2` (`Work.SmallBoxBridge.Kernel.lintegralPolarR3`):
the null set `M` corresponds to a `toSphere ⊗ volumeIoiPow 2`-null subset of `S² × (0,∞)`,
hence almost every radial section is null; the strictly positive density `r ↦ r²` of
`volumeIoiPow 2` w.r.t. Lebesgue measure on `(0,∞)` then lets us conclude for Lebesgue-a.e. `r`. -/
lemma polarSlice_null_Ioi {M : Set (EuclideanSpace ℝ (Fin 3))} (hM : MeasurableSet M)
    (hM0 : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) M = 0) :
    ∀ᵐ r ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))), polarSlice M r = 0 := by
  change ∀ᵐ r ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))),
    (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere
      {ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
        (r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)) ∈ M} = 0
  -- The two copies of the "polar graph" of `M`, in the two possible orders of the factors.
  set P' : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0:ℝ)) :=
    {b | (b.2 : ℝ) • (b.1 : EuclideanSpace ℝ (Fin 3)) ∈ M} with hP'def
  set P : Set (Set.Ioi (0:ℝ) × Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    {b | (b.1 : ℝ) • (b.2 : EuclideanSpace ℝ (Fin 3)) ∈ M} with hPdef
  have hP'm : MeasurableSet P' := by
    rw [hP'def]; exact hM.preimage (by fun_prop)
  have hPm : MeasurableSet P := by
    rw [hPdef]; exact hM.preimage (by fun_prop)
  -- Polar coordinates: the lower integral of the indicator of `M` is the product measure of `P'`.
  have key := Work.SmallBoxBridge.Kernel.lintegralPolarR3
    (g := M.indicator (1 : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞))
  have hL : ∫⁻ p, M.indicator (1 : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) p
      ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) = 0 := by
    rw [lintegral_indicator_one hM]; exact hM0
  rw [hL] at key
  have hR' : ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.prod
      (Measure.volumeIoiPow 2)) P' = 0 := by
    rw [← key.symm]
    rw [← lintegral_indicator_one hP'm]
    apply lintegral_congr
    intro b
    show M.indicator 1 ((b.2 : ℝ) • (b.1 : EuclideanSpace ℝ (Fin 3))) = P'.indicator 1 b
    by_cases hb : ((b.2 : ℝ) • (b.1 : EuclideanSpace ℝ (Fin 3))) ∈ M
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (show b ∈ P' from hb)]
      rfl
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (show b ∉ P' from hb)]
  -- Swap the two factors: `(volumeIoiPow 2).prod volume.toSphere P = 0`.
  have hP : (Measure.volumeIoiPow 2).prod
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) P = 0 := by
    rw [← Measure.prod_swap (μ := (MeasureTheory.volume :
      Measure (EuclideanSpace ℝ (Fin 3))).toSphere) (ν := Measure.volumeIoiPow 2)]
    rw [Measure.map_apply measurable_swap hPm]
    have : Prod.swap ⁻¹' P = P' := rfl
    rw [this]
    exact hR'
  -- Fubini: almost every radial section of `P` is `volume.toSphere`-null.
  have hae : (fun r : Set.Ioi (0:ℝ) =>
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)
        (Prod.mk r ⁻¹' P)) =ᵐ[Measure.volumeIoiPow 2] 0 :=
    Measure.measure_ae_null_of_prod_null hP
  -- `volumeIoiPow 2` is Lebesgue measure on `(0,∞)` with strictly positive density `r ↦ r²`.
  have hd : AEMeasurable (fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal (r.1 ^ 2))
      (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)) := by fun_prop
  have hne : ∀ᵐ x ∂(Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)),
      (fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal (r.1 ^ 2)) x ≠ 0 := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (show (0:ℝ) < x.1 from x.2) 2
  have hconv : (fun r : Set.Ioi (0:ℝ) =>
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)
        (Prod.mk r ⁻¹' P)) =ᵐ[Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)] 0 := by
    rw [show Measure.volumeIoiPow 2
        = (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)).withDensity
            (fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal (r.1 ^ 2)) from rfl] at hae
    exact (withDensity_ae_eq hd hne).mp hae
  refine (ae_restrict_iff_subtype measurableSet_Ioi).mpr ?_
  exact hconv

/-- If `M ⊆ ℝ³` is measurable and Lebesgue-null, then for almost every radius `r` the sphere
`r⁻¹ M` (i.e. `{ω ∈ S² | r • ω ∈ M}`) has zero `volume.toSphere`-measure. -/
theorem polarNullAe {M : Set (EuclideanSpace ℝ (Fin 3))} (hM : MeasurableSet M)
    (hM0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) M = 0) :
    ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).toSphere
        {ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
          (r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)) ∈ M} = 0 := by
  change ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), polarSlice M r = 0
  have hM' := measurable_polarSlice M hM
  -- Positive radii, from the polar Fubini lemma applied to `M`.
  have hA := polarSlice_null_Ioi hM hM0
  -- Negative radii, from the same lemma applied to the (also null) set `-M = (-1) • M`.
  have hB := polarSlice_null_Ioi (M := -M) hM.neg (by rw [Measure.measure_neg, hM0])
  have hsym : ∀ r : ℝ, polarSlice (-M) r = polarSlice M (-r) := by
    intro r
    simp only [polarSlice]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_neg]
    rw [neg_smul]
  have h1 : ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), 0 < r → polarSlice M r = 0 :=
    (ae_restrict_iff' measurableSet_Ioi).mp hA
  have h2a : ∀ᵐ r ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)),
      polarSlice M (-r) = 0 := by
    refine hB.mono fun r hr => ?_
    rwa [hsym r] at hr
  -- Change variables `r ↦ -r`, converting the a.e. statement on `(0,∞)` to one on `(-∞,0)`.
  have h2b : ∀ᵐ y ∂Measure.map Neg.neg ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)),
      polarSlice M y = 0 :=
    (ae_map_iff (μ := (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) (f := Neg.neg)
      measurable_neg.aemeasurable (p := fun y => polarSlice M y = 0) (by
        have : {y : ℝ | polarSlice M y = 0} = polarSlice M ⁻¹' {0} := rfl
        rw [this]; exact hM' (measurableSet_singleton 0))).mpr h2a
  have hmapIoi : Measure.map Neg.neg ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0))
      = (MeasureTheory.volume : Measure ℝ).restrict (Set.Iio 0) := by
    conv_rhs => rw [← Measure.map_neg_eq_self (MeasureTheory.volume : Measure ℝ),
      measurableEmbedding_neg.restrict_map]
    simp
  rw [hmapIoi] at h2b
  have h2 : ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), r < 0 → polarSlice M r = 0 :=
    (ae_restrict_iff' measurableSet_Iio).mp h2b
  -- Assemble the half-lines; the single point `r = 0` is Lebesgue-null.
  have hne0 : ∀ᵐ r ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), r ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h1, h2, hne0] with r hr1 hr2 hrne
  rcases lt_trichotomy r 0 with h | h | h
  · exact hr2 h
  · exact absurd h hrne
  · exact hr1 h

end Work.SmallBoxA0.PolarSphere
