import Mathlib
import Submission.Work.SmallBoxSliding.abs_wSmall1Pair_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

/-!
# Fibre measurability of the localised two-body kernel `wSmallPair`

`wSmallPair M ℓ d u h x y` is built from measurable cutoffs/denominators and the numerator
`h (x - y)`.  For the sliding localisation (FS §SmallBoxes) one has to integrate it in the fibre
`y ∈ acube ℓ` against a numerator `h` that is merely *a.e.* measurable for Lebesgue measure, and
conclude that the resulting function of the sliding centre is a.e. strongly measurable.

The measure-theoretic content is:

* `aemeasurable_comp_sub_prod` — if `f` is a.e. measurable for Lebesgue measure and `μ`, `ν` are
  absolutely continuous with respect to Lebesgue measure, then `(x,y) ↦ f (x - y)` is a.e.
  measurable for `μ.prod ν`.  (Pick `g = hf.mk f` measurable, a Lebesgue-null disagreement set
  `B₀`, a *measurable* null superset `B'`, and note that for each `x` the section
  `{y | x - y ∈ B'}` is the image of `B'` under the measure-preserving reflection `y ↦ x - y`.)
* `aestronglyMeasurable_convScaleSmall_diff` — `p ↦ convScaleSmall M c (p.1 - p.2)` is a.e. strongly
  measurable for *any* measure on the product, because `convScaleSmall` is a convolution integral
  and can be written as a Bochner integral of a jointly measurable function.

The remaining factors (`chiSmallB`, `convScale`) are continuous/measurable in the relevant variable,
so the product function is a.e. strongly measurable; `AEStronglyMeasurable.integral_prod_right'`
then gives the fibre measurability.
-/

namespace Work.BoseFixB1

open MeasureTheory
open scoped MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If `f` is a.e. measurable for Lebesgue measure on `ℝ³` and `μ`, `ν` are absolutely continuous
with respect to Lebesgue measure, then `(x, y) ↦ f (x − y)` is a.e. measurable for `μ.prod ν`. -/
lemma aemeasurable_comp_sub_prod {μ ν : Measure ℝ³} [SFinite ν]
    (hμ : μ ≪ (volume : Measure ℝ³)) (hν : ν ≪ (volume : Measure ℝ³))
    {f : ℝ³ → ℝ} (hf : AEMeasurable f (volume : Measure ℝ³)) :
    AEMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2)) (μ.prod ν) := by
  set g : ℝ³ → ℝ := hf.mk f with hgdef
  have hg : Measurable g := hf.measurable_mk
  have hgm : AEMeasurable (fun p : ℝ³ × ℝ³ => g (p.1 - p.2)) (μ.prod ν) :=
    (hg.comp (measurable_fst.sub measurable_snd)).aemeasurable
  refine hgm.congr ?_
  have hB0 : (volume : Measure ℝ³) {x | ¬ (f x = g x)} = 0 :=
    (ae_iff).mp hf.ae_eq_mk
  obtain ⟨B', hB'sub, hB'meas, hB'null⟩ := exists_measurable_superset_of_null hB0
  set Φ : ℝ³ × ℝ³ → ℝ³ := fun p => p.1 - p.2 with hΦdef
  have hCmeas : MeasurableSet (Φ ⁻¹' B') :=
    hB'meas.preimage (measurable_fst.sub measurable_snd)
  have hsec : ∀ x : ℝ³, ν (Prod.mk x ⁻¹' (Φ ⁻¹' B')) = 0 := by
    intro x
    have hset : Prod.mk x ⁻¹' (Φ ⁻¹' B') = (fun y : ℝ³ => x - y) ⁻¹' B' := rfl
    rw [hset]
    refine hν ?_
    rw [(Measure.measurePreserving_sub_left (volume : Measure ℝ³) x).measure_preimage
      hB'meas.nullMeasurableSet]
    exact hB'null
  have hCnull : (μ.prod ν) (Φ ⁻¹' B') = 0 :=
    Measure.measure_prod_null_of_ae_null hCmeas (Filter.Eventually.of_forall hsec)
  have hsub : {p : ℝ³ × ℝ³ | ¬ (g (p.1 - p.2) = f (p.1 - p.2))} ⊆ Φ ⁻¹' B' := by
    intro p hp
    exact hB'sub (fun h => hp h.symm)
  have hz : (μ.prod ν) {p : ℝ³ × ℝ³ | ¬ (g (p.1 - p.2) = f (p.1 - p.2))} = 0 :=
    measure_mono_null hsub hCnull
  exact (ae_iff (μ := μ.prod ν)
    (p := fun p : ℝ³ × ℝ³ => g (p.1 - p.2) = f (p.1 - p.2))).mpr hz

/-- `p ↦ convScaleSmall M c (p.1 - p.2)` is a.e. strongly measurable for any measure on the
product: `convScaleSmall M c` is the convolution integral
`x ↦ ∫ y, χ_M y · χ_M (c⁻¹ • x − y)`, whose integrand is jointly measurable. -/
lemma aestronglyMeasurable_convScaleSmall_diff (M : ℕ) (c : ℝ) (ρ : Measure (ℝ³ × ℝ³)) :
    AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScaleSmall M c (p.1 - p.2)) ρ := by
  have hmeas : Measurable (fun z : ℝ³ => Submission.BoseGases.chiSmall M z) := by
    have h := (Submission.BoseGases.chiSmallBase_continuous M).measurable.div_const
      (Real.sqrt (Submission.BoseGases.chiSmallNormSq M))
    simpa only [Submission.BoseGases.chiSmall] using h
  have harg : Measurable (fun q : (ℝ³ × ℝ³) × ℝ³ => c⁻¹ • (q.1.1 - q.1.2) - q.2) := by
    fun_prop
  have hΦ : Measurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.chiSmall M q.2 *
        Submission.BoseGases.chiSmall M (c⁻¹ • (q.1.1 - q.1.2) - q.2)) :=
    (hmeas.comp measurable_snd).mul (hmeas.comp harg)
  have h := (hΦ.aestronglyMeasurable (μ := ρ.prod (volume : Measure ℝ³))).integral_prod_right'
  refine h.congr ?_
  filter_upwards with p
  simp only [Submission.BoseGases.convScaleSmall, Submission.BoseGases.conv3Small]

/-- The uncurried kernel `(z, y) ↦ wSmallPair M ℓ d u f z y` is a.e. strongly measurable for the
product of two copies of `volume.restrict (acube ℓ)`, for an a.e. measurable numerator `f`. -/
lemma aestronglyMeasurable_wSmallPair_prod {ℓ d : ℝ} (M : ℕ) (u : ℝ³) {f : ℝ³ → ℝ}
    (hf : AEMeasurable f (volume : Measure ℝ³)) :
    AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) := by
  have hvol : (volume.restrict (Submission.BoseGases.acube ℓ)) ≪ (volume : Measure ℝ³) :=
    Measure.restrict_le_self.absolutelyContinuous
  have hchiSmall_meas : Measurable (fun z : ℝ³ => Submission.BoseGases.chiSmall M z) := by
    have h := (Submission.BoseGases.chiSmallBase_continuous M).measurable.div_const
      (Real.sqrt (Submission.BoseGases.chiSmallNormSq M))
    simpa only [Submission.BoseGases.chiSmall] using h
  have hchiB_meas : Measurable (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) := by
    have hg : Measurable (fun x : ℝ³ => Submission.BoseGases.chiScale ℓ x *
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
      (Submission.BoseGases.chiScale_continuous ℓ).measurable.mul
        (hchiSmall_meas.comp (by fun_prop : Measurable (fun x : ℝ³ => (ℓ * d)⁻¹ • x - u)))
    simpa only [Submission.BoseGases.chiSmallB] using hg
  have h1 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.1)
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) :=
    (hchiB_meas.comp measurable_fst).aemeasurable
  have h2 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) :=
    (hchiB_meas.comp measurable_snd).aemeasurable
  have h3 : AEMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2))
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) :=
    aemeasurable_comp_sub_prod hvol hvol hf
  have h4 : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) :=
    aestronglyMeasurable_convScaleSmall_diff M (ℓ * d) _
  have h5 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScale ℓ (p.1 - p.2))
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) :=
    ((Submission.BoseGases.convScale_continuous ℓ).measurable.comp
      (measurable_fst.sub measurable_snd)).aemeasurable
  have h6 : AEMeasurable (fun p : ℝ³ × ℝ³ =>
      Submission.BoseGases.chiSmallB M ℓ d u p.1 *
        ((f (p.1 - p.2) / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
          / Submission.BoseGases.convScale ℓ (p.1 - p.2)) *
      Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ))) :=
    (h1.mul ((h3.div h4.aemeasurable).div h5)).mul h2
  exact h6.aestronglyMeasurable.congr (Filter.Eventually.of_forall (fun p => by
    simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]))

theorem aestronglyMeasurable_wSmallPairFibre {ℓ d : ℝ} (M : ℕ) (u : EuclideanSpace ℝ (Fin 3))
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : AEMeasurable f (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    MeasureTheory.AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmallPair M ℓ d u f z y)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
  have h := aestronglyMeasurable_wSmallPair_prod (ℓ := ℓ) (d := d) M u hf
  have h' := h.integral_prod_right'
  simpa using h'

end Work.BoseFixB1
