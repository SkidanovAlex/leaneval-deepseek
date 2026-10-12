import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.boxPIndFibreMassB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.measurable_w1Fibre`

Measurability of the localised one-body fibre of the sliding small-box kernel,

  `z ↦ w1Fibre ℓ (wSmall1Pair h M ℓ d u) z = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy`.

## The mathematical point (why `Measurable`, not merely `AEMeasurable`)

The corpus only knows that the numerator `g₀ v h = v(1−w₀)` is *locally integrable* (it is the
`rhs_integrable` field of `IsScatteringSolution`, transported by `g0_integrable`), hence only
**a.e.** strongly measurable.  Accordingly `Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`
delivers only a.e. strong measurability of the fibre for `volume.restrict (acube ℓ)`.  That is not
enough here: the requested statement is measurability of the *actual* Bochner integral
`∫_{acube ℓ} w_{1,B(u)}(z,·)`, and a.e. measurability does not upgrade to measurability of a
specific integral expression.

The way out is that the Bochner integral is insensitive to a.e. changes of the integrand:
`MeasureTheory.integral_congr_ae` carries **no** measurability hypotheses.  Concretely, let `G`
be a measurable representative of `g₀ v h` (so `g₀ v h =ᵐ G`, `G` measurable):

* the integral with the *measurable* numerator `G` in place of `g₀ v h` is strongly measurable:
  its joint integrand `(z,y) ↦ χ_{B(u)}(z)·(G(z−y)/D(z−y))·χ_{B(u)}(y)` is measurable, and
  `StronglyMeasurable.integral_prod_right'` applies;
* for **every** `z` the two integrands (the one with `g₀ v h` and the one with `G`) agree a.e. in
  `y`: the disagreement set is the translate-by-`z` of the fixed Lebesgue-null set
  `{g₀ v h ≠ G}`, and `y ↦ z − y` is measure preserving.  Hence by `integral_congr_ae` the two
  integrals agree at *every* `z`, not just a.e.

So the fibre is *literally* the strongly measurable function above, hence measurable.
-/

namespace Work.BoseFixB1

open MeasureTheory

theorem measurable_w1Fibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Measurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) := by
  -- `g₀ v h` is integrable, hence a.e. strongly measurable: take a measurable representative
  have hg0int : Integrable (Submission.BoseGases.g0 v h)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0 : AEMeasurable (Submission.BoseGases.g0 v h)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := hg0int.aemeasurable
  have hGmeas : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 x) := hg0.measurable_mk
  have hGae : Submission.BoseGases.g0 v h =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3)))]
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 x) := hg0.ae_eq_mk
  -- the cutoffs and renormalisation denominators of the localised kernel are continuous,
  -- hence measurable
  have hchiB : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u x) := by
    have hg : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ x *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
      (Submission.BoseGases.chiScale_continuous ℓ).measurable.mul
        ((Submission.BoseGases.chiSmall_continuous hM).measurable.comp
          (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => (ℓ * d)⁻¹ • x - u)))
    simpa only [Submission.BoseGases.chiSmallB] using hg
  have hconv1 : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) x) := by
    have hg : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • x)) :=
      (Submission.BoseGases.conv3Small_continuous hM).measurable.comp
        (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => (ℓ * d)⁻¹ • x))
    simpa only [Submission.BoseGases.convScaleSmall] using hg
  -- the joint integrand with `g₀ v h` replaced by its measurable representative is measurable
  have hjoint : StronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u p.1 *
          ((AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (p.1 - p.2) /
              Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2)) /
            Submission.BoseGases.convScale ℓ (p.1 - p.2)) *
          Submission.BoseGases.chiSmallB M ℓ d u p.2) := by
    have hA : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u p.1) :=
      hchiB.comp measurable_fst
    have hB : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (p.1 - p.2)) :=
      hGmeas.comp (measurable_fst.sub measurable_snd)
    have hC : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2)) :=
      hconv1.comp (measurable_fst.sub measurable_snd)
    have hD : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.convScale ℓ (p.1 - p.2)) :=
      (Submission.BoseGases.convScale_continuous ℓ).measurable.comp
        (measurable_fst.sub measurable_snd)
    have hE : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u p.2) :=
      hchiB.comp measurable_snd
    exact ((hA.mul ((hB.div hC).div hD)).mul hE).stronglyMeasurable
  -- hence the fibre of that joint integrand is strongly measurable
  have hint : StronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ y, (Submission.BoseGases.chiSmallB M ℓ d u z *
          ((AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (z - y) /
              Submission.BoseGases.convScaleSmall M (ℓ * d) (z - y)) /
            Submission.BoseGases.convScale ℓ (z - y)) *
          Submission.BoseGases.chiSmallB M ℓ d u y)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) :=
    hjoint.integral_prod_right'
  -- the actual fibre coincides with that integral at *every* centre `z`
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
        = ∫ y, (Submission.BoseGases.chiSmallB M ℓ d u z *
            ((AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (z - y) /
                Submission.BoseGases.convScaleSmall M (ℓ * d) (z - y)) /
              Submission.BoseGases.convScale ℓ (z - y)) *
            Submission.BoseGases.chiSmallB M ℓ d u y)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)) := by
    intro z
    unfold Submission.BoseGases.w1Fibre Submission.BoseGases.wSmall1Pair
      Submission.BoseGases.wSmallPair Submission.BoseGases.wSmallScaled
    refine integral_congr_ae ?_
    -- the two integrands agree a.e. in `y`, by measure preservation of the reflection `y ↦ z − y`
    have hnull : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        {x : EuclideanSpace ℝ (Fin 3) | ¬ (Submission.BoseGases.g0 v h x =
          AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 x)} = 0 :=
      MeasureTheory.ae_iff.mp hGae
    have hpre : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        ((fun y : EuclideanSpace ℝ (Fin 3) => z - y) ⁻¹'
          {x : EuclideanSpace ℝ (Fin 3) | ¬ (Submission.BoseGases.g0 v h x =
            AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 x)}) = 0 :=
      (Measure.measurePreserving_sub_left
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) z).preimage_null hnull
    have hT : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        {y : EuclideanSpace ℝ (Fin 3) | ¬ (Submission.BoseGases.g0 v h (z - y) =
          AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (z - y))} = 0 :=
      measure_mono_null (fun y hy => hy) hpre
    have hfull : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
        Submission.BoseGases.g0 v h (z - y) =
          AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (z - y) :=
      MeasureTheory.ae_iff.mpr hT
    filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hfull] with y hy
    rw [hy]
  have hgoal : (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      = (fun z : EuclideanSpace ℝ (Fin 3) =>
        ∫ y, (Submission.BoseGases.chiSmallB M ℓ d u z *
            ((AEMeasurable.mk (Submission.BoseGases.g0 v h) hg0 (z - y) /
                Submission.BoseGases.convScaleSmall M (ℓ * d) (z - y)) /
              Submission.BoseGases.convScale ℓ (z - y)) *
            Submission.BoseGases.chiSmallB M ℓ d u y)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ))) :=
    funext hpt
  rw [hgoal]
  exact hint.measurable

end Work.BoseFixB1
