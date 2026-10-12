import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs6.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs7.Finding

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Auxiliary lemma** — a.e.-measurability of the composite `((u,a), y) ↦ u₀ (a - y)` on the
triple space `(ℝ³ × ℝ³) × ℝ³`, for an a.e.-measurable `u₀ : ℝ³ → ℝ`.  Same
measurable-representative + null-preimage argument as
`Work.UBBInputs2/aemeasurable_comp_sub_coord`: the composite with a measurable representative is
measurable, and the pointwise difference vanishes off `{p | p.1.2 - p.2 ∈ T}` for a measurable
null `T ⊇ {u₀ ≠ w}`, which is null by Tonelli because every fibre `y ↦ p.1.2 - y` is
measure-preserving. -/
theorem aemeasurable_comp_sub_coord₂ {u : ℝ³ → ℝ}
    (hu : AEMeasurable u (volume : Measure ℝ³)) (L : ℝ) :
    AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ => u (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) := by
  set w : ℝ³ → ℝ := hu.mk u with hwdef
  have hw : Measurable w := by rw [hwdef]; exact hu.measurable_mk
  have huw : u =ᵐ[(volume : Measure ℝ³)] w := by rw [hwdef]; exact hu.ae_eq_mk
  have hφ : Measurable (fun p : (ℝ³ × ℝ³) × ℝ³ => p.1.2 - p.2) := by fun_prop
  refine ((hw.comp hφ).aemeasurable).congr ?_
  have hT0 : (volume : Measure ℝ³) {y | u y ≠ w y} = 0 := by
    simpa using MeasureTheory.ae_iff.mp huw
  obtain ⟨T, hTsub, hTmeas, hTnull⟩ := MeasureTheory.exists_measurable_superset_of_null hT0
  set S : Set ((ℝ³ × ℝ³) × ℝ³) := {p | p.1.2 - p.2 ∈ T} with hSdef
  have hSmeas : MeasurableSet S := hTmeas.preimage hφ
  have hSnull : (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) S = 0 := by
    rw [Measure.prod_apply hSmeas]
    have hfib : ∀ q : ℝ³ × ℝ³,
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))
          (Prod.mk q ⁻¹' S) = 0 := by
      intro q
      have hset : Prod.mk q ⁻¹' S = (fun y : ℝ³ => q.2 - y) ⁻¹' T := by
        rw [hSdef]; ext y; simp
      rw [hset]
      have hpmp : MeasurePreserving (fun y : ℝ³ => q.2 - y)
          (volume : Measure ℝ³) (volume : Measure ℝ³) := by
        convert (Measure.measurePreserving_neg (volume : Measure ℝ³)).comp
          (measurePreserving_sub_right (volume : Measure ℝ³) q.2) using 1
        ext y
        simp [Function.comp, neg_sub]
      have hle : ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))
            ((fun y : ℝ³ => q.2 - y) ⁻¹' T)
          ≤ (volume : Measure ℝ³) ((fun y : ℝ³ => q.2 - y) ⁻¹' T) :=
        Measure.restrict_le_self _
      rw [hpmp.measure_preimage hTmeas.nullMeasurableSet, hTnull] at hle
      exact le_antisymm hle zero_le
    simp only [hfib, lintegral_zero]
  have hsub : {p : (ℝ³ × ℝ³) × ℝ³ | w (p.1.2 - p.2) ≠ u (p.1.2 - p.2)} ⊆ S := by
    intro p hp
    rw [hSdef]
    by_contra hmem
    exact hp (not_not.mp (fun h => hmem (hTsub h))).symm
  have hdiff : (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L)))
        {p | w (p.1.2 - p.2) ≠ u (p.1.2 - p.2)} = 0 :=
    MeasureTheory.measure_mono_null hsub hSnull
  exact MeasureTheory.ae_iff.mpr hdiff

/-- **A.e.-measurability of the localised one-body marginal, in lintegral form.**  Suggested
route: the uncurried function `((u,a), y) ↦ ENNReal.ofReal (wSmall1Pair h M L d u a y) *
1_{acube L}(y)` on `(ℝ³ × ℝ³) × ℝ³` is a.e.-measurable — a product of the continuous factors
`(u,a) ↦ chiSmallB M L d u a` and `(u,y) ↦ chiSmallB M L d u y`, and the quotient whose numerator
is `g0 (a - y)` (handle `g0` by the same measurable-representative + null-preimage argument as
`Work.UBBInputs2/aemeasurable_comp_sub_coord`; `g0` is a.e.-measurable because it is integrable,
`Submission.BoseGases.g0_integrable`) with the continuous denominator
`Submission.BoseGases.convScaleSmall`; then apply `AEMeasurable.lintegral_prod_right` (the
restriction to `acube L` is the measurable indicator of a measurable set). -/
theorem aemeasurable_marginal_lintegral {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {L : ℝ} (hL : 1 ≤ L) {M : ℕ} (hM : 1 ≤ M) {d : ℝ} (hd : 0 < d)
    {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hdR : R0 ≤ (L * d) / 16) :
    AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ∫⁻ y in Submission.BoseGases.acube L,
          ENNReal.ofReal (Submission.BoseGases.wSmall1Pair h M L d q.1 q.2 y))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hg0 : Integrable (Submission.BoseGases.g0 v h) (volume : Measure ℝ³) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hnum : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.g0 v h (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
    aemeasurable_comp_sub_coord₂ hg0.aemeasurable L
  have hden : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.convScaleSmall M (L * d) (p.1.2 - p.2)) := by
    have h1 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        (L * d)⁻¹ • (p.1.2 - p.2)) := by fun_prop
    exact (Submission.BoseGases.conv3Small_continuous hM).comp h1
  have hW0 : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.wSmallScaled M (L * d) (Submission.BoseGases.g0 v h) (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) := by
    have hq : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.g0 v h (p.1.2 - p.2) /
          Submission.BoseGases.convScaleSmall M (L * d) (p.1.2 - p.2))
        (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
          ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
      hnum.div hden.aemeasurable
    exact hq
  have hvc : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.convScale L (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
    ((Submission.BoseGases.convScale_continuous L).comp (by fun_prop)).aemeasurable
  have hW : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.wSmallScaled M (L * d) (Submission.BoseGases.g0 v h) (p.1.2 - p.2)
        / Submission.BoseGases.convScale L (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) := hW0.div hvc
  have hA : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.chiSmallB M L d p.1.1 p.1.2)
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) := by
    have h1 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.chiScale L p.1.2) :=
      (Submission.BoseGases.chiScale_continuous L).comp (by fun_prop)
    have h2 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.chiSmall M ((L * d)⁻¹ • p.1.2 - p.1.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).aemeasurable
  have hC : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.chiSmallB M L d p.1.1 p.2)
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) := by
    have h1 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.chiScale L p.2) :=
      (Submission.BoseGases.chiScale_continuous L).comp (by fun_prop)
    have h2 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.chiSmall M ((L * d)⁻¹ • p.2 - p.1.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).aemeasurable
  have hmain : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.chiSmallB M L d p.1.1 p.1.2 *
        (Submission.BoseGases.wSmallScaled M (L * d) (Submission.BoseGases.g0 v h) (p.1.2 - p.2)
          / Submission.BoseGases.convScale L (p.1.2 - p.2)) *
        Submission.BoseGases.chiSmallB M L d p.1.1 p.2)
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
    (hA.mul hW).mul hC
  have hf : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      ENNReal.ofReal (Submission.BoseGases.wSmall1Pair h M L d p.1.1 p.1.2 p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) := by
    exact hmain.ennreal_ofReal
  exact AEMeasurable.lintegral_prod_right'
    (ν := (volume : Measure ℝ³).restrict (Submission.BoseGases.acube L)) hf

end Work.UBBInputs7.Finding
