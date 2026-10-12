import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Kinetic

/-- Shorthand for the product measure on the `(u, r)`-space, `u : ℝ³` the box position and
`r : X n` the remaining particles. -/
private abbrev gapBareVol (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :=
  (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))

/-- **Set integrals over the moving box are a.e. strongly measurable in the box position.**

If `F` is jointly a.e. strongly measurable on the product of the parameter space and `ℝ³`, then so
is the moving-box set integral `q ↦ ∫_{Λ(q.1)} F (q, z)`.

The proof rewrites the box integral as the (full-space) integral of `F` cut by the *indicator of
the graph* `{p | p.2 ∈ Λ(p.1.1)}`, which is a measurable subset of the product because
`Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` is the translate by `ℓu` of the fixed centred cube; the
parametrized-integral measurability lemma `AEStronglyMeasurable.integral_prod_right'` then
applies.  No hypothesis on `ℓ` is needed. -/
private theorem aemeasurable_setIntegral_lamBox {ℓ : ℝ} {n : ℕ}
    {F : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hF : MeasureTheory.AEStronglyMeasurable F
      ((gapBareVol n).prod (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ∫ z in Work.BoseKinLoc.lamBox ℓ q.1, F (q, z)) (gapBareVol n) := by
  classical
  -- the graph of the moving box is measurable in the product
  have hSmeas : MeasurableSet
      {p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3) |
        p.2 ∈ Work.BoseKinLoc.lamBox ℓ p.1.1} := by
    change MeasurableSet ((fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
        EuclideanSpace ℝ (Fin 3) => p.2 - ℓ • p.1.1) ⁻¹' Submission.BoseGases.acube ℓ)
    exact (Submission.BoseGases.acube_measurable ℓ).preimage (by measurability)
  have hlam : ∀ q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      MeasurableSet (Work.BoseKinLoc.lamBox ℓ q.1) := fun q => by
    change MeasurableSet
      ((fun z : EuclideanSpace ℝ (Fin 3) => z - ℓ • q.1) ⁻¹' Submission.BoseGases.acube ℓ)
    exact (Submission.BoseGases.acube_measurable ℓ).preimage (by measurability)
  -- measurability of the parametrized integral against the graph indicator
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ∫ z, ({p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
            EuclideanSpace ℝ (Fin 3) | p.2 ∈ Work.BoseKinLoc.lamBox ℓ p.1.1}.indicator F) (q, z))
      (gapBareVol n) :=
    (hF.indicator hSmeas).integral_prod_right'
  refine h1.congr ?_
  filter_upwards with q
  have hpoint : ∀ z, ({p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
        EuclideanSpace ℝ (Fin 3) | p.2 ∈ Work.BoseKinLoc.lamBox ℓ p.1.1}.indicator F) (q, z)
      = (Work.BoseKinLoc.lamBox ℓ q.1).indicator (fun z => F (q, z)) z := by
    intro z
    by_cases hz : z ∈ Work.BoseKinLoc.lamBox ℓ q.1
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem]
      exact hz
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
      exact hz
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_indicator (hlam q)]

theorem gapBare_fibre_aemeasurable {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.gapBare ℓ q.1 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  have hΦm : Measurable Φ := hΦ.continuous.measurable
  -- The box mean `m(q) = |Λ(q.1)|⁻¹∫_{Λ(q.1)}ψ_q`, written on the fixed cube `acube ℓ`.
  have hm0 : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ∫ z in Submission.BoseGases.acube ℓ,
          Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2)))
      (gapBareVol n) := by
    have hjoint : Measurable
        (fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN n i (ℓ • p.1.1 + p.2, p.1.2))) := by
      apply hΦm.comp
      measurability
    have hS2 : MeasurableSet
        {p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3) |
          p.2 ∈ Submission.BoseGases.acube ℓ} :=
      (Submission.BoseGases.acube_measurable ℓ).preimage measurable_snd
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (∫ z, ({p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
              EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.acube ℓ}.indicator
            (fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
              EuclideanSpace ℝ (Fin 3) =>
                Φ (Submission.BoseGases.kcInsN n i (ℓ • p.1.1 + p.2, p.1.2))) (q, z))))
        (gapBareVol n) :=
      (hjoint.indicator hS2).aestronglyMeasurable.integral_prod_right'
    refine h1.congr ?_
    filter_upwards with q
    have hpoint : ∀ z, ({p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
          EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.acube ℓ}.indicator
            (fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
              EuclideanSpace ℝ (Fin 3) =>
                Φ (Submission.BoseGases.kcInsN n i (ℓ • p.1.1 + p.2, p.1.2))) (q, z))
        = (Submission.BoseGases.acube ℓ).indicator
            (fun z => Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))) z := by
      intro z
      by_cases hz : z ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem
            (show (q, z) ∈ {p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
                EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.acube ℓ} from hz),
          Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem
            (show (q, z) ∉ {p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
                EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.acube ℓ} from hz),
          Set.indicator_of_notMem hz]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  have hm : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BSKinetic.bsMean ℓ q.1 (fun z => Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      (gapBareVol n) := by
    have h := hm0.const_mul ((ℓ ^ 3)⁻¹)
    simpa [Work.BSKinetic.bsMean] using h
  -- The mean-free square integrand is jointly a.e. strongly measurable.
  have hF : MeasureTheory.AEStronglyMeasurable
      (fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3) =>
        (Φ (Submission.BoseGases.kcInsN n i (p.2, p.1.2))
          - Work.BSKinetic.bsMean ℓ p.1.1
              (fun z => Φ (Submission.BoseGases.kcInsN n i (z, p.1.2)))) ^ 2)
      ((gapBareVol n).prod (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have hH : Measurable
        (fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN n i (p.2, p.1.2))) := by
      apply hΦm.comp
      measurability
    have hm' : MeasureTheory.AEStronglyMeasurable
        (fun p : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) × EuclideanSpace ℝ (Fin 3) =>
          Work.BSKinetic.bsMean ℓ p.1.1
            (fun z => Φ (Submission.BoseGases.kcInsN n i (z, p.1.2))))
        ((gapBareVol n).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := hm.comp_fst
    exact (hH.aestronglyMeasurable.sub hm').pow 2
  have h2 := aemeasurable_setIntegral_lamBox (ℓ := ℓ) (n := n) hF
  -- identify the moving-box integral with `gapBare` of the fibre
  refine h2.congr ?_
  filter_upwards with q
  simp only [Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]

end Work.BoseKinLoc.Kinetic
