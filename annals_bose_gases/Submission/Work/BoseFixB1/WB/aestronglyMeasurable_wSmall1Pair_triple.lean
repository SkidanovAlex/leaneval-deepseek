import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Joint continuity of the `dℓ`-scale two-factor cutoff `χ_{B(u)}(x)` in the
pair `(u, x)`: `χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is a product of two
compositions of continuous bumps with continuous affine maps. -/
private lemma continuous_chiSmallB_pair (M : ℕ) (hM : 1 ≤ M) (ℓ d : ℝ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d p.1 p.2) := by
  have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ p.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
    (Submission.BoseGases.chiSmall_continuous hM).comp
      ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  have heq : (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d p.1 p.2)
      = fun p => Submission.BoseGases.chiScale ℓ p.2 *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := by
    funext p; rfl
  rw [heq]
  exact h1.mul h2

/-- Continuity of the renormalisation denominator
`convScaleSmall M c z = (χ_M ⋆ χ_M)(z/c)`, a composition of the continuous
self-convolution `conv3Small M` with the continuous dilation `z ↦ c⁻¹ • z`. -/
private lemma continuous_convScaleSmall (M : ℕ) (hM : 1 ≤ M) (c : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.convScaleSmall M c z) :=
  (Submission.BoseGases.conv3Small_continuous hM).comp
    (continuous_id.const_smul c⁻¹)

theorem aestronglyMeasurable_wSmall1Pair_triple {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) := by
  let μ0 : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) := MeasureTheory.volume
  let μ : MeasureTheory.Measure
      (EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) :=
    μ0.prod (μ0.prod μ0)
  -- the difference map `(u, x, y) ↦ x - y` is quasi-measure-preserving
  have hsnd : MeasureTheory.Measure.QuasiMeasurePreserving
      (Prod.snd : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →
        EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) μ (μ0.prod μ0) :=
    Measure.quasiMeasurePreserving_snd
  have hsub : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => q.1 - q.2)
      (μ0.prod μ0) μ0 :=
    quasiMeasurePreserving_sub_of_right_invariant _ _
  have hφ : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        p.2.1 - p.2.2) μ μ0 :=
    hsub.comp hsnd
  -- the scattering numerator `g₀`, only a.e. strongly measurable
  have hg0 : MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.g0 v h) μ0 :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).aestronglyMeasurable
  have hg0sub : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.g0 v h (p.2.1 - p.2.2)) μ :=
    hg0.comp_quasiMeasurePreserving hφ
  -- the two cutoff factors `χ_{B(u)}(x)` and `χ_{B(u)}(y)`
  have hχx : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.chiSmallB M ℓ d p.1 p.2.1) μ :=
    ((continuous_chiSmallB_pair M hM ℓ d).comp
      (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin 3) ×
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) => (p.1, p.2.1)))).aestronglyMeasurable
  have hχy : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.chiSmallB M ℓ d p.1 p.2.2) μ :=
    ((continuous_chiSmallB_pair M hM ℓ d).comp
      (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin 3) ×
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) => (p.1, p.2.2)))).aestronglyMeasurable
  -- the two denominators, both continuous hence measurable
  have hinv1 : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        (Submission.BoseGases.convScaleSmall M (ℓ * d) (p.2.1 - p.2.2))⁻¹) μ :=
    (measurable_inv.comp ((continuous_convScaleSmall M hM (ℓ * d)).comp
      (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin 3) ×
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) => p.2.1 - p.2.2))).measurable).aestronglyMeasurable
  have hinv2 : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        (Submission.BoseGases.convScale ℓ (p.2.1 - p.2.2))⁻¹) μ :=
    (measurable_inv.comp ((Submission.BoseGases.convScale_continuous ℓ).comp
      (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin 3) ×
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) => p.2.1 - p.2.2))).measurable).aestronglyMeasurable
  have hmain : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Submission.BoseGases.chiSmallB M ℓ d p.1 p.2.1 *
          (Submission.BoseGases.g0 v h (p.2.1 - p.2.2) *
            (Submission.BoseGases.convScaleSmall M (ℓ * d) (p.2.1 - p.2.2))⁻¹ *
              (Submission.BoseGases.convScale ℓ (p.2.1 - p.2.2))⁻¹) *
            Submission.BoseGases.chiSmallB M ℓ d p.1 p.2.2) μ :=
    (hχx.mul ((hg0sub.mul hinv1).mul hinv2)).mul hχy
  refine hmain.congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
    Submission.BoseGases.wSmallScaled, div_eq_mul_inv]

end Work.BoseFixB1.WB
