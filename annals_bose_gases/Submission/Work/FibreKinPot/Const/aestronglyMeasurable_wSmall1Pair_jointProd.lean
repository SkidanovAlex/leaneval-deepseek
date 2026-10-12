import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FibreWord.SliceAE
import Submission.Work.FibreWord.fibPiece_ae_eq_zero_of_fibMass_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A.e.-strong measurability of the localised one-body kernel on the full `(u,x,y)`-space

The three-variable function

    ((u,x),y) ↦ wSmall1Pair h M L d u x y
      = χ_{B(u)}(x) · (W₁(x−y)/C_L(x−y)) · χ_{B(u)}(y)

(FS eq:HBU localised one-body kernel, `Submission.BoseGases.wSmall1Pair`) is proved
a.e.-strongly-measurable for the product measure

    (volume ⊗ (volume ↾ acube L)) ⊗ (volume ↾ acube L).

The statement is a pure measurability statement: the hypotheses on `v` (support in a ball of
radius `R > 0` and the existence of a scattering solution `h`) are used only to know that
`g₀ v h = v(1−w₀)` is *integrable* (`Submission.BoseGases.g0_integrable`), hence
a.e.-measurable; `L > 0` and `d > 0` are not needed (they are carried by the requester's
interface).

Structure of the argument.

* The two `chiSmallB` factors are **continuous** functions of `(u,x)` resp. `(u,y)`
  (`chiScale_continuous`, `chiSmall_continuous`), hence measurable.
* The denominator `convScale L (x−y) = (χ⋆χ)((x−y)/L)` is continuous (`convScale_continuous`),
  and the renormalisation denominator `convScaleSmall M (L·d) (x−y) = (χ_M⋆χ_M)((x−y)/(Ld))`
  is continuous by `conv3Small_continuous` (needs `1 ≤ M`).
* The numerator `(u,x,y) ↦ g₀ v h (x−y)` is only a.e.-measurable (a locally integrable /
  integrable function need not be measurable).  We obtain it in the *larger* measure
  `(volume ⊗ volume) ⊗ (volume ↾ acube L)` from the workspiece lemma
  `Work.UBBInputs7.Finding.aemeasurable_comp_sub_coord₂` (measurable representative +
  translation-invariance of Lebesgue measure) and then **restrict the middle coordinate**
  to `acube L` by monotonicity of `AEMeasurable`/`AEStronglyMeasurable` in the measure
  (`AEStronglyMeasurable.mono_measure`), since
  `volume ↾ acube L ≤ volume` and `.prod` is monotone.
-/

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

theorem aestronglyMeasurable_wSmall1Pair_jointProd {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} {L d R : ℝ} (hM : 1 ≤ M) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hL : 0 < L) (hd : 0 < d) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M L d q.1.1 q.1.2 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube L))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube L))) := by
  have hg0 : Integrable (Submission.BoseGases.g0 v h) (volume : Measure ℝ³) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hnum : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.g0 v h (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
    Work.UBBInputs7.Finding.aemeasurable_comp_sub_coord₂ hg0.aemeasurable L
  have hden : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.convScaleSmall M (L * d) (p.1.2 - p.2)) := by
    have h1 : Continuous (fun p : (ℝ³ × ℝ³) × ℝ³ => (L * d)⁻¹ • (p.1.2 - p.2)) := by fun_prop
    exact (Submission.BoseGases.conv3Small_continuous hM).comp h1
  have hW0 : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.wSmallScaled M (L * d) (Submission.BoseGases.g0 v h) (p.1.2 - p.2))
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
    hnum.div hden.aemeasurable
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
  have hAEM : AEMeasurable (fun p : (ℝ³ × ℝ³) × ℝ³ =>
      Submission.BoseGases.wSmall1Pair h M L d p.1.1 p.1.2 p.2)
      (((volume : Measure ℝ³).prod (volume : Measure ℝ³)).prod
        ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L))) :=
    ((hA.mul hW).mul hC)
  refine AEStronglyMeasurable.mono_measure hAEM.aestronglyMeasurable ?_
  have h1 : ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L)) ≤ (volume : Measure ℝ³) :=
    Measure.restrict_le_self
  have h2 : ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube L)))
      ≤ ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    Measure.prod_mono le_rfl h1
  exact Measure.prod_mono h2 le_rfl

end Work.SmallBoxSliding
