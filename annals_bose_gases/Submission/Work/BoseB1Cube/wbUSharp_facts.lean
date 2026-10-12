import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NomDefs
import Submission.Work.BoseFixB1.WB.aestronglyMeasurable_wbMass
import Submission.Work.BoseFixB1S.integral_wbUSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.wbUSharp_facts`

The four elementary facts about the **sharp sliding one-body potential**

    wbUSharp h μ z = ∫_{I₋} (∬w_{1,B(u)} / |B(u)|) · 1_{B(u)}(z) du

of `Work.BoseFixB1S.BoxNormDefs` (the normaliser of FS `thm:aprioriHLambda` step 4 is the
*sharp* box volume `boxMass`): nonnegativity, a.e. measurability, local integrability on the
big box `Λ = acube ℓ`, and the **sharp sup bound** `U(z) ≤ C (a v)`.

The last one is the reason this exact spelling matters: with the sharp box indicator the
`u`-tube of a point has volume **one** (`boxInd_integral_u`: `∫_u 1_{B(u)}(x) du = 1_{Λ}(x)`),
so dividing `w_{1,B(u)}` by the box **volume** and integrating the indicator against `du`
costs *no* dimensionful factor — the bound is the constant `C (a v)` itself, rather than
`C (a v)·χSupAbs²` as in the `χ_{B(u)}²`-windowed twin `Work.BoseFixB1.WB.U_facts`.

Given the interface bound `hmassU : ∬w_{1,B(u)} ≤ C (a v)·|B(u)|` (which is exactly the
hypothesis supplied by the caller), the pointwise ratio `∬w_{1,B(u)}/|B(u)|` is bounded by
`C (a v)` (also where `|B(u)| = 0`, because there the dominating hypothesis forces
`∬w_{1,B(u)} = 0`), and the rest is the tube identity.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Measurability of the box volume -/

/-- `u ↦ boxMass ℓ d u` is a.e. strongly measurable: it is the `x`-marginal of the jointly
measurable box indicator `(u,x) ↦ 1_{B(u)}(x)` (`AEStronglyMeasurable.integral_prod_right'`,
which needs no integrability hypothesis). -/
private lemma aestronglyMeasurable_boxMass (ℓ d : ℝ) :
    AEStronglyMeasurable (fun u : E3 => Work.SmallBoxSliding.boxMass ℓ d u)
      (volume : Measure E3) := by
  have hjoint : AEStronglyMeasurable
      (fun p : E3 × E3 => Work.SmallBoxSliding.boxInd ℓ d p.1 p.2)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have hind : (fun p : E3 × E3 => Work.SmallBoxSliding.boxInd ℓ d p.1 p.2)
        = {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
            (fun _ => (1 : ℝ)) := by
      funext p
      obtain ⟨u, x⟩ := p
      by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
      · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx,
          Set.indicator_of_mem (show (u, x) ∈
            {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show (u, x) ∉
            {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    rw [hind]
    exact (measurable_const.indicator
      (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)).aestronglyMeasurable
  have h := hjoint.integral_prod_right'
  simpa only [Work.SmallBoxSliding.boxMass] using h

/-- A section of the box indicator is a.e. strongly measurable. -/
private lemma aestronglyMeasurable_boxInd_slice (ℓ d : ℝ) (z : E3) :
    AEStronglyMeasurable (fun u : E3 => Work.SmallBoxSliding.boxInd ℓ d u z)
      (volume : Measure E3) := by
  have hset : MeasurableSet {u : E3 | z ∈ Submission.BoseGases.dlBox ℓ d u} :=
    (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage
      (f := fun u : E3 => (u, z)) (by measurability)
  have hfun : (fun u : E3 => Work.SmallBoxSliding.boxInd ℓ d u z)
      = {u : E3 | z ∈ Submission.BoseGases.dlBox ℓ d u}.indicator (fun _ => (1 : ℝ)) := by
    funext u
    rw [Work.SmallBoxSliding.boxInd]
    by_cases h : z ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show u ∈ {u : E3 | z ∈ Submission.BoseGases.dlBox ℓ d u} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show u ∉ {u : E3 | z ∈ Submission.BoseGases.dlBox ℓ d u} from h)]
  rw [hfun]
  exact (measurable_const.indicator hset).aestronglyMeasurable

/-! ## Integrability of a section of the box indicator -/

/-- **The `u`-section of the box indicator is integrable.**  For `ℓd > 0` and a fixed point `z`
the function `u ↦ 1_{B(u)}(z)` is the indicator of the tube
`T = {u | (ℓd)⁻¹•z − u ∈ acube 1}`, which is a translate of the unit cube up to reflection and
hence has volume `1` (`volume_preimage_sub_acube_one`); a bounded measurable function supported
in a finite-measure set is integrable. -/
private lemma integrable_boxInd_slice {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (z : E3) :
    Integrable (fun u : E3 => Work.SmallBoxSliding.boxInd ℓ d u z) (volume : Measure E3) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hne : ℓ * d ≠ 0 := ne_of_gt hld
  set T : Set E3 := (fun u : E3 => (ℓ * d)⁻¹ • z - u) ⁻¹' Submission.BoseGases.acube 1 with hT
  have hTmeas : MeasurableSet T :=
    measurableSet_preimage (by fun_prop) (Submission.BoseGases.acube_measurable 1)
  have hTvol : (volume : Measure E3) T = 1 := by
    rw [hT]
    exact Work.SmallBoxSliding.volume_preimage_sub_acube_one ((ℓ * d)⁻¹ • z)
  have hunit : Integrable (T.indicator (fun _ => (1 : ℝ))) (volume : Measure E3) := by
    rw [MeasureTheory.integrable_indicator_iff hTmeas]
    change Integrable (fun _ : E3 => (1 : ℝ)) ((volume : Measure E3).restrict T)
    rw [MeasureTheory.integrable_const_iff]
    right
    rw [MeasureTheory.isFiniteMeasure_restrict, hTvol]
    exact ENNReal.one_ne_top
  -- the check that the two indicators of `dlBox` / the unit tube agree
  have hspec : ∀ w : E3, (Submission.BoseGases.acube (ℓ * d)).indicator (fun _ => (1 : ℝ))
        ((ℓ * d) • w) = (Submission.BoseGases.acube 1).indicator (fun _ => (1 : ℝ)) w := by
    intro w
    by_cases hw : w ∈ Submission.BoseGases.acube 1
    · rw [Set.indicator_of_mem ((Work.SmallBoxSliding.smul_mem_acube_iff hld w).mpr hw),
        Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem
          (fun h => hw ((Work.SmallBoxSliding.smul_mem_acube_iff hld w).mp h)),
        Set.indicator_of_notMem hw]
  have hsecond : ∀ u : E3,
      (Submission.BoseGases.acube (ℓ * d)).indicator (fun _ => (1 : ℝ)) (z - (ℓ * d) • u)
        = T.indicator (fun _ => (1 : ℝ)) u := by
    intro u
    rw [show z - (ℓ * d) • u = (ℓ * d) • ((ℓ * d)⁻¹ • z - u) from by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]]
    rw [hspec]
    rw [hT]
    by_cases h : (ℓ * d)⁻¹ • z - u ∈ Submission.BoseGases.acube 1
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show u ∈ (fun u : E3 => (ℓ * d)⁻¹ • z - u) ⁻¹'
          Submission.BoseGases.acube 1 from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show u ∉ (fun u : E3 => (ℓ * d)⁻¹ • z - u) ⁻¹'
          Submission.BoseGases.acube 1 from h)]
  have hpt : ∀ u : E3, Work.SmallBoxSliding.boxInd ℓ d u z
      = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) z
        * T.indicator (fun _ => (1 : ℝ)) u := by
    intro u
    rw [Work.SmallBoxSliding.boxInd_eq_mul]
    rw [hsecond u]
  exact (hunit.const_mul ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) z)).congr
    (Filter.Eventually.of_forall fun u => (hpt u).symm)

/-! ## The four facts -/

theorem wbUSharp_facts {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) {C : ℝ} (hC : 0 ≤ C)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.boxMass
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    (∀ z : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixB1S.wbUSharp h μ z)
      ∧ AEMeasurable (Work.BoseFixB1S.wbUSharp h μ) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      ∧ MeasureTheory.IntegrableOn (Work.BoseFixB1S.wbUSharp h μ)
          (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      ∧ (∀ z : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1S.wbUSharp h μ z ≤ C * (_root_.BoseGases.a v)) := by
  let M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  have hM' : 1 ≤ M := hM
  have hℓ' : 0 < ℓ := hℓ
  have hd' : 0 < d := hd
  have hpos : 0 < _root_.BoseGases.a v := hav
  have hCa : 0 ≤ C * _root_.BoseGases.a v := mul_nonneg hC hpos.le
  have hmassU' : ∀ u : E3, Work.BoseFixB1.wbMass v h μ u
      ≤ C * _root_.BoseGases.a v * Work.SmallBoxSliding.boxMass ℓ d u := hmassU
  have hmnn : ∀ u : E3, 0 ≤ Work.BoseFixB1.wbMass v h μ u :=
    fun u => Work.BoseFixB1.wbMass_nonneg hv hvrad hv_supp hR hM' hℓ' hd' u
  -- ### the pointwise ratio bound, also where the box is empty
  have hratio : ∀ u : E3, Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.boxMass ℓ d u
      ≤ C * _root_.BoseGases.a v := by
    intro u
    rcases eq_or_lt_of_le (boxMass_nonneg' ℓ d u) with h0 | h0
    · -- `|B(u)| = 0` forces `∬w_{1,B(u)} = 0` by the dominating hypothesis
      have hm0 : Work.BoseFixB1.wbMass v h μ u = 0 := by
        refine le_antisymm ?_ (hmnn u)
        have hh := hmassU' u
        rw [← h0, mul_zero] at hh
        exact hh
      rw [hm0, ← h0, zero_div]
      exact hCa
    · rw [div_le_iff₀ h0]
      exact hmassU' u
  -- ### the four facts
  have hnn : ∀ z : E3, 0 ≤ Work.BoseFixB1S.wbUSharp h μ z := by
    intro z
    rw [Work.BoseFixB1S.wbUSharp]
    exact integral_nonneg fun u => mul_nonneg (div_nonneg (hmnn u) (boxMass_nonneg' ℓ d u))
      (boxInd_nonneg' ℓ d u z)
  have hmass_le : ∀ z : E3,
      (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.SmallBoxSliding.boxInd ℓ d u z)
        ≤ 1 := by
    intro z
    have h1 : (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
          Work.SmallBoxSliding.boxInd ℓ d u z)
        ≤ ∫ u : E3, Work.SmallBoxSliding.boxInd ℓ d u z :=
      setIntegral_le_integral (integrable_boxInd_slice hℓ' hd' z)
        (Filter.Eventually.of_forall fun u => boxInd_nonneg' ℓ d u z)
    rw [Work.SmallBoxSliding.boxInd_integral_u hℓ' hd' z] at h1
    refine le_trans h1 ?_
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      norm_num
  have hle : ∀ z : E3, Work.BoseFixB1S.wbUSharp h μ z ≤ C * _root_.BoseGases.a v := by
    intro z
    haveI : IsFiniteMeasure
        ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (Work.BoseFixB1.WB.interiorSet_lt_top hℓ' hd').ne
    have hIntg : Integrable
        (fun u : E3 => (C * _root_.BoseGases.a v) * Work.SmallBoxSliding.boxInd ℓ d u z)
        ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ)) := by
      refine Integrable.of_bound ?_ (C * _root_.BoseGases.a v) (Filter.Eventually.of_forall ?_)
      · exact (AEStronglyMeasurable.const_mul
          (aestronglyMeasurable_boxInd_slice ℓ d z) (C * _root_.BoseGases.a v)).mono_measure
            Measure.restrict_le_self
      · intro u
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hCa, abs_of_nonneg (boxInd_nonneg' ℓ d u z)]
        calc (C * _root_.BoseGases.a v) * Work.SmallBoxSliding.boxInd ℓ d u z
            ≤ (C * _root_.BoseGases.a v) * 1 :=
              mul_le_mul_of_nonneg_left (boxInd_le_one' ℓ d u z) hCa
          _ = C * _root_.BoseGases.a v := mul_one _
    rw [Work.BoseFixB1S.wbUSharp]
    calc (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
          (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.boxMass ℓ d u)
            * Work.SmallBoxSliding.boxInd ℓ d u z)
        ≤ ∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
            (C * _root_.BoseGases.a v) * Work.SmallBoxSliding.boxInd ℓ d u z :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun u =>
              mul_nonneg (div_nonneg (hmnn u) (boxMass_nonneg' ℓ d u)) (boxInd_nonneg' ℓ d u z))
            hIntg
            (Filter.Eventually.of_forall fun u =>
              mul_le_mul_of_nonneg_right (hratio u) (boxInd_nonneg' ℓ d u z))
      _ = (C * _root_.BoseGases.a v) * ∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
            Work.SmallBoxSliding.boxInd ℓ d u z := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (C * _root_.BoseGases.a v) * 1 := mul_le_mul_of_nonneg_left (hmass_le z) hCa
      _ = C * _root_.BoseGases.a v := mul_one _
  have hsmeas : AEStronglyMeasurable (Work.BoseFixB1S.wbUSharp h μ) (volume : Measure E3) := by
    have hleprod : ((volume : Measure E3).prod
          ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ)))
        ≤ ((volume : Measure E3).prod (volume : Measure E3)) :=
      MeasureTheory.Measure.prod_mono le_rfl Measure.restrict_le_self
    have hI : AEStronglyMeasurable (fun p : E3 × E3 => Work.BoseFixB1.wbMass v h μ p.2)
        ((volume : Measure E3).prod
          ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ))) :=
      (Work.BoseFixB1.WB.aestronglyMeasurable_wbMass (v := v) (h := h) (μ := μ)).comp_snd.mono_measure
        hleprod
    have hB : AEStronglyMeasurable (fun p : E3 × E3 => Work.SmallBoxSliding.boxMass ℓ d p.2)
        ((volume : Measure E3).prod
          ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ))) :=
      (aestronglyMeasurable_boxMass ℓ d).comp_snd.mono_measure hleprod
    have hW : AEMeasurable (fun p : E3 × E3 => Work.SmallBoxSliding.boxInd ℓ d p.2 p.1)
        ((volume : Measure E3).prod
          ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ))) := by
      have hset : MeasurableSet {p : E3 × E3 | p.1 ∈ Submission.BoseGases.dlBox ℓ d p.2} :=
        (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage
          (f := fun p : E3 × E3 => (p.2, p.1)) (by measurability)
      have hfun : (fun p : E3 × E3 => Work.SmallBoxSliding.boxInd ℓ d p.2 p.1)
          = {p : E3 × E3 | p.1 ∈ Submission.BoseGases.dlBox ℓ d p.2}.indicator
              (fun _ => (1 : ℝ)) := by
        funext p
        obtain ⟨z, u⟩ := p
        rw [Work.SmallBoxSliding.boxInd]
        by_cases hh : z ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show (z, u) ∈
            {p : E3 × E3 | p.1 ∈ Submission.BoseGases.dlBox ℓ d p.2} from hh)]
        · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (show (z, u) ∉
            {p : E3 × E3 | p.1 ∈ Submission.BoseGases.dlBox ℓ d p.2} from hh)]
      rw [hfun]
      exact (measurable_const.indicator hset).aemeasurable
    have hF : AEMeasurable (fun p : E3 × E3 =>
        (Work.BoseFixB1.wbMass v h μ p.2 / Work.SmallBoxSliding.boxMass ℓ d p.2)
          * Work.SmallBoxSliding.boxInd ℓ d p.2 p.1)
        ((volume : Measure E3).prod
          ((volume : Measure E3).restrict (Work.SmallBoxSliding.interiorSet ℓ d μ))) :=
      (hI.aemeasurable.div hB.aemeasurable).mul hW
    have h := hF.aestronglyMeasurable.integral_prod_right'
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.BoseFixB1S.wbUSharp]
    rfl
  exact ⟨hnn, hsmeas.aemeasurable,
    MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ'.le)
      (hsmeas.mono_measure Measure.restrict_le_self) (C * _root_.BoseGases.a v)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]
        exact hle z),
    hle⟩

end Work.BoseB1Cube
