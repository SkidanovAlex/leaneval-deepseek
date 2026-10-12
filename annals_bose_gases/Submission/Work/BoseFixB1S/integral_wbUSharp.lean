import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.integrableOn_wbMass_interior
import Submission.Work.BoseFixB1.WB.interiorSet_lt_top
import Submission.Work.BoseFixB1S.BoxNormDefs
import Submission.Work.BoseFixB1S.chiMass_le_const_mul_boxMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.integral_wbUSharp` — `∫_Λ U = W` for the **sharp** sliding potential

FS `final_v2.tex` step 4 of `thm:aprioriHLambda` reads its localising one-body potential
against the *sharp* box volume `|B(u)|` (rather than the smooth cutoff mass `chiMass`):

    U(z) = ∫_{I₋} (∬w_{1,B(u)} / |B(u)|) · 1_{B(u)}(z) du ,      W = ∫_{I₋} ∬w_{1,B(u)} ,

and the defining property of `U` is the exact identity `∫_Λ U = W` (`Λ = acube ℓ`), which
makes the `P`-part of the slot operator `U(xᵢ)` equal to `(W/ℓ³)` times the identity.

In the corpus vocabulary this is the pair `Work.BoseFixB1S.wbUSharp` / `Work.BoseFixB1.wbW`
(this file); the `chiMass`-normalised twin `Work.BoseFixB1.wbU` / `U_facts` is its smooth
counterpart.

## The proof

`1_{B(u)}` is supported in `Λ` (`dlBox_subset_acube`), so for every centre `u`

    ∫_{z∈Λ} 1_{B(u)}(z) dz = |B(u)| = boxMass ℓ d u ,

and hence the `z`-integral of the integrand of `wbUSharp` at fixed `u` is
`(wbMass u / boxMass u)·boxMass u = wbMass u` (the ratio is `0` where `boxMass u = 0`,
because there `wbMass u = 0` by the dominating hypothesis `hmassU`, which also gives
`chiMass ≤ C·boxMass` through `chiMass_le_const_mul_boxMass`).  The identity is therefore the
Fubini swap of the `(u,z)`-product integrand against
`(volume.restrict I₋).prod (volume.restrict Λ)`; joint integrability comes from the pointwise
bound `wbMass u ≤ (C a v)·K·boxMass u` (`K = (chiSupAbs·chiSmallDecay M)²`), which makes the
integrand bounded by the constant `(C a v)·K` on the finite-measure product `I₋ × Λ`
(`interiorSet_lt_top`, `acube_lt_top`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Shorthand for the configuration space `ℝ³` of this file. -/
abbrev BS1E3 := EuclideanSpace ℝ (Fin 3)

private lemma boxMass_nonneg (ℓ d : ℝ) (u : BS1E3) : 0 ≤ boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
  exact measureReal_nonneg

private lemma boxInd_nonneg (ℓ d : ℝ) (u x : BS1E3) : 0 ≤ boxInd ℓ d u x := by
  rw [Work.SmallBoxSliding.boxInd]
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hx]; norm_num
  · rw [Set.indicator_of_notMem hx]

private lemma boxInd_le_one (ℓ d : ℝ) (u x : BS1E3) : boxInd ℓ d u x ≤ 1 := by
  rw [Work.SmallBoxSliding.boxInd]
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; norm_num

private lemma boxInd_le_cube (ℓ d : ℝ) (u x : BS1E3) :
    boxInd ℓ d u x ≤ (acube ℓ).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · have hx' : x ∈ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hx
    rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- **The joint measurability of the box indicator**: `(u,x) ↦ 1_{B(u)}(x)` is the indicator
of the measurable set `{(u,x) | x ∈ dlBox ℓ d u}` (`measurableSet_boxIndSet`). -/
private lemma aestronglyMeasurable_boxInd (ℓ d : ℝ) :
    AEStronglyMeasurable (fun p : BS1E3 × BS1E3 => boxInd ℓ d p.1 p.2) (volume.prod volume) := by
  have hS : MeasurableSet
      ({p : BS1E3 × BS1E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} : Set (BS1E3 × BS1E3)) :=
    Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d
  have heq : (fun p : BS1E3 × BS1E3 => boxInd ℓ d p.1 p.2)
      = ({p : BS1E3 × BS1E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} :
          Set (BS1E3 × BS1E3)).indicator (fun _ => (1 : ℝ)) := by
    funext p
    obtain ⟨u, x⟩ := p
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem
          (show (u, x) ∈ {p : BS1E3 × BS1E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}
            from hx),
        Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem
          (show (u, x) ∉ {p : BS1E3 × BS1E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}
            from hx),
        Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx]
  rw [heq]
  exact (measurable_const.indicator hS).aestronglyMeasurable

/-- **`boxMass` is a.e. strongly measurable**: it is the `x`-marginal of the jointly
measurable box indicator. -/
private lemma aestronglyMeasurable_boxMass (ℓ d : ℝ) :
    AEStronglyMeasurable (fun u : BS1E3 => boxMass ℓ d u) volume := by
  have h2 := (aestronglyMeasurable_boxInd ℓ d).integral_prod_right'
  simpa only [Work.SmallBoxSliding.boxMass] using h2

/-- `1_{B(u)}` is supported in the big box `Λ = acube ℓ`, so its `z`-integral over `Λ` is the
box volume `boxMass ℓ d u = ∫_z 1_{B(u)}(z) dz`. -/
private lemma integral_acube_boxInd (ℓ d : ℝ) (u : BS1E3) :
    (∫ z in acube ℓ, boxInd ℓ d u z) = boxMass ℓ d u := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rfl
  · intro z hz
    rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem]
    exact fun h => hz (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u h)

theorem integral_wbUSharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {C : ℝ} (hC : 0 ≤ C)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u
      ≤ C * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseFixB1S.wbUSharp h μ z) = Work.BoseFixB1.wbW v h μ := by
  let M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  have hM' : 1 ≤ M := hM
  have hℓ' : 0 < ℓ := hℓ
  have hd' : 0 < d := hd
  have hmassU' : ∀ u : BS1E3, Work.BoseFixB1.wbMass v h μ u
      ≤ C * _root_.BoseGases.a v * chiMass M ℓ d u := hmassU
  have hmnn : ∀ u : BS1E3, 0 ≤ Work.BoseFixB1.wbMass v h μ u :=
    fun u => Work.BoseFixB1.wbMass_nonneg hv hvrad hv_supp hR0 hM' hℓ' hd' u
  -- ### the cutoff mass is positive somewhere, hence `0 ≤ C * a v`
  obtain ⟨u₀, hu₀⟩ : ∃ u : BS1E3, 0 < chiMass M ℓ d u := by
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ u : BS1E3, chiMass M ℓ d u = 0 :=
      fun u => le_antisymm (hcon u) (chiMass_nonneg M ℓ d u)
    have h0 : (∫ u : BS1E3, chiMass M ℓ d u) = 0 := by
      rw [show (fun u : BS1E3 => chiMass M ℓ d u) = fun _ : BS1E3 => (0 : ℝ) from
        funext hzero]
      simp
    have hvol : (∫ u : BS1E3, chiMass M ℓ d u) = ℓ ^ 3 := integral_chiMass_eq hM' hℓ' hd'
    rw [hvol] at h0
    have hpos : 0 < ℓ ^ 3 := by positivity
    linarith
  have hCa : 0 ≤ C * _root_.BoseGases.a v := by
    have h1 : 0 ≤ (C * _root_.BoseGases.a v) * chiMass M ℓ d u₀ :=
      le_trans (hmnn u₀) (hmassU' u₀)
    exact nonneg_of_mul_nonneg_left h1 hu₀
  -- ### the dominating constant
  have hchi_le : ∀ u : BS1E3, chiMass M ℓ d u
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * boxMass ℓ d u :=
    fun u => chiMass_le_const_mul_boxMass hM' hℓ' hd' u
  have hBnn : 0 ≤ (C * _root_.BoseGases.a v)
      * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 :=
    mul_nonneg hCa (sq_nonneg _)
  have hmassbox : ∀ u : BS1E3, Work.BoseFixB1.wbMass v h μ u
      ≤ ((C * _root_.BoseGases.a v)
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
        * boxMass ℓ d u := by
    intro u
    calc Work.BoseFixB1.wbMass v h μ u
        ≤ C * _root_.BoseGases.a v * chiMass M ℓ d u := hmassU' u
      _ ≤ (C * _root_.BoseGases.a v)
            * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
                * boxMass ℓ d u) :=
          mul_le_mul_of_nonneg_left (hchi_le u) hCa
      _ = ((C * _root_.BoseGases.a v)
            * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
          * boxMass ℓ d u := by ring
  -- ### the pointwise ratio bound and the cancellation of `boxMass`
  have hratio : ∀ u : BS1E3, Work.BoseFixB1.wbMass v h μ u / boxMass ℓ d u
      ≤ (C * _root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
    intro u
    rcases eq_or_lt_of_le (boxMass_nonneg ℓ d u) with h0 | hpos
    · have hm0 : Work.BoseFixB1.wbMass v h μ u = 0 := by
        refine le_antisymm ?_ (hmnn u)
        have hh := hmassbox u
        rw [← h0, mul_zero] at hh
        exact hh
      rw [← h0, hm0, zero_div]
      exact hBnn
    · rw [div_le_iff₀ hpos]
      exact hmassbox u
  have hunit : ∀ u : BS1E3,
      (Work.BoseFixB1.wbMass v h μ u / boxMass ℓ d u) * boxMass ℓ d u
        = Work.BoseFixB1.wbMass v h μ u := by
    intro u
    rcases eq_or_lt_of_le (boxMass_nonneg ℓ d u) with h0 | hpos
    · have hm0 : Work.BoseFixB1.wbMass v h μ u = 0 := by
        refine le_antisymm ?_ (hmnn u)
        have hh := hmassbox u
        rw [← h0, mul_zero] at hh
        exact hh
      rw [← h0, hm0]
      simp
    · exact div_mul_cancel₀ _ (ne_of_gt hpos)
  -- ### the finite-measure product `I₋ × Λ`
  haveI : IsFiniteMeasure ((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)) :=
    isFiniteMeasure_restrict.mpr (Work.BoseFixB1.WB.interiorSet_lt_top hℓ' hd').ne
  haveI : IsFiniteMeasure ((volume : Measure BS1E3).restrict (acube ℓ)) :=
    isFiniteMeasure_restrict.mpr (acube_lt_top ℓ hℓ'.le).ne
  haveI : IsFiniteMeasure (((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)).prod
      ((volume : Measure BS1E3).restrict (acube ℓ))) := inferInstance
  -- ### measurability of the joint integrand
  have hintw_aesm : AEStronglyMeasurable (fun u : BS1E3 => Work.BoseFixB1.wbMass v h μ u)
      ((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)) :=
    (Work.BoseFixB1.WB.integrableOn_wbMass_interior hv hvrad hv_supp hR0 hμ hav hM hℓ
      hd).aestronglyMeasurable
  have hbm_aesm : AEStronglyMeasurable (fun u : BS1E3 => boxMass ℓ d u)
      ((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)) :=
    (aestronglyMeasurable_boxMass ℓ d).mono_measure Measure.restrict_le_self
  have hfmeas : AEStronglyMeasurable
      (fun p : BS1E3 × BS1E3 => Work.BoseFixB1.wbMass v h μ p.1 / boxMass ℓ d p.1)
      (((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)).prod
        ((volume : Measure BS1E3).restrict (acube ℓ))) :=
    (hintw_aesm.div₀ hbm_aesm).comp_fst
  have hbmeas : AEStronglyMeasurable (fun p : BS1E3 × BS1E3 => boxInd ℓ d p.1 p.2)
      (((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)).prod
        ((volume : Measure BS1E3).restrict (acube ℓ))) :=
    (aestronglyMeasurable_boxInd ℓ d).mono_measure
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  -- ### the uniform bound
  have hbound : ∀ p : BS1E3 × BS1E3,
      ‖(Work.BoseFixB1.wbMass v h μ p.1 / boxMass ℓ d p.1) * boxInd ℓ d p.1 p.2‖
        ≤ (C * _root_.BoseGases.a v)
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
    intro p
    have h1 : 0 ≤ boxInd ℓ d p.1 p.2 := boxInd_nonneg ℓ d p.1 p.2
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (div_nonneg (hmnn p.1) (boxMass_nonneg ℓ d p.1)), abs_of_nonneg h1]
    calc (Work.BoseFixB1.wbMass v h μ p.1 / boxMass ℓ d p.1) * boxInd ℓ d p.1 p.2
        ≤ ((C * _root_.BoseGases.a v)
            * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
          * boxInd ℓ d p.1 p.2 := mul_le_mul_of_nonneg_right (hratio p.1) h1
      _ ≤ ((C * _root_.BoseGases.a v)
            * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
          * 1 := mul_le_mul_of_nonneg_left (boxInd_le_one ℓ d p.1 p.2) hBnn
      _ = (C * _root_.BoseGases.a v)
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 :=
          mul_one _
  -- ### joint integrability and Fubini
  have hInt : Integrable (fun p : BS1E3 × BS1E3 =>
      (Work.BoseFixB1.wbMass v h μ p.1 / boxMass ℓ d p.1) * boxInd ℓ d p.1 p.2)
      (((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)).prod
        ((volume : Measure BS1E3).restrict (acube ℓ))) :=
    Integrable.of_bound (hfmeas.mul hbmeas)
      ((C * _root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
      (Filter.Eventually.of_forall hbound)
  have hswap := MeasureTheory.integral_integral_swap
    (μ := (volume : Measure BS1E3).restrict (interiorSet ℓ d μ))
    (ν := (volume : Measure BS1E3).restrict (acube ℓ))
    (f := fun u z : BS1E3 =>
      (Work.BoseFixB1.wbMass v h μ u / boxMass ℓ d u) * boxInd ℓ d u z) hInt
  -- ### assembly
  rw [show (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseFixB1S.wbUSharp h μ z)
      = ∫ z, (∫ u, (Work.BoseFixB1.wbMass v h μ u / boxMass ℓ d u) * boxInd ℓ d u z
            ∂((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)))
          ∂((volume : Measure BS1E3).restrict (acube ℓ)) from rfl]
  rw [hswap.symm]
  rw [show Work.BoseFixB1.wbW v h μ
      = ∫ u, Work.BoseFixB1.wbMass v h μ u
          ∂((volume : Measure BS1E3).restrict (interiorSet ℓ d μ)) from rfl]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only []
  rw [MeasureTheory.integral_const_mul]
  rw [integral_acube_boxInd ℓ d u]
  exact hunit u

end Work.BoseFixB1S
