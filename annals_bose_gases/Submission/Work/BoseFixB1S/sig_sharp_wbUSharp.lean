import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.aestronglyMeasurable_wbMass
import Submission.Work.BoseFixB1.WB.boxState_sq_bound
import Submission.Work.BoseFixB1S.integral_wbUSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The measure-theoretic core of `sig_sharp_wbUSharp`: for a bounded measurable weight `f`,
the `x`-integral of `|Φ|²` against the `u`-average of `f·1_{B(u)}` equals the `u`-integral of `f`
against the box count. -/
private lemma wbUSharp_measure_aux {ℓ d μ B0 : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : E3 → ℝ} (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume : MeasureTheory.Measure E3))
    (hfbd : ∀ u : E3, |f u| ≤ B0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {P : ℝ} (hP0 : 0 ≤ P) (hP : ∀ x ∈ Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 ≤ P) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
        * (∑ i : Fin n, ∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
            f u * Work.SmallBoxSliding.boxInd ℓ d u (x i)))
      = ∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, f u
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
              * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) := by
  set I : Set E3 := Work.SmallBoxSliding.interiorSet ℓ d μ with hIdef
  have hboxInd01 : ∀ u x : E3,
      0 ≤ Work.SmallBoxSliding.boxInd ℓ d u x ∧ Work.SmallBoxSliding.boxInd ℓ d u x ≤ 1 := by
    intro u x
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx]; norm_num
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx]; norm_num
  have hboxInd_meas : Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) := by
    have hEq : Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)
        = {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator (fun _ => (1:ℝ)) := by
      funext p
      obtain ⟨u, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
      · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx,
          Set.indicator_of_mem (show (u,x) ∈ {p : E3 × E3
              | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show (u,x) ∉ {p : E3 × E3
              | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    rw [hEq]
    exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)
  have hIlt : (MeasureTheory.volume : MeasureTheory.Measure E3) I < ⊤ := by
    rw [hIdef]; exact Work.BoseFixB1.WB.interiorSet_lt_top hℓ hd
  haveI : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hIlt⟩
  have hf_I : AEStronglyMeasurable f ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I) :=
    hfmeas.mono_measure Measure.restrict_le_self
  have hind_aesm : ∀ y : E3, AEStronglyMeasurable
      (fun u : E3 => Work.SmallBoxSliding.boxInd ℓ d u y)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I) := by
    intro y
    have hset : MeasurableSet {u : E3 | y ∈ Submission.BoseGases.dlBox ℓ d u} :=
      (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage
        (f := fun u : E3 => (u, y)) (by measurability)
    have hfun : (fun u : E3 => Work.SmallBoxSliding.boxInd ℓ d u y)
        = {u : E3 | y ∈ Submission.BoseGases.dlBox ℓ d u}.indicator (fun _ => (1:ℝ)) := by
      funext u
      rw [Work.SmallBoxSliding.boxInd]
      by_cases hy : y ∈ Submission.BoseGases.dlBox ℓ d u <;> simp [hy]
    rw [hfun]
    exact (measurable_const.indicator hset).aestronglyMeasurable
  -- the pointwise sum identity
  have hsum : ∀ z : Submission.BoseGases.X n,
      (∑ i : Fin n, ∫ u in I, f u * Work.SmallBoxSliding.boxInd ℓ d u (z i))
        = ∫ u in I, f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) z := by
    intro z
    have hint : ∀ i : Fin n, Integrable (fun u : E3 =>
        f u * Work.SmallBoxSliding.boxInd ℓ d u (z i))
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I) := by
      intro i
      refine MeasureTheory.Integrable.of_bound (hf_I.mul (hind_aesm (z i))) B0 ?_
      filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hboxInd01 u (z i)).1]
      calc |f u| * Work.SmallBoxSliding.boxInd ℓ d u (z i)
          ≤ B0 * 1 := mul_le_mul (hfbd u) (hboxInd01 u (z i)).2 (hboxInd01 u (z i)).1
              (le_trans (abs_nonneg _) (hfbd u))
        _ = B0 := mul_one B0
    calc (∑ i : Fin n, ∫ u in I, f u * Work.SmallBoxSliding.boxInd ℓ d u (z i))
        = ∫ u in I, ∑ i : Fin n, f u * Work.SmallBoxSliding.boxInd ℓ d u (z i) :=
          (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)).symm
      _ = ∫ u in I, f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) z := by
          refine MeasureTheory.setIntegral_congr_fun ?_ (fun u _ => ?_)
          · rw [hIdef]; exact Work.SmallBoxSliding.measurableSet_interiorSet ℓ d μ
          · rw [Work.FockBridge.boxCount_eq_sum_indicator, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rfl
  have habox_lt : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  haveI : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact habox_lt⟩
  -- measurability of the joint integrand pieces
  have hf_snd : AEStronglyMeasurable (fun p : E3 × Submission.BoseGases.X n => f p.1)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    hf_I.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst
        (μ := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict I)
        (ν := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
  have hPhiAesm : AEStronglyMeasurable
      (fun p : E3 × Submission.BoseGases.X n => (Φ p.2) ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    ((hΦc.comp continuous_snd).pow 2).aestronglyMeasurable
  have hbCmeas : Measurable (fun p : E3 × Submission.BoseGases.X n =>
      Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2) := by
    have hEq : (fun p : E3 × Submission.BoseGases.X n =>
        Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2)
        = fun p : E3 × Submission.BoseGases.X n =>
            ∑ i : Fin n, Work.SmallBoxSliding.boxInd ℓ d p.1 (p.2 i) := by
      funext p
      rw [Work.FockBridge.boxCount_eq_sum_indicator]
      rfl
    rw [hEq]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have hset : MeasurableSet {p : E3 × Submission.BoseGases.X n
        | p.2 i ∈ Submission.BoseGases.dlBox ℓ d p.1} :=
      (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage
        (f := fun p : E3 × Submission.BoseGases.X n => (p.1, p.2 i)) (by measurability)
    have hfun : (fun p : E3 × Submission.BoseGases.X n =>
        Work.SmallBoxSliding.boxInd ℓ d p.1 (p.2 i))
        = {p : E3 × Submission.BoseGases.X n
            | p.2 i ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator (fun _ => (1:ℝ)) := by
      funext p
      rw [Work.SmallBoxSliding.boxInd]
      by_cases h : p.2 i ∈ Submission.BoseGases.dlBox ℓ d p.1 <;> simp [h]
    rw [hfun]
    exact measurable_const.indicator hset
  have hboxC_aesm : AEStronglyMeasurable (fun p : E3 × Submission.BoseGases.X n =>
      Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := hbCmeas.aestronglyMeasurable
  -- joint integrability
  have hboxmem : ∀ᵐ p ∂(((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I).prod
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))), p.2 ∈ Submission.BoseGases.abox n ℓ := by
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : E3 × Submission.BoseGases.X n | p.2 ∈ Submission.BoseGases.abox n ℓ})
      ((Submission.BoseGases.abox_measurable n ℓ).preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall (fun _ =>
        MeasureTheory.ae_restrict_of_forall_mem (Submission.BoseGases.abox_measurable n ℓ)
          (fun x hx => hx)))
  have hbC01 : ∀ p : E3 × Submission.BoseGases.X n,
      0 ≤ Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2 ∧
      Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2 ≤ (n : ℝ) :=
    fun p => ⟨Work.FockBridge.boxCount_nonneg _ _, Work.FockBridge.boxCount_le _ _⟩
  have hFint : Integrable (fun p : E3 × Submission.BoseGases.X n =>
      f p.1 * ((Φ p.2) ^ 2
          * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict I).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) := by
    refine MeasureTheory.Integrable.of_bound
      (hf_snd.mul (hPhiAesm.mul hboxC_aesm)) (B0 * (P * (n : ℝ))) ?_
    filter_upwards [hboxmem] with p hp
    have h1 := hfbd p.1
    have h2 : (Φ p.2) ^ 2 ≤ P := hP p.2 hp
    have h2' : 0 ≤ (Φ p.2) ^ 2 := sq_nonneg _
    have h3 := (hbC01 p).1
    have h4 := (hbC01 p).2
    have hB0nn : 0 ≤ B0 := le_trans (abs_nonneg _) h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg h2' h3)]
    calc |f p.1| * ((Φ p.2) ^ 2
            * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d p.1) p.2)
        ≤ B0 * (P * (n : ℝ)) :=
          mul_le_mul h1 (mul_le_mul h2 h4 h3 hP0) (mul_nonneg h2' h3) hB0nn
      _ = B0 * (P * (n : ℝ)) := rfl
  -- the Fubini swap
  have hswap := MeasureTheory.integral_integral_swap
    (μ := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict I)
    (ν := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ))
    (f := fun u : E3 => fun x : Submission.BoseGases.X n =>
      f u * ((Φ x) ^ 2 * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x))
    hFint
  -- assembly
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
          * (∑ i : Fin n, ∫ u in I, f u * Work.SmallBoxSliding.boxInd ℓ d u (x i)))
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
          * (∫ u in I, f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => ?_)
    rw [hsum x]
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
          * (∫ u in I, f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x))
      = ∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
          (Φ x) ^ 2 * (f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
        (Φ x) ^ 2 * (f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x))
      = ∫ u in I, ∫ x in Submission.BoseGases.abox n ℓ,
          f u * ((Φ x) ^ 2 * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) := by
    have h3a : (∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
          (Φ x) ^ 2 * (f u * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x))
        = ∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
            f u * ((Φ x) ^ 2 * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) := by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
        (fun x _ => ?_)
      refine MeasureTheory.setIntegral_congr_fun
        (Work.SmallBoxSliding.measurableSet_interiorSet ℓ d μ) (fun u _ => ?_)
      ring
    rw [h3a, hswap.symm]
  have hstep4 : (∫ u in I, ∫ x in Submission.BoseGases.abox n ℓ,
        f u * ((Φ x) ^ 2 * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x))
      = ∫ u in I, f u
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
              * Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) := by
    refine MeasureTheory.setIntegral_congr_fun
      (Work.SmallBoxSliding.measurableSet_interiorSet ℓ d μ) (fun u _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-- `boxMass` is nonnegative. -/
private lemma boxMass_nonneg_aux (ℓ d : ℝ) (u : E3) :
    0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
  exact MeasureTheory.measureReal_nonneg

/-- A.e. strong measurability of `boxMass`. -/
private lemma boxMass_aesm_aux (ℓ d : ℝ) :
    AEStronglyMeasurable (fun u : E3 => Work.SmallBoxSliding.boxMass ℓ d u)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
  have hEq : (fun u : E3 => Work.SmallBoxSliding.boxMass ℓ d u)
      = fun u : E3 => ∫ x : E3, Work.SmallBoxSliding.boxInd ℓ d u x := by
    funext u; rfl
  rw [hEq]
  have hboxInd_meas : Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) := by
    have hE : Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)
        = {p : E3 × E3 | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator (fun _ => (1:ℝ)) := by
      funext p
      obtain ⟨u, x⟩ := p
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
      · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx,
          Set.indicator_of_mem (show (u,x) ∈ {p : E3 × E3
              | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
      · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show (u,x) ∉ {p : E3 × E3
              | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    rw [hE]
    exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    (f := fun p : E3 × E3 => Work.SmallBoxSliding.boxInd ℓ d p.1 p.2)
    hboxInd_meas.stronglyMeasurable).aestronglyMeasurable

theorem sig_sharp_wbUSharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
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
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * (∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i)))
      = ∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          (Work.BoseFixB1.wbMass v h μ u
              / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
                  * Work.FockBridge.boxCount
                      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) x) := by
  set B0 : ℝ := C * _root_.BoseGases.a v * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) ^ 2
    with hB0def
  have hB0nn : 0 ≤ B0 := by
    rw [hB0def]
    exact mul_nonneg (mul_nonneg hC hav.le) (sq_nonneg _)
  have hbm_aesm : AEStronglyMeasurable (fun u : E3 =>
      Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    boxMass_aesm_aux _ _
  have hfm : AEStronglyMeasurable (fun u : E3 =>
      Work.BoseFixB1.wbMass v h μ u
        / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (Work.BoseFixB1.WB.aestronglyMeasurable_wbMass).div₀ hbm_aesm
  have hfb : ∀ u : E3,
      |Work.BoseFixB1.wbMass v h μ u
        / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u| ≤ B0 := by
    intro u
    have h1 : (0:ℝ) ≤ Work.BoseFixB1.wbMass v h μ u :=
      Work.BoseFixB1.wbMass_nonneg hv hvrad hv_supp hR0 hM hℓ hd u
    have h3 := Work.BoseFixB1S.chiMass_le_const_mul_boxMass hM hℓ hd u
    have h4 : Work.BoseFixB1.wbMass v h μ u
        ≤ B0 * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
      rw [hB0def]
      exact le_trans (le_trans (hmassU u)
        (mul_le_mul_of_nonneg_left h3 (mul_nonneg hC hav.le)))
        (le_of_eq (by ring))
    rcases eq_or_lt_of_le (boxMass_nonneg_aux _ _ u) with hg | hg
    · rw [← hg, div_zero, abs_zero]; exact hB0nn
    · rw [abs_of_nonneg (div_nonneg h1 hg.le), div_le_iff₀ hg]
      exact h4
  have hU : ∀ z : E3, Work.BoseFixB1S.wbUSharp h μ z
      = ∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          (Work.BoseFixB1.wbMass v h μ u
              / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.SmallBoxSliding.boxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z := by
    intro z
    rw [Work.BoseFixB1S.wbUSharp]
    rfl
  obtain ⟨P, hP0, hP⟩ := Work.BoseFixB1.WB.boxState_sq_bound Φ
  have hP' : ∀ x : Submission.BoseGases.X n,
      x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) →
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 ≤ P := hP
  rw [show (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
          * (∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i)))
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2
            * (∑ i : Fin n, ∫ u in Work.SmallBoxSliding.interiorSet
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                (Work.BoseFixB1.wbMass v h μ u
                    / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  * Work.SmallBoxSliding.boxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i)) from by
        refine MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (fun x _ => ?_)
        rw [show (∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i))
            = ∑ i : Fin n, ∫ u in Work.SmallBoxSliding.interiorSet
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                (Work.BoseFixB1.wbMass v h μ u
                    / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  * Work.SmallBoxSliding.boxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i)
            from Finset.sum_congr rfl (fun i _ => hU (x i))]]
  exact wbUSharp_measure_aux hℓ hd hfm hfb Φ.contDiff.continuous hP0 hP'

end Work.BoseFixB1S
