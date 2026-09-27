import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.condExp_localize
import Submission.Work.EKLComp.Hcond_joinPart_reindex
import Submission.Work.EKLComp.condExp_rowsum
import Submission.Work.EKLComp.condExp_sum_one
import Submission.Work.EKLComp.negMulLog_sum_div

namespace Work.EKLComp

open MeasureTheory Filter
open scoped BigOperators

/-! ## Small helpers -/

theorem negMulLog_indicator_mul {X : Type} (S : Set X) (x : X) (t : ℝ) :
    Real.negMulLog ((S.indicator (fun _ => (1:ℝ)) x) * t)
      = (S.indicator (fun _ => (1:ℝ)) x) * Real.negMulLog t := by
  by_cases h : x ∈ S
  · rw [Set.indicator_of_mem h, one_mul, one_mul]
  · rw [Set.indicator_of_notMem h, zero_mul, zero_mul, Real.negMulLog_zero]

theorem sum_indicator_eq_one {X : Type} [mX : MeasurableSpace X] {ι : Type} [Fintype ι]
    {A : ι → Set X} (hA : Core.IsMPart A) :
    (∑ i, (A i).indicator (fun _ => (1:ℝ))) = (fun _ => (1:ℝ)) := by
  funext x
  obtain ⟨i0, hi0, huniq⟩ := hA.exists_unique x
  simp only [Finset.sum_apply, Pi.one_apply]
  rw [Finset.sum_eq_single i0]
  · exact Set.indicator_of_mem hi0 (fun _ => (1:ℝ))
  · intro j _ hjne
    exact Set.indicator_of_notMem (fun h => hjne (huniq j h)) (fun _ => (1:ℝ))
  · intro h; exact absurd (Finset.mem_univ i0) h

theorem isMPart_parts__Hcond_joinPart {X : Type} [mX : MeasurableSpace X] (P : Work.EKLContract.FinPart X) :
    Core.IsMPart P.parts := ⟨P.measurable, P.disjoint, P.cover⟩

/-- Pull `1_{A i}` out of the conditional expectation w.r.t. `m ⊔ partSigmaFam A`. -/
theorem condExp_inter_indicator_localize {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {ι : Type} [Fintype ι] (A : ι → Set X) (hA : Core.IsMPart A) (hm : m ≤ mX)
    (μ : Measure X) [IsProbabilityMeasure μ] (i : ι) (S : Set X) (hS : MeasurableSet S) :
    condExp (m ⊔ Core.partSigmaFam A) μ ((A i ∩ S).indicator (fun _ => (1:ℝ)))
      =ᵐ[μ] (A i).indicator (fun _ => (1:ℝ))
        * condExp (m ⊔ Core.partSigmaFam A) μ (S.indicator (fun _ => (1:ℝ))) := by
  have hAi_le : Core.partSigmaFam A ≤ m ⊔ Core.partSigmaFam A := le_sup_right
  have hAi : MeasurableSet[m ⊔ Core.partSigmaFam A] (A i) :=
    hAi_le _ (MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩)
  have hfun : ((A i).indicator (fun _ => (1:ℝ))) * (S.indicator (fun _ => (1:ℝ)))
      = ((A i ∩ S).indicator (fun _ => (1:ℝ))) := by
    funext x
    by_cases hx : x ∈ A i <;> by_cases hy : x ∈ S <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
  rw [← hfun]
  refine condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m ⊔ Core.partSigmaFam A)
    (f := (A i).indicator (fun _ => (1:ℝ))) (g := S.indicator (fun _ => (1:ℝ)))
    ?_ ?_ ?_
  · exact (measurable_const.indicator hAi).stronglyMeasurable
  · rw [hfun]
    exact (integrable_const (1:ℝ)).indicator ((hA.measurable i).inter hS)
  · exact (integrable_const (1:ℝ)).indicator hS

/-- `{p i = 0} ∩ A i` is null. -/
theorem condExp_indicator_zero_inter_null {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {ι : Type} [Fintype ι] (A : ι → Set X) (hA : Core.IsMPart A) (hm : m ≤ mX)
    (μ : Measure X) [IsProbabilityMeasure μ] (i : ι) :
    μ ({x | condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} ∩ A i) = 0 := by
  set Z : Set X := {x | condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} with hZdef
  have hp_meas : Measurable[m] (fun x => condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x) :=
    stronglyMeasurable_condExp.measurable
  have hZmeas : MeasurableSet[m] Z := hp_meas (measurableSet_singleton 0)
  have hZamb : MeasurableSet Z := hm Z hZmeas
  have hint : Integrable ((A i).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator (hA.measurable i)
  have h1 : ∫ x in Z, condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x ∂μ
      = ∫ x in Z, ((A i).indicator (fun _ => (1:ℝ))) x ∂μ :=
    setIntegral_condExp (m := m) (m₀ := mX) hm hint hZmeas
  have h2 : ∫ x in Z, condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x ∂μ = 0 := by
    rw [show (∫ x in Z, condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x ∂μ)
        = ∫ x in Z, (0:ℝ) ∂μ from ?_]
    · simp
    · refine setIntegral_congr_fun hZamb (fun x hx => ?_)
      exact hx
  have h3 : ∫ x in Z, ((A i).indicator (fun _ => (1:ℝ))) x ∂μ = (μ (Z ∩ A i)).toReal := by
    rw [← integral_indicator hZamb]
    have hfun : Z.indicator (fun x => ((A i).indicator (fun _ => (1:ℝ))) x)
        = (Z ∩ A i).indicator (fun _ => (1:ℝ)) := by
      funext x
      by_cases hx : x ∈ Z <;> by_cases hy : x ∈ A i <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
    rw [hfun]
    exact integral_indicator_one (hZamb.inter (hA.measurable i))
  have h4 : (μ (Z ∩ A i)).toReal = 0 := by rw [← h3, ← h1, h2]
  rcases (ENNReal.toReal_eq_zero_iff (μ (Z ∩ A i))).mp h4 with h | h
  · exact h
  · exact absurd h (measure_ne_top μ _)


/-! ## The chain rule for the conditional entropy of a join -/

theorem Hcond_fam_chain {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : ι → Set X) (B : κ → Set X) (hA : Core.IsMPart A) (hB : Core.IsMPart B)
    (hm : m ≤ mX) :
    (∫ x, ∑ i, ∑ j, Real.negMulLog (condExp m μ ((A i ∩ B j).indicator (fun _ => (1:ℝ))) x) ∂μ)
      = (∫ x, ∑ i, Real.negMulLog (condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x) ∂μ)
        + (∫ x, ∑ j, Real.negMulLog (condExp (m ⊔ Core.partSigmaFam A) μ ((B j).indicator (fun _ => (1:ℝ))) x) ∂μ) := by
  classical
  have hn_le : m ⊔ Core.partSigmaFam A ≤ mX := sup_le hm (Core.partSigmaFam_le hA)
  set p : ι → X → ℝ := fun i => condExp m μ ((A i).indicator (fun _ => (1:ℝ))) with hp
  set q : ι → κ → X → ℝ := fun i j => condExp m μ ((A i ∩ B j).indicator (fun _ => (1:ℝ))) with hq
  set r : κ → X → ℝ := fun j => condExp (m ⊔ Core.partSigmaFam A) μ ((B j).indicator (fun _ => (1:ℝ))) with hr
  set W : ι → X → ℝ := fun i x => ∑ j, Real.negMulLog (q i j x / p i x) with hW
  have hpe : ∀ i, p i = condExp m μ ((A i).indicator (fun _ => (1:ℝ))) := fun i => congrFun hp i
  have hqe : ∀ i j, q i j = condExp m μ ((A i ∩ B j).indicator (fun _ => (1:ℝ))) :=
    fun i j => congrFun (congrFun hq i) j
  have hre : ∀ j, r j = condExp (m ⊔ Core.partSigmaFam A) μ ((B j).indicator (fun _ => (1:ℝ))) :=
    fun j => congrFun hr j
  have hWe : ∀ i, W i = fun x => ∑ j, Real.negMulLog (q i j x / p i x) := fun i => congrFun hW i
  have hp_meas : ∀ i, Measurable[m] (p i) := fun i => by
    rw [hpe i]; exact stronglyMeasurable_condExp.measurable
  have hq_meas : ∀ i j, Measurable[m] (q i j) := fun i j => by
    rw [hqe i j]; exact stronglyMeasurable_condExp.measurable
  have hr_meas : ∀ j, Measurable[m ⊔ Core.partSigmaFam A] (r j) := fun j => by
    rw [hre j]; exact stronglyMeasurable_condExp.measurable
  have hp_int : ∀ i, Integrable (p i) μ := fun i => by rw [hpe i]; exact integrable_condExp
  have hq_int : ∀ i j, Integrable (q i j) μ := fun i j => by rw [hqe i j]; exact integrable_condExp
  have hr_int : ∀ j, Integrable (r j) μ := fun j => by rw [hre j]; exact integrable_condExp
  have hp_bnd : ∀ i, ∀ᵐ x ∂μ, p i x ∈ Set.Icc 0 1 := by
    intro i
    rw [hpe i]
    exact Work.EKLC6Core.condExp_mem_Icc (μ := μ) (m := m) hm
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).2)
      ((integrable_const (1:ℝ)).indicator (hA.measurable i))
  have hq_bnd : ∀ i j, ∀ᵐ x ∂μ, q i j x ∈ Set.Icc 0 1 := by
    intro i j
    rw [hqe i j]
    exact Work.EKLC6Core.condExp_mem_Icc (μ := μ) (m := m) hm
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i ∩ B j) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i ∩ B j) x).2)
      ((integrable_const (1:ℝ)).indicator ((hA.measurable i).inter (hB.measurable j)))
  have hr_bnd : ∀ j, ∀ᵐ x ∂μ, r j x ∈ Set.Icc 0 1 := by
    intro j
    rw [hre j]
    exact Work.EKLC6Core.condExp_mem_Icc (μ := μ) (m := m ⊔ Core.partSigmaFam A) hn_le
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (B j) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (B j) x).2)
      ((integrable_const (1:ℝ)).indicator (hB.measurable j))
  have hrowsum : ∀ i, (fun x => ∑ j, q i j x) =ᵐ[μ] p i := by
    intro i
    have h := condExp_rowsum (m := m) (A := A) (B := B) hA hB μ i
    have hq' : (fun j => q i j) = (fun j => condExp m μ ((A i ∩ B j).indicator (fun _ => (1:ℝ)))) :=
      funext fun j => hqe i j
    have hp' : p i = condExp m μ ((A i).indicator (fun _ => (1:ℝ))) := hpe i
    rw [← hq', ← hp'] at h
    filter_upwards [h] with x hx
    simpa only [Finset.sum_apply] using hx
  have hq_nonneg : ∀ i j, ∀ᵐ x ∂μ, 0 ≤ q i j x := fun i j => (hq_bnd i j).mono fun x hx => hx.1
  have hq_le_p : ∀ i j, q i j ≤ᵐ[μ] p i := by
    intro i j
    filter_upwards [hrowsum i, Filter.eventually_all.mpr (fun j => hq_nonneg i j)] with x hrow hnon
    calc q i j x ≤ ∑ j', q i j' x := Finset.single_le_sum (fun j' _ => hnon j') (Finset.mem_univ j)
      _ = p i x := hrow
  have hloc : ∀ i j, ((A i).indicator (fun _ => (1:ℝ))) * (p i * r j)
      =ᵐ[μ] ((A i).indicator (fun _ => (1:ℝ))) * q i j := by
    intro i j
    have h := condExp_localize (m := m) (mX := mX) A hA hm μ i (B j) (hB.measurable j)
    have hpu := condExp_inter_indicator_localize (m := m) A hA hm μ i (B j) (hB.measurable j)
    rw [← hpe i, ← hqe i j] at h
    rw [← hre j] at hpu
    filter_upwards [h, hpu] with x hx hxpu
    simp only [Pi.mul_apply] at hx hxpu ⊢
    rw [hxpu] at hx
    rw [← hx]
    ring
  have hVeq : ∀ i j, ((A i).indicator (fun _ => (1:ℝ))) * (fun x => q i j x / p i x)
      =ᵐ[μ] ((A i).indicator (fun _ => (1:ℝ))) * r j := by
    intro i j
    have hZ := condExp_indicator_zero_inter_null (m := m) A hA hm μ i
    have hZae : ∀ᵐ x ∂μ,
        x ∉ ({x | condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} ∩ A i) := by
      rw [MeasureTheory.ae_iff]
      rw [show ({a | ¬ (a ∉ ({x | condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} ∩ A i))})
          = ({x | condExp m μ ((A i).indicator (fun _ => (1:ℝ))) x = 0} ∩ A i) from by ext x; simp]
      exact hZ
    filter_upwards [hloc i j, hZae] with x hlocx hZx
    simp only [Pi.mul_apply] at hlocx ⊢
    by_cases hx : x ∈ A i
    · have hpne : p i x ≠ 0 := by
        rw [hpe i]; exact fun h => hZx ⟨h, hx⟩
      have hval : p i x * r j x = q i j x := by
        have hh := hlocx
        rw [Set.indicator_of_mem hx (fun _ => (1:ℝ))] at hh
        simpa using hh
      rw [Set.indicator_of_mem hx (fun _ => (1:ℝ)), one_mul, one_mul]
      exact (div_eq_iff hpne).mpr (by rw [← hval, mul_comm])
    · simp [Set.indicator_of_notMem, hx]
  have hWeq : ∀ i, ((A i).indicator (fun _ => (1:ℝ))) * W i
      =ᵐ[μ] ((A i).indicator (fun _ => (1:ℝ))) * (fun x => ∑ j, Real.negMulLog (r j x)) := by
    intro i
    have hall : ∀ᵐ x ∂μ, ∀ j,
        (((A i).indicator (fun _ => (1:ℝ))) * (fun x => q i j x / p i x)) x
          = (((A i).indicator (fun _ => (1:ℝ))) * r j) x :=
      Filter.eventually_all.mpr (fun j => hVeq i j)
    filter_upwards [hall] with x hx
    simp only [Pi.mul_apply] at hx ⊢
    rw [hWe i]
    simp only [Pi.mul_apply]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := hx j
    have key : Real.negMulLog ((((A i).indicator (fun _ => (1:ℝ))) x) * (q i j x / p i x))
        = Real.negMulLog ((((A i).indicator (fun _ => (1:ℝ))) x) * r j x) := by rw [hj]
    rwa [negMulLog_indicator_mul, negMulLog_indicator_mul] at key
  have hmain_ae : (fun x => ∑ i, ∑ j, Real.negMulLog (q i j x))
      =ᵐ[μ] (fun x => ∑ i, Real.negMulLog (p i x) + ∑ i, p i x * W i x) := by
    have h1 : ∀ᵐ x ∂μ, ∀ i, ∑ j, q i j x = p i x :=
      Filter.eventually_all.mpr (fun i => hrowsum i)
    have h2 : ∀ᵐ x ∂μ, ∀ i, ∀ j, 0 ≤ q i j x :=
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => hq_nonneg i j))
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [negMulLog_sum_div (fun j => q i j x) (p i x) (fun j => hx2 i j) (hx1 i)]
  have hV_bnd : ∀ i j, ∀ᵐ x ∂μ, q i j x / p i x ∈ Set.Icc 0 1 := by
    intro i j
    filter_upwards [hq_bnd i j, hq_le_p i j, hp_bnd i] with x hqij hqlep hpb
    refine ⟨div_nonneg hqij.1 hpb.1, ?_⟩
    by_cases hp0 : p i x = 0
    · rw [hp0, div_zero]; norm_num
    · rw [div_le_one (lt_of_le_of_ne hpb.1 (Ne.symm hp0))]; exact hqlep
  have hW_meas : ∀ i, Measurable[m] (W i) := by
    intro i
    rw [hWe i]
    exact Finset.measurable_sum _ (fun j _ =>
      Real.continuous_negMulLog.measurable.comp ((hq_meas i j).div (hp_meas i)))
  have hW_sm : ∀ i, StronglyMeasurable[m] (W i) := fun i => (hW_meas i).stronglyMeasurable
  have hW_nb : ∀ i, ∀ᵐ x ∂μ, ‖W i x‖ ≤ (Fintype.card κ : ℝ) := by
    intro i
    filter_upwards [Filter.eventually_all.mpr (fun j => hV_bnd i j)] with x hx
    have hnn : 0 ≤ ∑ j, Real.negMulLog (q i j x / p i x) :=
      Finset.sum_nonneg (fun j _ => Real.negMulLog_nonneg (hx j).1 (hx j).2)
    have hup : ∑ j, Real.negMulLog (q i j x / p i x) ≤ (Fintype.card κ : ℝ) := by
      calc ∑ j, Real.negMulLog (q i j x / p i x) ≤ ∑ j, (1:ℝ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact le_trans (Real.negMulLog_le_one_sub_self (hx j).1) (by linarith [(hx j).1])
        _ = (Fintype.card κ : ℝ) := by simp
    rw [hWe i]
    change ‖∑ j, Real.negMulLog (q i j x / p i x)‖ ≤ (Fintype.card κ : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hup
  have hW_int : ∀ i, Integrable (W i) μ := by
    intro i
    refine (integrable_const (Fintype.card κ : ℝ)).mono' ?_ (hW_nb i)
    exact ((hW_meas i).mono hm le_rfl).aestronglyMeasurable
  have hpW_int : ∀ i, Integrable (fun x => p i x * W i x) μ := by
    intro i
    have hb : ∀ᵐ x ∂μ, ‖p i x * W i x‖ ≤ (Fintype.card κ : ℝ) := by
      filter_upwards [hp_bnd i, hW_nb i] with x hpb hWb
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpb.1, ← Real.norm_eq_abs]
      calc p i x * ‖W i x‖ ≤ 1 * (Fintype.card κ : ℝ) :=
            mul_le_mul hpb.2 hWb (norm_nonneg _) (by norm_num)
        _ = (Fintype.card κ : ℝ) := one_mul _
    refine (integrable_const (Fintype.card κ : ℝ)).mono' ?_ hb
    exact (((hp_meas i).mul (hW_meas i)).mono hm le_rfl).aestronglyMeasurable
  have hW1_int : ∀ i, Integrable (fun x => ((A i).indicator (fun _ => (1:ℝ))) x * W i x) μ := by
    intro i
    have hb : ∀ᵐ x ∂μ, ‖((A i).indicator (fun _ => (1:ℝ))) x * W i x‖ ≤ (Fintype.card κ : ℝ) := by
      filter_upwards [hW_nb i] with x hx
      rw [norm_mul]
      have h1 : ‖((A i).indicator (fun _ => (1:ℝ))) x‖ ≤ 1 := by
        by_cases h : x ∈ A i
        · rw [Set.indicator_of_mem h (fun _ => (1:ℝ))]; simp
        · rw [Set.indicator_of_notMem h (fun _ => (1:ℝ))]; simp
      calc ‖((A i).indicator (fun _ => (1:ℝ))) x‖ * ‖W i x‖ ≤ 1 * (Fintype.card κ : ℝ) :=
            mul_le_mul h1 hx (norm_nonneg _) (by positivity)
        _ = (Fintype.card κ : ℝ) := one_mul _
    refine (integrable_const (Fintype.card κ : ℝ)).mono' ?_ hb
    exact ((measurable_const.indicator (hA.measurable i)).mul
      ((hW_meas i).mono hm le_rfl)).aestronglyMeasurable
  have hnml_p_int : ∀ i, Integrable (fun x => Real.negMulLog (p i x)) μ := fun i =>
    Work.EKLC6Core.integrable_negMulLog_condExp (μ := μ) (m := m)
      (f := (A i).indicator (fun _ => (1:ℝ)))
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).2)
      ((integrable_const (1:ℝ)).indicator (hA.measurable i))
  have hnml_r_int : ∀ j, Integrable (fun x => Real.negMulLog (r j x)) μ := fun j =>
    Work.EKLC6Core.integrable_negMulLog_condExp (μ := μ) (m := m ⊔ Core.partSigmaFam A)
      (f := (B j).indicator (fun _ => (1:ℝ)))
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (B j) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (B j) x).2)
      ((integrable_const (1:ℝ)).indicator (hB.measurable j))
  have hpull : ∀ i, ∫ x, p i x * W i x ∂μ
      = ∫ x, ((A i).indicator (fun _ => (1:ℝ))) x * W i x ∂μ := by
    intro i
    have hce : condExp m μ (fun x => ((A i).indicator (fun _ => (1:ℝ))) x * W i x)
        =ᵐ[μ] fun x => p i x * W i x := by
      have h := condExp_mul_of_stronglyMeasurable_right (μ := μ) (m := m)
        (f := (A i).indicator (fun _ => (1:ℝ))) (g := W i) (hW_sm i) (hW1_int i)
        ((integrable_const (1:ℝ)).indicator (hA.measurable i))
      rw [← hpe i] at h
      exact h
    calc ∫ x, p i x * W i x ∂μ
        = ∫ x, condExp m μ (fun x => ((A i).indicator (fun _ => (1:ℝ))) x * W i x) x ∂μ :=
          integral_congr_ae hce.symm
      _ = ∫ x, ((A i).indicator (fun _ => (1:ℝ))) x * W i x ∂μ := integral_condExp hm
  have hsumWeq_ae : (fun x => ∑ i, ((A i).indicator (fun _ => (1:ℝ))) x * W i x)
      =ᵐ[μ] (fun x => ∑ j, Real.negMulLog (r j x)) := by
    have hall : ∀ᵐ x ∂μ, ∀ i,
        (((A i).indicator (fun _ => (1:ℝ))) * W i) x
          = (((A i).indicator (fun _ => (1:ℝ))) * (fun x => ∑ j, Real.negMulLog (r j x))) x :=
      Filter.eventually_all.mpr (fun i => hWeq i)
    filter_upwards [hall] with x hx
    calc ∑ i, ((A i).indicator (fun _ => (1:ℝ))) x * W i x
        = ∑ i, ((A i).indicator (fun _ => (1:ℝ))) x * (∑ j, Real.negMulLog (r j x)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simpa only [Pi.mul_apply] using hx i
      _ = (∑ i, ((A i).indicator (fun _ => (1:ℝ))) x) * (∑ j, Real.negMulLog (r j x)) := by
          rw [Finset.sum_mul]
      _ = (∑ j, Real.negMulLog (r j x)) := by
          rw [← Finset.sum_apply, congrFun (sum_indicator_eq_one hA) x, one_mul]
  have hint_W_sum : Integrable (fun x => ∑ i, p i x * W i x) μ :=
    integrable_finsetSum _ (fun i _ => hpW_int i)
  have hint_nmlp_sum : Integrable (fun x => ∑ i, Real.negMulLog (p i x)) μ :=
    integrable_finsetSum _ (fun i _ => hnml_p_int i)
  have hint_1W_sum : Integrable (fun x => ∑ i, ((A i).indicator (fun _ => (1:ℝ))) x * W i x) μ :=
    integrable_finsetSum _ (fun i _ => hW1_int i)
  calc ∫ x, ∑ i, ∑ j, Real.negMulLog (q i j x) ∂μ
      = ∫ x, (∑ i, Real.negMulLog (p i x) + ∑ i, p i x * W i x) ∂μ := integral_congr_ae hmain_ae
    _ = ∫ x, ∑ i, Real.negMulLog (p i x) ∂μ + ∫ x, ∑ i, p i x * W i x ∂μ :=
          integral_add hint_nmlp_sum hint_W_sum
    _ = ∫ x, ∑ i, Real.negMulLog (p i x) ∂μ + ∑ i, ∫ x, p i x * W i x ∂μ := by
          rw [integral_finsetSum Finset.univ (fun i _ => hpW_int i)]
    _ = ∫ x, ∑ i, Real.negMulLog (p i x) ∂μ
          + ∑ i, ∫ x, ((A i).indicator (fun _ => (1:ℝ))) x * W i x ∂μ := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => hpull i)
    _ = ∫ x, ∑ i, Real.negMulLog (p i x) ∂μ
          + ∫ x, ∑ i, ((A i).indicator (fun _ => (1:ℝ))) x * W i x ∂μ := by
          rw [integral_finsetSum Finset.univ (fun i _ => hW1_int i)]
    _ = ∫ x, ∑ i, Real.negMulLog (p i x) ∂μ + ∫ x, ∑ j, Real.negMulLog (r j x) ∂μ := by
          congr 1
          exact integral_congr_ae hsumWeq_ae
theorem Hcond_joinPart_gen {X : Type} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P Q : Work.EKLContract.FinPart X) :
    @Work.EKLContract.Hcond X mX μ (@joinPart__USCBasic X mX P Q) m
      = @Work.EKLContract.Hcond X mX μ P m
        + @Work.EKLContract.Hcond X mX μ Q (m ⊔ @Work.EKLContract.partSigma X mX P) := by
  classical
  by_cases hm : m ≤ mX
  · have hre := Hcond_joinPart_reindex (m := m) (μ := μ) P Q
    have hchain := Hcond_fam_chain (m := m) (μ := μ) P.parts Q.parts
      (isMPart_parts__Hcond_joinPart P) (isMPart_parts__Hcond_joinPart Q) hm
    simp only [Work.EKLContract.Hcond] at hre ⊢
    rw [hre]
    exact hchain
  · have hj : ¬ (m ⊔ @Work.EKLContract.partSigma X mX P) ≤ mX :=
      fun h => hm (le_trans le_sup_left h)
    have h0 := Work.EKLC6Core.Hcond_eq_zero_of_not_le (m := m) (μ := μ) P hm
    have h1 := Work.EKLC6Core.Hcond_eq_zero_of_not_le (m := m ⊔ @Work.EKLContract.partSigma X mX P)
      (μ := μ) Q hj
    have h2 := Work.EKLC6Core.Hcond_eq_zero_of_not_le (m := m) (μ := μ)
      (@joinPart__USCBasic X mX P Q) hm
    rw [h0, h1, h2]; ring

theorem Hcond_joinPart (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ] (P Q : Work.EKLContract.FinPart Work.EKLContract.X3) (m : MeasurableSpace Work.EKLContract.X3) : @Work.EKLContract.Hcond Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ (@Work.EKLComp.joinPart__USCBasic Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 P Q) m = @Work.EKLContract.Hcond Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ P m + @Work.EKLContract.Hcond Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ Q (m ⊔ @Work.EKLContract.partSigma Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 P) := by
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  exact Hcond_joinPart_gen (m := m) μ P Q

end Work.EKLComp
