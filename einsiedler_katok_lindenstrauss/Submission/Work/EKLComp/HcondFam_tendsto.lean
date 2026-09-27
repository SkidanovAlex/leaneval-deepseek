import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

/-- The conditional expectation of the indicator of a set, with respect to a sub-σ-algebra `m`
of the ambient σ-algebra, lies almost everywhere in `[0,1]`. -/
theorem condExp_indicator_mem_Icc {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (m : MeasurableSpace X) (hm : m ≤ mX) (s : Set X) :
    ∀ᵐ x ∂μ, MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Classical.em (Integrable (s.indicator (fun _ => (1 : ℝ))) μ) with hf | hf
  · have hlow : (0 : X → ℝ) ≤ᵐ[μ]
        MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) :=
      MeasureTheory.condExp_nonneg
        (Filter.Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    have hup : MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ] (1 : X → ℝ) := by
      have h : MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ]
          MeasureTheory.condExp m μ (fun _ => (1 : ℝ)) :=
        MeasureTheory.condExp_mono hf (integrable_const (1 : ℝ))
          (Filter.Eventually.of_forall (fun x => by
            by_cases hx : x ∈ s
            · simp [Set.indicator_of_mem hx]
            · simp [Set.indicator_of_notMem hx]))
      rwa [MeasureTheory.condExp_const hm (1 : ℝ)] at h
    filter_upwards [hlow, hup] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  · rw [MeasureTheory.condExp_of_not_integrable hf]
    exact Filter.Eventually.of_forall (fun x => by simp)

theorem HcondFam_tendsto {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type} [Fintype ι] (A : ι → Set X) (mseq : ℕ → MeasurableSpace X)
    (hmono : Monotone mseq) (hle : ∀ n, mseq n ≤ mX) :
    Filter.Tendsto (fun n => Work.EKLComp.Core.HcondFam X μ A (mseq n)) Filter.atTop
      (nhds (Work.EKLComp.Core.HcondFam X μ A (⨆ n, mseq n))) := by
  classical
  let f : ι → X → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ))
  -- Almost-everywhere convergence of each conditional expectation (Lévy's upward theorem).
  have hconv_i : ∀ i, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => MeasureTheory.condExp (mseq n) μ (f i) x) Filter.atTop
        (nhds (MeasureTheory.condExp (⨆ n, mseq n) μ (f i) x)) := by
    intro i
    have h := MeasureTheory.tendsto_ae_condExp (μ := μ)
      (ℱ := (⟨mseq, hmono, hle⟩ : MeasureTheory.Filtration ℕ mX)) (f i)
    exact h
  -- Almost-everywhere boundedness of each summand.
  have hmem_i : ∀ n i, ∀ᵐ x ∂μ, MeasureTheory.condExp (mseq n) μ (f i) x ∈ Set.Icc (0 : ℝ) 1 :=
    fun n i => condExp_indicator_mem_Icc μ (mseq n) (hle n) (A i)
  -- Strong measurability of the integrand.
  have haesm : ∀ n, MeasureTheory.AEStronglyMeasurable
      (fun x => ∑ i, Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x)) μ := by
    intro n
    have h : MeasureTheory.AEStronglyMeasurable
        (∑ i : ι, fun x => Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x)) μ :=
      Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
        Real.continuous_negMulLog.comp_aestronglyMeasurable
          ((MeasureTheory.stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable))
    simpa [Finset.sum_fn] using h
  -- Pointwise domination by the (integrable) constant `card ι`.
  have hbdd : ∀ n, ∀ᵐ x ∂μ,
      ‖∑ i, Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x)‖ ≤ (Fintype.card ι : ℝ) := by
    intro n
    have hmem : ∀ᵐ x ∂μ, ∀ i,
        MeasureTheory.condExp (mseq n) μ (f i) x ∈ Set.Icc (0 : ℝ) 1 :=
      (MeasureTheory.ae_all_iff (μ := μ)).mpr (fun i => hmem_i n i)
    filter_upwards [hmem] with x hx
    have hnn : 0 ≤ ∑ i, Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x) :=
      Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hx i).1 (hx i).2)
    rw [Real.norm_of_nonneg hnn]
    calc ∑ i, Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x)
        ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
            have h1 := Real.negMulLog_le_one_sub_self (hx i).1
            linarith [(hx i).1])
      _ = (Fintype.card ι : ℝ) := by simp
  -- Almost-everywhere convergence of the integrand.
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n => ∑ i, Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x)) Filter.atTop
      (nhds (∑ i, Real.negMulLog (MeasureTheory.condExp (⨆ n, mseq n) μ (f i) x))) := by
    have hterm : ∀ i, ∀ᵐ x ∂μ, Filter.Tendsto
        (fun n => Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x)) Filter.atTop
        (nhds (Real.negMulLog (MeasureTheory.condExp (⨆ n, mseq n) μ (f i) x))) := by
      intro i
      filter_upwards [hconv_i i] with x hx
      exact (Real.continuous_negMulLog.tendsto _).comp hx
    have hterm' := (MeasureTheory.ae_all_iff (μ := μ)).mpr hterm
    filter_upwards [hterm'] with x hx
    exact tendsto_finsetSum Finset.univ (fun i _ => hx i)
  -- Dominated convergence passes to the integral.
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ∑ i, Real.negMulLog (MeasureTheory.condExp (mseq n) μ (f i) x))
      (f := fun x => ∑ i, Real.negMulLog (MeasureTheory.condExp (⨆ n, mseq n) μ (f i) x))
      (fun _ : X => (Fintype.card ι : ℝ))
      haesm (integrable_const _) hbdd hlim
  simpa only [Core.HcondFam] using hmain

end Work.EKLComp
