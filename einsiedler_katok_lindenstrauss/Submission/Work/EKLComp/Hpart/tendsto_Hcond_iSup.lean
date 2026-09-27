import Mathlib
import Submission.Work.EKLComp.Entropy

/-!
# `Hcond (m n) → Hcond (⨆ n, m n)` for a monotone sequence of sub-σ-algebras

`Work.EKLContract.Hcond μ P m = ∫ ∑_i -E(1_{P_i} | m) log E(1_{P_i} | m) dμ` is the conditional
entropy of the finite partition `P` with respect to an arbitrary sub-σ-algebra `m`.

For a monotone sequence `m : ℕ → MeasurableSpace X` of sub-σ-algebras of `mX`, Lévy's upward
theorem (`MeasureTheory.tendsto_ae_condExp`) gives, for each atom `P_i` of `P`, the a.e.
convergence of the conditional expectations `E(1_{P_i} | m n) → E(1_{P_i} | ⨆ n, m n)`.
As each conditional expectation of an indicator lies a.e. in `[0,1]` (probability measure),
the integrands are dominated by the constant `P.n`, and dominated convergence upgrades the
a.e. convergence to convergence of the integrals.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1000000

namespace Work.EKLComp.Hpart

/-- The conditional expectation of the indicator function of an arbitrary set, with respect to a
sub-σ-algebra `m ≤ mX` of a probability measure, lies almost everywhere in `[0,1]`. -/
theorem condExp_indicator_one_mem_Icc {X : Type} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (m : MeasurableSpace X) (hm : m ≤ mX) (s : Set X) :
    ∀ᵐ x ∂μ, MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Classical.em (Integrable (s.indicator (fun _ => (1 : ℝ))) μ) with hf | hf
  · have hlow : 0 ≤ᵐ[μ] MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) :=
      MeasureTheory.condExp_nonneg
        (Filter.Eventually.of_forall (Set.indicator_nonneg (fun _ _ => zero_le_one)))
    have hup : MeasureTheory.condExp m μ (s.indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ]
        (fun _ => (1 : ℝ)) := by
      have h2 := MeasureTheory.condExp_mono (m := m) hf (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ s
          · rw [Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx]; norm_num)
      rwa [MeasureTheory.condExp_const hm (1 : ℝ)] at h2
    filter_upwards [hlow, hup] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  · rw [MeasureTheory.condExp_of_not_integrable hf]
    exact Filter.Eventually.of_forall (fun x => by simp)

theorem tendsto_Hcond_iSup {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : Work.EKLContract.FinPart X)
    (m : ℕ → MeasurableSpace X) (hmono : Monotone m) (hle : ∀ n, m n ≤ mX) :
    Filter.Tendsto (fun n => @Work.EKLContract.Hcond X mX μ P (m n)) Filter.atTop
      (nhds (@Work.EKLContract.Hcond X mX μ P (⨆ n, m n))) := by
  classical
  let F : MeasureTheory.Filtration ℕ mX := ⟨m, hmono, hle⟩
  let f : Fin P.n → X → ℝ := fun i => (P.parts i).indicator (fun _ => (1 : ℝ))
  -- Each atom indicator is integrable (probability measure, measurable atom).
  have hfi : ∀ i, Integrable (f i) μ := by
    intro i
    rw [show f i = (P.parts i).indicator (fun _ => (1 : ℝ)) from rfl,
      integrable_indicator_iff (P.measurable i)]
    exact integrableOn_const (measure_ne_top μ _) (by simp)
  -- Lévy's upward theorem: a.e. convergence of each conditional expectation.
  have hconv : ∀ i, ∀ᵐ x ∂μ, Filter.Tendsto (fun n => MeasureTheory.condExp (m n) μ (f i) x)
      Filter.atTop (nhds (MeasureTheory.condExp (⨆ n, m n) μ (f i) x)) := by
    intro i
    have h := MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := F) (f i)
    simpa only [F] using h
  -- Each conditional expectation of an atom indicator lies a.e. in `[0,1]`.
  have hmem : ∀ n i, ∀ᵐ x ∂μ, MeasureTheory.condExp (m n) μ (f i) x ∈ Set.Icc (0 : ℝ) 1 := by
    intro n i
    simpa only [f] using condExp_indicator_one_mem_Icc μ (m n) (hle n) (P.parts i)
  -- Strong measurability of the integrand.
  have haesm : ∀ n, MeasureTheory.AEStronglyMeasurable
      (fun x => ∑ i, Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x)) μ := by
    intro n
    have h : MeasureTheory.AEStronglyMeasurable
        (∑ i : Fin P.n, fun x => Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x)) μ :=
      Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
        Real.continuous_negMulLog.comp_aestronglyMeasurable
          ((MeasureTheory.stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable))
    simpa [Finset.sum_fn] using h
  -- Pointwise (a.e.) domination by the integrable constant `P.n`.
  have hbdd : ∀ n, ∀ᵐ x ∂μ,
      ‖∑ i, Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x)‖ ≤ (P.n : ℝ) := by
    intro n
    have hmem' : ∀ᵐ x ∂μ, ∀ i,
        MeasureTheory.condExp (m n) μ (f i) x ∈ Set.Icc (0 : ℝ) 1 :=
      (MeasureTheory.ae_all_iff (μ := μ)).mpr (fun i => hmem n i)
    filter_upwards [hmem'] with x hx
    have hnn : 0 ≤ ∑ i, Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x) :=
      Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hx i).1 (hx i).2)
    rw [Real.norm_of_nonneg hnn]
    calc ∑ i, Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x)
        ≤ ∑ _i : Fin P.n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
            have h1 := Real.negMulLog_le_one_sub_self (hx i).1
            linarith [(hx i).1])
      _ = (P.n : ℝ) := by simp
  -- Almost-everywhere convergence of the integrand.
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n => ∑ i, Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x)) Filter.atTop
      (nhds (∑ i, Real.negMulLog (MeasureTheory.condExp (⨆ n, m n) μ (f i) x))) := by
    have hterm : ∀ i, ∀ᵐ x ∂μ, Filter.Tendsto
        (fun n => Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x)) Filter.atTop
        (nhds (Real.negMulLog (MeasureTheory.condExp (⨆ n, m n) μ (f i) x))) := by
      intro i
      filter_upwards [hconv i] with x hx
      exact (Real.continuous_negMulLog.tendsto _).comp hx
    have hterm' := (MeasureTheory.ae_all_iff (μ := μ)).mpr hterm
    filter_upwards [hterm'] with x hx
    exact tendsto_finsetSum Finset.univ (fun i _ => hx i)
  -- Dominated convergence upgrades the a.e. convergence to convergence of the integrals.
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ∑ i, Real.negMulLog (MeasureTheory.condExp (m n) μ (f i) x))
      (f := fun x => ∑ i, Real.negMulLog (MeasureTheory.condExp (⨆ n, m n) μ (f i) x))
      (fun _ : X => (P.n : ℝ)) haesm (integrable_const _) hbdd hlim
  simpa only [Work.EKLContract.Hcond, f] using hmain

end Work.EKLComp.Hpart
