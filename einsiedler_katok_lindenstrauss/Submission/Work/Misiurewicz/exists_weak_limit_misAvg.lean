import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLComp.polishSpace_X3
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.Misiurewicz.integral_misAvg_diff_le
import Submission.Work.Misiurewicz.vMove_lt_iff
import Submission.Work.Misiurewicz.misAvgMeasure_prob_supp

namespace Work.Misiurewicz

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLComp

noncomputable section


/-- Asymptotic invariance of a weak limit: if a sequence of probability measures `μs n`
converges weakly to `ν` and the pushforwards under `x ↦ g • x` stay asymptotically close to
`μs n` (in the sense that the integrals against every bounded continuous function differ by a
quantity tending to `0`), then `ν` is invariant under `x ↦ g • x`. -/
lemma map_smulMap_eq_self_aux (g : SL3) (μs : ℕ → Measure X3) (ν : Measure X3)
    [IsProbabilityMeasure ν]
    (hweak : ∀ f : BoundedContinuousFunction X3 ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μs n)) atTop (nhds (∫ x, f x ∂ν)))
    (hdelta : ∀ f : BoundedContinuousFunction X3 ℝ,
      Tendsto (fun n => (∫ x, f x ∂Measure.map (smulMap g) (μs n)) - ∫ x, f x ∂(μs n))
        atTop (nhds 0)) :
    Measure.map (smulMap g) ν = ν := by
  haveI : IsFiniteMeasure ν := ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (Measure.map (smulMap g) ν) := Measure.isFiniteMeasure_map ν (smulMap g)
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let cg : C(X3, X3) := ⟨smulMap g, continuous_smulMap g⟩
  have hint : ∀ μ : Measure X3, ∫ x, f x ∂Measure.map (smulMap g) μ
      = ∫ x, (f.compContinuous cg) x ∂μ := by
    intro μ
    rw [MeasureTheory.integral_map (continuous_smulMap g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    simp only [BoundedContinuousFunction.compContinuous_apply]
    rfl
  have hA : Tendsto (fun n => ∫ x, f x ∂Measure.map (smulMap g) (μs n)) atTop
      (nhds (∫ x, f x ∂Measure.map (smulMap g) ν)) := by
    have h := hweak (f.compContinuous cg)
    simpa only [hint] using h
  have hB : Tendsto (fun n => ∫ x, f x ∂(μs n)) atTop (nhds (∫ x, f x ∂ν)) := hweak f
  have hdiff := hA.sub hB
  have : (∫ x, f x ∂Measure.map (smulMap g) ν) - (∫ x, f x ∂ν) = 0 :=
    tendsto_nhds_unique hdiff (hdelta f)
  exact sub_eq_zero.mp this

theorem exists_weak_limit_misAvg (K : Set Work.EKLContract.X3) (hK : IsCompact K)
    (g : Work.EKLContract.SL3) (hgK : ∀ x ∈ K, g • x ∈ K) (a : ℕ → ℕ)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop)
    (E : ℕ → Finset Work.EKLContract.X3) (hEK : ∀ j, (E j : Set Work.EKLContract.X3) ⊆ K)
    (hne : ∀ j, (E j).Nonempty) :
    ∃ ν : MeasureTheory.Measure Work.EKLContract.X3, MeasureTheory.IsProbabilityMeasure ν ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ν K = 1 ∧ MeasureTheory.MeasurePreserving (Work.EKLComp.smulMap g) ν ν ∧
        ∀ f : BoundedContinuousFunction Work.EKLContract.X3 ℝ,
          Filter.Tendsto (fun j => ∫ x, f x ∂(Work.EKLComp.misAvgMeasure g (a (φ j)) (Work.EKLComp.unifMeasure (E (φ j))))) Filter.atTop (nhds (∫ x, f x ∂ν))) := by
  classical
  -- A threshold beyond which `a` is positive.
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ j ≥ N₀, 0 < a j := by
    obtain ⟨N₀, hN₀⟩ := Filter.tendsto_atTop_atTop.mp ha 1
    exact ⟨N₀, fun j hj => lt_of_lt_of_le Nat.zero_lt_one (hN₀ j hj)⟩
  have hpos : ∀ j : ℕ, 0 < a (N₀ + j) := fun j => hN₀ _ (Nat.le_add_right N₀ j)
  -- The shifted sequence of Misiurewicz averages, as probability measures.
  let y : ℕ → ProbabilityMeasure X3 := fun j =>
    ⟨misAvgMeasure g (a (N₀ + j)) (unifMeasure (E (N₀ + j))),
      (misAvgMeasure_prob_supp g K hgK (E (N₀ + j)) (hEK _) (hne _) (hpos j)).1⟩
  have hy_eq : ∀ j, (y j : Measure X3)
      = misAvgMeasure g (a (N₀ + j)) (unifMeasure (E (N₀ + j))) := fun j => rfl
  have hy_supp : ∀ j, (y j : Measure X3) Kᶜ = 0 := fun j =>
    (misAvgMeasure_prob_supp g K hgK (E (N₀ + j)) (hEK _) (hne _) (hpos j)).2
  -- The compact set of probability measures carried by `K` (Prokhorov).
  have hS : IsCompact {μ : ProbabilityMeasure X3 | ∀ n : ℕ, μ Kᶜ ≤ (0 : NNReal)} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le (u := fun _ => 0)
      (K := fun _ => K) tendsto_const_nhds (fun _ => hK) (Or.inr fun _ _ _ => subset_rfl)
  have hyS : ∀ j, y j ∈ {μ : ProbabilityMeasure X3 | ∀ n : ℕ, μ Kᶜ ≤ (0 : NNReal)} := by
    intro j n
    have h : (y j Kᶜ : ℝ≥0∞) = 0 := by
      rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hy_supp j]
    exact le_of_eq (ENNReal.coe_eq_zero.mp h)
  -- Extract a convergent subsequence.
  obtain ⟨aν, haνS, χ, hχmono, hχtend⟩ := hS.tendsto_subseq hyS
  refine ⟨(aν : Measure X3), (inferInstance : IsProbabilityMeasure (aν : Measure X3)),
    (fun j => N₀ + χ j), ?_, ?_, ?_, ?_⟩
  · -- strict monotonicity of the index shift
    intro i j hij
    exact Nat.add_lt_add_left (hχmono hij) N₀
  · -- the limit measure is carried by `K`
    have hνsupp : (aν : Measure X3) Kᶜ = 0 := by
      have h : aν Kᶜ = 0 := le_antisymm (haνS 0) bot_le
      have h' : (aν Kᶜ : ℝ≥0∞) = 0 := by rw [h]; rfl
      rwa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h'
    have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
    have hKu : (aν : Measure X3) K ≠ ⊤ := by
      have hle : (aν : Measure X3) K ≤ (aν : Measure X3) Set.univ := measure_mono (Set.subset_univ K)
      rw [measure_univ] at hle
      exact ne_of_lt (hle.trans_lt ENNReal.one_lt_top)
    have hcompl : (aν : Measure X3) Set.univ - (aν : Measure X3) K = 0 := by
      rw [← measure_compl hKmeas hKu]
      exact hνsupp
    have hle : (aν : Measure X3) Set.univ ≤ (aν : Measure X3) K := tsub_eq_zero_iff_le.mp hcompl
    have hge : (aν : Measure X3) K ≤ (aν : Measure X3) Set.univ := measure_mono (Set.subset_univ K)
    rw [le_antisymm hge hle, measure_univ]
  · -- invariance of the limit under `x ↦ g • x`
    have hweak : ∀ f : BoundedContinuousFunction X3 ℝ,
        Tendsto (fun j => ∫ x, f x ∂(y (χ j) : Measure X3)) atTop
          (nhds (∫ x, f x ∂(aν : Measure X3))) := by
      intro f
      have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hχtend) f
      simpa only [Function.comp_apply] using h
    have hdelta : ∀ f : BoundedContinuousFunction X3 ℝ,
        Tendsto (fun j => (∫ x, f x ∂Measure.map (smulMap g) (y (χ j) : Measure X3))
          - ∫ x, f x ∂(y (χ j) : Measure X3)) atTop (nhds 0) := by
      intro f
      have hbound : ∀ j, |(∫ x, f x ∂Measure.map (smulMap g) (y (χ j) : Measure X3))
          - ∫ x, f x ∂(y (χ j) : Measure X3)| ≤ 2 * ‖f‖ / (a (N₀ + χ j) : ℝ) := by
        intro j
        haveI : IsProbabilityMeasure (unifMeasure (E (N₀ + χ j))) :=
          ⟨unifMeasure_univ (E (N₀ + χ j)) (hne _)⟩
        have h := integral_misAvg_diff_le g (hpos (χ j)) (unifMeasure (E (N₀ + χ j))) f
        simpa only [hy_eq] using h
      have hshift : Tendsto (fun j => N₀ + χ j) atTop atTop :=
        tendsto_atTop_mono (fun j => Nat.le_add_left (χ j) N₀) hχmono.tendsto_atTop
      have hlim : Tendsto (fun j => 2 * ‖f‖ / (a (N₀ + χ j) : ℝ)) atTop (nhds 0) := by
        have hcast : Tendsto (fun j => ((a (N₀ + χ j) : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (ha.comp hshift)
        simpa only using hcast.const_div_atTop (2 * ‖f‖)
      have h1 : Tendsto (fun j => |(∫ x, f x ∂Measure.map (smulMap g) (y (χ j) : Measure X3))
          - ∫ x, f x ∂(y (χ j) : Measure X3)|) atTop (nhds 0) :=
        squeeze_zero (fun j => abs_nonneg _) hbound hlim
      have hnorm : Tendsto (fun j => ‖(∫ x, f x ∂Measure.map (smulMap g) (y (χ j) : Measure X3))
          - ∫ x, f x ∂(y (χ j) : Measure X3)‖) atTop (nhds 0) := by
        simpa only [Real.norm_eq_abs] using h1
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    refine ⟨(continuous_smulMap g).measurable, ?_⟩
    exact map_smulMap_eq_self_aux g (fun j => (y (χ j) : Measure X3)) (aν : Measure X3)
      hweak hdelta
  · -- weak convergence along the subsequence
    intro f
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hχtend) f
    simpa only [Function.comp_apply, hy_eq] using h

end

end Work.Misiurewicz
