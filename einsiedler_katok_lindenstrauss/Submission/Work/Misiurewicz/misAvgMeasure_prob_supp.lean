import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLComp.X3Background

namespace Work.Misiurewicz

open MeasureTheory
open Work.EKLComp Work.EKLContract
open scoped ENNReal

noncomputable section

/-!
# The Misiurewicz averaged measure of the uniform measure on a finite set

`Work.EKLComp.misAvgMeasure g N σ` is the Cesàro average `N⁻¹ ∑_{k<N} (x ↦ g^k • x)_* σ`.
For `σ = Work.EKLComp.unifMeasure E` the uniform measure on a nonempty finite set `E` this is
again a probability measure, and — the point of this file — it is *supported on any
`g`-forward-invariant set `K ⊇ E`*, i.e. it gives measure `0` to `Kᶜ`, even when `K` is not
measurable.

The argument is completely explicit: `unifMeasure E` is the average of the Dirac masses at the
points of `E`, pushforwards of Dirac masses are Dirac masses (`Measure.map_dirac'`), and a Dirac
mass carried by a point of `K` gives measure `0` to `Kᶜ` (`Measure.dirac_apply`, which needs
`X₃` to have measurable singletons — available since `X₃` is Hausdorff with the Borel
σ-algebra).
-/

/-- `X₃ = SL₃(ℝ)/SL₃(ℤ)` has measurable singletons: it is Hausdorff and carries the Borel
σ-algebra, so its (closed) singletons are measurable. -/
lemma measurableSingletonClass_X3 : MeasurableSingletonClass X3 :=
  ⟨fun _ => by
    haveI : T2Space X3 := X3Background.1
    exact isClosed_singleton.measurableSet⟩

/-- Evaluating the Misiurewicz averaged measure on an arbitrary set. -/
lemma misAvgMeasure_apply (g : SL3) (N : ℕ) (σ : Measure X3) (s : Set X3) :
    misAvgMeasure g N σ s
      = (N : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range N, (Measure.map (smulMap (g ^ k)) σ) s := by
  rw [misAvgMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

/-- The uniform measure on a nonempty finite set is a probability measure. -/
lemma unifMeasure_univ (E : Finset X3) (hne : E.Nonempty) : unifMeasure E Set.univ = 1 := by
  have hsum : (∑ x ∈ E, (Measure.dirac x : Measure X3) Set.univ) = (E.card : ℝ≥0∞) := by simp
  rw [unifMeasure, Measure.smul_apply, Measure.finsetSum_apply, hsum, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using Finset.card_ne_zero.mpr hne)
    (ENNReal.natCast_ne_top _)

/-- Pushing forward the uniform measure on `E` along the homeomorphism `x ↦ u • x`. -/
lemma map_unifMeasure_eq (u : SL3) (E : Finset X3) :
    Measure.map (smulMap u) (unifMeasure E)
      = (E.card : ℝ≥0∞)⁻¹ • ∑ x ∈ E, Measure.dirac (u • x) := by
  rw [unifMeasure, Measure.map_smul _ (continuous_smulMap _).measurable.aemeasurable]
  congr 1
  rw [Measure.map_finset_sum (continuous_smulMap u).aemeasurable]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Measure.map_dirac' (continuous_smulMap u).measurable x

/-- Averaging probability measures (with `N > 0` terms) gives a probability measure. -/
lemma misAvgMeasure_isProbabilityMeasure (g : SL3) {N : ℕ} (hN : 0 < N)
    (σ : Measure X3) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (misAvgMeasure g N σ) := by
  rw [isProbabilityMeasure_iff, misAvgMeasure_apply]
  have hterm : ∀ k ∈ Finset.range N, (Measure.map (smulMap (g ^ k)) σ) Set.univ = 1 :=
    fun k _ =>
      measure_univ
  have hsum : (∑ k ∈ Finset.range N, (Measure.map (smulMap (g ^ k)) σ) Set.univ)
      = (N : ℝ≥0∞) := by
    trans ∑ k ∈ Finset.range N, (1 : ℝ≥0∞)
    · exact Finset.sum_congr rfl hterm
    · simp
  rw [hsum]
  exact ENNReal.inv_mul_cancel (by simpa using hN.ne') (ENNReal.natCast_ne_top N)

/-- The iterates of `x ↦ g • x` preserve any `g`-forward-invariant set. -/
lemma pow_smul_mem_of_mem (g : SL3) {K : Set X3} (hgK : ∀ x ∈ K, g • x ∈ K) :
    ∀ k : ℕ, ∀ x ∈ K, (g ^ k) • x ∈ K := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
      intro x hx
      rw [pow_succ', mul_smul]
      exact hgK _ (ih x hx)

theorem misAvgMeasure_prob_supp (g : Work.EKLContract.SL3) (K : Set Work.EKLContract.X3)
    (hgK : ∀ x ∈ K, g • x ∈ K) (E : Finset Work.EKLContract.X3) (hE : (E : Set Work.EKLContract.X3) ⊆ K)
    (hne : E.Nonempty) {N : ℕ} (hN : 0 < N) :
    MeasureTheory.IsProbabilityMeasure (Work.EKLComp.misAvgMeasure g N (Work.EKLComp.unifMeasure E)) ∧
      Work.EKLComp.misAvgMeasure g N (Work.EKLComp.unifMeasure E) Kᶜ = 0 := by
  haveI hmsc : MeasurableSingletonClass X3 := measurableSingletonClass_X3
  haveI hprob : IsProbabilityMeasure (unifMeasure E) := ⟨unifMeasure_univ E hne⟩
  refine ⟨misAvgMeasure_isProbabilityMeasure g hN (unifMeasure E), ?_⟩
  -- Each pushforward of `unifMeasure E` is supported on `(g^k) • E ⊆ K`.
  have key : ∀ k ∈ Finset.range N, (Measure.map (smulMap (g ^ k)) (unifMeasure E)) Kᶜ = 0 := by
    intro k _
    rw [map_unifMeasure_eq (g ^ k) E, Measure.smul_apply, Measure.finsetSum_apply]
    have hterm : ∀ x ∈ E, (Measure.dirac ((g ^ k) • x) : Measure X3) Kᶜ = 0 := by
      intro x hx
      have hmem : (g ^ k) • x ∈ K := pow_smul_mem_of_mem g hgK k x (hE hx)
      rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hmem)]
    rw [Finset.sum_eq_zero hterm, smul_zero]
  rw [misAvgMeasure_apply, Finset.sum_eq_zero key, mul_zero]

end

end Work.Misiurewicz
