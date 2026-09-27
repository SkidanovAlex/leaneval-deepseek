import Mathlib
import Submission.Work.EKLC6Core.AlongAuxSandwich
import Submission.Work.EKLC6Core.HcondSigFree.radius_independence_mp
import Submission.Work.EKLC6Core.radius_independence
import Submission.Work.EKLC6Core.ae_forall_smul_mem_mp
import Submission.Work.EKLC6Core.tendsto_inv_sum_shifted
import Submission.Work.EKLC6Core.box_sandwich
import Submission.Work.EKLC6Core.covAlong

/-!
# `EKLC6Core.radius_independence_along`

`Work.EKLC6Core.HcondSigFree.radius_independence_mp` with the full `A`-covariance
`ACovariant ν X''` replaced by the covariance along the integer multiples of the single
direction `t` (`Work.EKLC6Core.ACovariantAlong ν t X''`).

The proof is the one of `radius_independence_mp`: the pointwise two-sided estimate
`log_mass_sandwich` is replaced by its `_along` version `log_mass_sandwich_alongAux`
(in `AlongAuxSandwich`), and everything else (the Birkhoff theorem along the single
orbit `n ↦ (aDiag t)^n • x`, the a.e. statement `ae_forall_smul_mem_mp`, the radius
sandwich `box_sandwich` and the limit algebra) uses the covariance nowhere and is copied
verbatim.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem radius_independence_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ X''ᶜ = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        ((ν (Work.EKLContract.aDiag t ^ n • x)
          (Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3))).toReal))
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨k, hkpos, hsmall, hbig⟩ := box_sandwich hU hcontr hr
  have hOrb := Work.EKLC6Core.ae_forall_smul_mem_mp hmp hL.conull hX''
  have hBirk := Work.EKLComp.birkhoff_all μ (fun y : X3 => aDiag t • y) hmp
      (growthFun U ν t) hint
  filter_upwards [hOrb, hBirk] with x hxOrb hxBirk
  have hces : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
        growthFun U ν t (aDiag ((j : ℝ) • t) • x)) Filter.atTop
      (nhds (μ[growthFun U ν t |
        MeasurableSpace.invariants (fun y : X3 => aDiag t • y)] x)) := by
    refine hxBirk.congr' (Filter.Eventually.of_forall (fun n => ?_))
    simp only [Work.EKLComp.Birkhoff.birkA_def]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ri_iterate_aDiag_smul]
  obtain ⟨hA1, hA2⟩ := tendsto_inv_sum_shifted hces k
  have hest : ∀ n : ℕ, k ≤ n →
      -(∑ i ∈ Finset.Icc 1 k, growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))
          ≤ Real.log ((ν (aDiag (((n : ℕ) : ℝ) • t) • x)
              (V r ∩ (U : Set SL3))).toReal) ∧
        Real.log ((ν (aDiag (((n : ℕ) : ℝ) • t) • x)
              (V r ∩ (U : Set SL3))).toReal)
          ≤ ∑ i ∈ Finset.Icc 1 k,
              growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x) := by
    intro n hn
    exact Work.EKLC6Core.log_mass_sandwich_alongAux (r := r) (k := k) (x := x) t hL hU hcov
      hcontr hsmall hbig
      (fun m j => by
        rw [aDiag_smul_mul, ri_add_smul_nat]
        exact hxOrb (m + j)) hn
  have hrew : (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        ((ν (aDiag (((n : ℕ) : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal))
      = (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
        ((ν (aDiag t ^ n • x) (V r ∩ (U : Set SL3))).toReal)) := by
    funext n
    rw [aDiag_real_nsmul]
  rw [← hrew]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ => -((n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k,
        growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)))
    (h := fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k,
        growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) ?_ ?_ ?_ ?_
  · have h := hA2.neg
    simpa using h
  · exact hA1
  · filter_upwards [Filter.eventually_ge_atTop k] with n hn
    have h := (hest n hn).1
    calc -((n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))
        = (n : ℝ)⁻¹ * (-(∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))) := by ring
      _ ≤ (n : ℝ)⁻¹ * Real.log ((ν (aDiag (((n : ℕ) : ℝ) • t) • x)
            (V r ∩ (U : Set SL3))).toReal) :=
          mul_le_mul_of_nonneg_left h (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop k] with n hn
    exact mul_le_mul_of_nonneg_left (hest n hn).2 (by positivity)

end Work.EKLC6Core
