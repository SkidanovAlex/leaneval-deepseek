import Mathlib
import Submission.Work.EKLC6Core.radius_independence
import Submission.Work.EKLC6Core.ae_forall_smul_mem
import Submission.Work.EKLC6Core.ae_forall_smul_mem_mp
import Submission.Work.EKLC6Core.log_mass_sandwich

/-!
# `EKLC6Core.HcondSigFree.radius_independence_mp`

`Work.EKLC6Core.radius_independence` proves that the exponential rate of the leafwise masses
`ν (aDiag t ^ n • x) (V r ∩ U)` is independent of the radius `r`, under the hypothesis
`IsAInvariant μ` (invariance under *every* diagonal flow).  Here the invariance is weakened to
the single flow `x ↦ aDiag t • x`, which is exactly what the two uses of `IsAInvariant` need:

* the Birkhoff ergodic theorem along the orbit `n ↦ (aDiag t)^n • x`, which needs only
  `MeasurePreserving (aDiag t ·) μ μ`;
* the a.e. statement that the whole forward orbit of `x` stays in the conull set `X' ∩ X''`,
  which becomes `Work.EKLC6Core.ae_forall_smul_mem_mp` (a countable intersection of preimages
  of a null set under the iterates of a single measure-preserving map).

The pointwise two-sided estimate is the extracted lemma `Work.EKLC6Core.log_mass_sandwich`;
the rest is the same squeeze as in `radius_independence`.
-/

namespace Work.EKLC6Core.HcondSigFree

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

theorem radius_independence_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
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
    exact Work.EKLC6Core.log_mass_sandwich (r := r) (k := k) (x := x) t hL hU hcov hcontr
      hsmall hbig
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

end Work.EKLC6Core.HcondSigFree
