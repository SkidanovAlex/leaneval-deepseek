import Mathlib
import Submission.Work.EKLC6Core.atomInfo_ae_eq_aux_along
import Submission.Work.EKLC6Core.HcondSigFree.orbit_telescope_gl_mp

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **Telescoping of Pisa 7.34 along the orbit, `ACovariantAlong` version.**

This is `Work.EKLC6Core.HcondSigFree.orbit_telescope_gl_mp` with the full covariance
`ACovariant ν X''` replaced by the covariance along the integer multiples of the single
direction `t` (`ACovariantAlong ν t X''`); the pointwise identity of Pisa 7.34 in that form is
`Work.EKLC6Core.atomInfo_ae_eq_aux_along`, and the telescoping argument is unchanged. -/
theorem orbit_telescope_gl_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      (∑ j ∈ Finset.range n, Work.EKLC6Core.atomInfo A U ν t
          (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x))
        = Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x)
              (Work.EKLContract.shape A U
                (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x))).toReal)
          - Real.log ((ν x (Work.EKLContract.shape A U x)).toReal)
          + ∑ j ∈ Finset.range n, Work.EKLC6Core.growthFun U ν t
              (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j+1]) x) := by
  classical
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  -- the pointwise identity of Pisa 7.34, in the along-`ℤ·t` form
  have hbase := Work.EKLC6Core.atomInfo_ae_eq_aux_along (t := t) hL hU hcov hX'' hmp hplaq hZ
  -- push it along the flow: the identity holds at every iterate
  have hAtomAe : ∀ᵐ x ∂μ, ∀ k : ℕ,
      Work.EKLC6Core.atomInfo A U ν t
          (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k]) x)
        = Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k+1]) x)
              (Work.EKLContract.shape A U
                (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k+1]) x))).toReal)
          - Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k]) x)
              (Work.EKLContract.shape A U
                (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k]) x))).toReal)
          + Work.EKLC6Core.growthFun U ν t
              (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k+1]) x) := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    have hk := (hmp.iterate k).quasiMeasurePreserving.ae hbase
    filter_upwards [hk] with x hx
    simpa only [Function.iterate_succ_apply'] using hx
  filter_upwards [hAtomAe] with x hAtom
  intro n
  -- the telescoping of the `ψ`-difference
  have hsplit : (∑ j ∈ Finset.range n, Work.EKLC6Core.atomInfo A U ν t
        (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x))
      = (∑ j ∈ Finset.range n,
          (Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j+1]) x)
                (Work.EKLContract.shape A U
                  (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j+1]) x))).toReal)
            - Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x)
                (Work.EKLContract.shape A U
                  (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x))).toReal)))
        + ∑ j ∈ Finset.range n, Work.EKLC6Core.growthFun U ν t
              (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j+1]) x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [hAtom j])
  have htel := Finset.sum_range_sub
    (fun j : ℕ => Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x)
        (Work.EKLContract.shape A U
          (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x))).toReal)) n
  simp only [Function.iterate_zero_apply] at htel
  rw [hsplit, htel]

end Work.EKLC6Core
