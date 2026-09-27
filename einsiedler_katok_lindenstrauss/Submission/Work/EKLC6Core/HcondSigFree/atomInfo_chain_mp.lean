import Mathlib
import Submission.Work.EKLC6Core.atomInfo_chain
import Submission.Work.EKLC6Core.growth_le_atomInfo_mp

namespace Work.EKLC6Core.HcondSigFree

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLC6Core
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

noncomputable section

/-- **The telescoping of the atom information along the `a`-orbit, single-parameter form.**

This is `Work.EKLC6Core.atomInfo_chain` with the hypothesis `IsAErgodic μ` — used there only
through `IsAInvariant μ`, i.e. through `MeasurePreserving (aDiag t ·) μ μ` for the single diagonal
element `t` at hand — weakened to that single instance.  The proof is the same telescoping: the
pointwise identity of Pisa 7.34 in the single-parameter form
(`Work.EKLC6Core.atomInfo_ae_eq_aux_mp`) summed along the orbit gives a telescoping of
`ψ y = log (ν y (shape A U y))`, and the iterate covariance converts the iterated shape mass
back into the shape mass at `x`. -/
theorem atomInfo_chain_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
          Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t
            ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[i] x))
        = Real.log ((ν x (Work.EKLContract.shape
              (MeasurableSpace.comap ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) A)
              (Work.EKLC6Core.Uminus t) x)).toReal)
          - Real.log ((ν x (Work.EKLContract.shape A (Work.EKLC6Core.Uminus t) x)).toReal) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  -- the conull set on which all iterates are good
  have hGae : ∀ᵐ x ∂μ, ∀ j : ℕ, aIter t j x ∈ X' ∩ X'' ∩ Z := by
    show ∀ᵐ x ∂μ, ∀ j : ℕ, (fun y : X3 => aDiag t • y)^[j] x ∈ X' ∩ X'' ∩ Z
    rw [ae_all_iff]
    intro j
    have hj : MeasurePreserving ((fun y : X3 => aDiag t • y)^[j]) μ μ := hmp.iterate j
    have h1 : ∀ᵐ x ∂μ, (fun y : X3 => aDiag t • y)^[j] x ∈ X' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hL.conull)
    have h2 : ∀ᵐ x ∂μ, (fun y : X3 => aDiag t • y)^[j] x ∈ X'' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hX'')
    have h3 : ∀ᵐ x ∂μ, (fun y : X3 => aDiag t • y)^[j] x ∈ Z :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hZ)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    exact ⟨⟨hx1, hx2⟩, hx3⟩
  -- the pointwise identity of Pisa 7.34, along the orbit
  have hAtomAe : ∀ᵐ x ∂μ, ∀ k : ℕ,
      atomInfo A (Uminus t) ν t (aIter t k x)
        = Real.log ((ν (aIter t (k+1) x) (shape A (Uminus t) (aIter t (k+1) x))).toReal)
          - Real.log ((ν (aIter t k x) (shape A (Uminus t) (aIter t k x))).toReal)
          + growthFun (Uminus t) ν t (aIter t (k+1) x) := by
    have hbase := atomInfo_ae_eq_aux_mp (t := t) hL hU hcov hX'' hmp hplq hZ
    rw [ae_all_iff]
    intro k
    have hk := (hmp.iterate k).quasiMeasurePreserving.ae hbase
    filter_upwards [hk] with x hx
    rw [show ((fun y : X3 => aDiag t • y)^[k]) x = aIter t k x from rfl] at hx
    rw [← aIter_succ t k x] at hx
    exact hx
  -- the iterate identity
  have hIterAe : ∀ᵐ x ∂μ, ∀ n : ℕ,
      Real.log ((ν x (shape (Aiter t A n) (Uminus t) x)).toReal)
        = Real.log ((ν (aIter t n x) (shape A (Uminus t) (aIter t n x))).toReal)
          + ∑ i ∈ Finset.range n, growthFun (Uminus t) ν t (aIter t (i+1) x) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hGae] with x hx
    exact iterate_log_pointwise t hL hU hcov hplq hx n
  filter_upwards [hGae, hAtomAe, hIterAe] with x hxG hAtom hIter
  intro n
  change (∑ i ∈ Finset.range n, atomInfo A (Uminus t) ν t (aIter t i x))
      = Real.log ((ν x (shape (Aiter t A n) (Uminus t) x)).toReal)
        - Real.log ((ν x (shape A (Uminus t) x)).toReal)
  -- telescoping of the pointwise identities
  have hsplit : (∑ i ∈ Finset.range n, atomInfo A (Uminus t) ν t (aIter t i x))
      = (∑ i ∈ Finset.range n,
          (Real.log ((ν (aIter t (i+1) x) (shape A (Uminus t) (aIter t (i+1) x))).toReal)
            - Real.log ((ν (aIter t i x) (shape A (Uminus t) (aIter t i x))).toReal)))
        + ∑ i ∈ Finset.range n, growthFun (Uminus t) ν t (aIter t (i+1) x) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hAtom i])
  have htel := Finset.sum_range_sub
    (fun i : ℕ => Real.log ((ν (aIter t i x) (shape A (Uminus t) (aIter t i x))).toReal)) n
  simp only [aIter_zero] at htel
  rw [hsplit, htel]
  rw [hIter n]
  ring

end

end Work.EKLC6Core.HcondSigFree
