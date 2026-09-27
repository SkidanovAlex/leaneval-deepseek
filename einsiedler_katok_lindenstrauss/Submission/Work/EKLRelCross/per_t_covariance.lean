import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.covariant_shape
import Submission.Work.EKLRelCross.acexp_flower
import Submission.Work.EKLRelCross.flower_family
import Submission.Work.EKLRelCross.ae_covPt_of_flower
import Submission.Work.EKLComp.prove_X3

/-!
# `Work.EKLRelCross.per_t_covariance`

For a fixed parameter `t`, the `A`-covariance of a system of leafwise measures (EKL (4),
Pisa 7.16), in the "pointwise" form: at `μ`-a.e. point `x` whose `U`-orbit is free (both at `x`
and at `aDiag t • x`) and which lies with its translate in the domain `X'` of the leafwise
system, the leafwise measures `ν (aDiag t • x)` and `(ν x).map (g ↦ aDiag t * g * (aDiag t)⁻¹)`
are proportional with a nonzero finite constant.

The proof is the flower argument of `Work.EKLRelCross.ae_covPt_of_flower`: the countable family
of plaque algebras supplied by `Work.EKLRelCross.flower_family` (built on `Work.EKLComp.prove_X3`
and the `A`-contraction provided by `IsHoro`) covers a.e. point at every scale `R`, the local
Pisa 7.17 statement `Work.EKLRelCross.local_covPt_shape` gives proportionality on the growing
shapes, and comparison of the constants on a fixed set of positive finite `ν x`-mass (`V 3 ∩ U`)
identifies them; continuity from below extends the identity from `⋃_R V R ∩ U = U` to all of `U`.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

theorem per_t_covariance {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hA : Work.EKLContract.IsAInvariant μ)
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) (t : Fin 3 → ℝ) :
    ∀ᵐ x ∂μ, (x ∈ X' ∧ Work.EKLContract.aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
      (∀ u ∈ U, u • (Work.EKLContract.aDiag t • x) = Work.EKLContract.aDiag t • x → u = 1)) →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (Work.EKLContract.aDiag t • x) = c • (ν x).map (fun g : Work.EKLContract.SL3 => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) := by
  -- the contraction direction of `IsHoro` and the `A`-invariance of `μ`
  obtain ⟨t0, hcontr⟩ := hU.2.2
  have ht0 : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ := hA t0
  have ht : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ := hA t
  -- Pisa Cor. 6.15: the flower families at every scale
  have hfam : ∀ R : ℝ, 0 < R → ∃ (ι : Type) (_ : Countable ι) (Z : ι → Set Work.EKLContract.X3)
      (mm : ι → MeasurableSpace Work.EKLContract.X3) (G : ι → Set Work.EKLContract.X3),
      (∀ i, Work.EKLContract.IsPlaqueAlgebra U (Z i) (mm i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧
      (∀ i, ∀ x ∈ G i, Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)
        ⊆ Work.EKLContract.shape (mm i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 :=
    fun R hR => flower_family Work.EKLComp.prove_X3 μ U hU t0 ht0 hcontr R hR
  have hcov := ae_covPt_of_flower (U := U) (ν := ν) (X' := X') hU hL hfree hfam t ht
  filter_upwards [hcov] with x hx _
  exact hx

end

end Work.EKLRelCross
