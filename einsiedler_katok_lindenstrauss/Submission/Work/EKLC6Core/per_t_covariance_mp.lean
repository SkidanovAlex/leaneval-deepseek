import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLRelCross.ae_covPt_of_flower
import Submission.Work.EKLRelCross.flower_family
import Submission.Work.EKLComp.prove_X3

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-- **Pisa 7.16/7.17 (single parameter), measure-preserving form.**  For a probability measure
`μ` preserved by the single diagonal element `α^t = aDiag t`, a subgroup `U` which `α^t`
contracts to the identity, and a system of leafwise measures `ν` for `U`, the leafwise measures
at `aDiag t • x` and at `x` are proportional (by a nonzero finite constant) off a `μ`-null set,
as soon as both points lie in the domain `X'` of the system.

The two mathematical inputs are
* `Work.EKLRelCross.ae_free_orbit` — a.e. freeness of the `U`-orbits (Pisa 7.12), which is a
  consequence of the contraction hypothesis `hcontr` and of `P_X3` alone;
* `Work.EKLRelCross.ae_covPt_of_flower` — the flower argument of Pisa 7.17, applied to the
  countable flower families of `Work.EKLRelCross.flower_family` at all scales. -/
theorem per_t_covariance_mp {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    ∃ N : Set Work.EKLContract.X3, μ N = 0 ∧ ∀ x : Work.EKLContract.X3, x ∉ N → x ∈ X' →
      Work.EKLContract.aDiag t • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (Work.EKLContract.aDiag t • x) =
          c • (ν x).map (fun g : Work.EKLContract.SL3 =>
            Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) := by
  classical
  -- `P_X3`: the structure theory of the space of lattices (proved in this workspace).
  have h2 : Work.EKLContract.P_X3 := Work.EKLComp.prove_X3
  -- a.e. freeness of the `U`-orbits (Pisa 7.12)
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    Work.EKLRelCross.ae_free_orbit h2 μ U hU t hmp hcontr
  -- the flower families of plaque algebras at every scale (Pisa Cor. 6.15)
  have hfam : ∀ R : ℝ, 0 < R → ∃ (ι : Type) (_ : Countable ι) (Z : ι → Set X3)
      (mm : ι → MeasurableSpace X3) (G : ι → Set X3),
      (∀ i, IsPlaqueAlgebra U (Z i) (mm i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧
      (∀ i, ∀ x ∈ G i, V R ∩ (U : Set SL3) ⊆ shape (mm i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 :=
    fun R hR => Work.EKLRelCross.flower_family h2 μ U hU t hmp hcontr R hR
  -- the pointwise covariance on a `μ`-conull set (Pisa 7.17)
  have hcov : ∀ᵐ x ∂μ, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag t • x) =
        c • (ν x).map (fun g : Work.EKLContract.SL3 =>
          aDiag t * g * (aDiag t)⁻¹) :=
    Work.EKLRelCross.ae_covPt_of_flower (U := U) hU hL hfree hfam t hmp
  have hcovNull : μ {x : X3 | ¬ (∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag t • x) =
        c • (ν x).map (fun g : Work.EKLContract.SL3 =>
          aDiag t * g * (aDiag t)⁻¹))} = 0 :=
    MeasureTheory.ae_iff.mp hcov
  have hfreeNull : μ {x : X3 | ¬ (∀ u ∈ U, u • x = x → u = 1)} = 0 :=
    MeasureTheory.ae_iff.mp hfree
  -- the exceptional set: points where the covariance, or the freeness, fails
  refine ⟨{x : X3 | ¬ (∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag t • x) =
        c • (ν x).map (fun g : Work.EKLContract.SL3 =>
          aDiag t * g * (aDiag t)⁻¹))} ∪ {x : X3 | ¬ (∀ u ∈ U, u • x = x → u = 1)},
    measure_union_null hcovNull hfreeNull, ?_⟩
  intro x hx _ _
  rw [Set.mem_union, not_or] at hx
  exact of_not_not hx.1

end Work.EKLC6Core
