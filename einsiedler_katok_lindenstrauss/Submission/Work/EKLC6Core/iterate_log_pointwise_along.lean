import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.atomInfo_chain
import Submission.Work.EKLC6Core.covariant_iterate_along
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLC6Core.shape_mass_pos

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `Work.EKLC6Core.iterate_log_pointwise` (Submission/Work/EKLC6Core/atomInfo_chain.lean, ~line 135) with the full `A`-covariance `ACovariant ν X''` replaced by the covariance along the integer multiples of the single direction `t` (`ACovariantAlong ν t X''`). Along the orbit of a point `x` all of whose iterates lie in `X' ∩ X'' ∩ Z`, `log ν x (shape (Aiter t A n) U x) = log ν (aIter t n x) (shape A U (aIter t n x)) + ∑_{i<n} growthFun U ν t (aIter t (i+1) x)`. The proof is line-for-line that of `Work.EKLC6Core.iterate_log_pointwise`: its only use of the covariance hypothesis is the iterated one-step covariance `Work.EKLC6Core.covariant_iterate'`, read at the single parameter `-t` at each step; replacing that call by the existing `Work.EKLC6Core.covariant_iterate_along` gives this statement. -/
theorem iterate_log_pointwise_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'')
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    {x : Work.EKLContract.X3}
    (hxG : ∀ j : ℕ, Work.EKLC6Core.aIter t j x ∈ X' ∩ X'' ∩ Z) :
    ∀ n : ℕ,
      Real.log ((ν x (Work.EKLContract.shape (Work.EKLC6Core.Aiter t A n) U x)).toReal)
        = Real.log ((ν (Work.EKLC6Core.aIter t n x)
              (Work.EKLContract.shape A U (Work.EKLC6Core.aIter t n x))).toReal)
          + ∑ i ∈ Finset.range n,
              Work.EKLC6Core.growthFun U ν t (Work.EKLC6Core.aIter t (i+1) x) := by
  intro n
  set S : Set SL3 := shape A U (aIter t n x) with hS
  have hSZ : aIter t n x ∈ Z := (hxG n).2
  have hSmeas : MeasurableSet S := by rw [hS]; exact measurableSet_shape_of_mem hU hplq hSZ
  -- the iterated covariance, along the integer multiples of the single direction `t`
  have hit : ν x (conjBy (-((n : ℝ) • t)) S) *
      ∏ j ∈ Finset.range n, ν (aIter t (j + 1) x) (conjBox U t) = ν (aIter t n x) S :=
    covariant_iterate_along t hL hU hcov n x (fun j _ => ⟨(hxG j).1.1, (hxG j).1.2⟩) hSmeas
  have hmain : ν x (shape (Aiter t A n) U x) *
      ∏ j ∈ Finset.range n, ν (aIter t (j + 1) x) (conjBox U t) = ν (aIter t n x) S := by
    rw [shape_Aiter hU t A n x]; exact hit
  -- positivity of the factors
  have hbox : ∀ j : ℕ, 0 < ν (aIter t (j + 1) x) (conjBox U t) ∧
      ν (aIter t (j + 1) x) (conjBox U t) < ⊤ :=
    fun j => conjBox_mass_pos hL hU t (hxG (j + 1)).1.1
  have hCpos : 0 < ν (aIter t n x) S ∧ ν (aIter t n x) S < ⊤ := by
    rw [hS]; exact shape_mass_pos hL hplq (hxG n).1.1 hSZ
  -- take real values
  set a : ℝ := (ν x (shape (Aiter t A n) U x)).toReal with ha
  set P : ℝ := ∏ j ∈ Finset.range n, (ν (aIter t (j + 1) x) (conjBox U t)).toReal with hP
  set c : ℝ := (ν (aIter t n x) S).toReal with hc
  have haPc : a * P = c := by
    have h := congrArg ENNReal.toReal hmain
    simp only [ENNReal.toReal_mul, ENNReal.toReal_prod] at h
    rw [ha, hP, hc]; exact h
  have hPpos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun j _ => ENNReal.toReal_pos (hbox j).1.ne' (hbox j).2.ne)
  have hcpos : 0 < c := by
    rw [hc]; exact ENNReal.toReal_pos hCpos.1.ne' hCpos.2.ne
  have hapos : 0 < a := by nlinarith [haPc, hPpos, hcpos]
  -- logarithms
  have hlog : Real.log c = Real.log a +
      ∑ j ∈ Finset.range n, Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal) := by
    calc Real.log c = Real.log (a * P) := by rw [haPc]
      _ = Real.log a + Real.log P := Real.log_mul hapos.ne' hPpos.ne'
      _ = Real.log a + ∑ j ∈ Finset.range n,
            Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal) := by
          rw [hP, Real.log_prod (fun j _ =>
            (ENNReal.toReal_pos (hbox j).1.ne' (hbox j).2.ne).ne')]
  have hgf : ∀ j : ℕ, Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal) =
      - growthFun U ν t (aIter t (j + 1) x) := by
    intro j; simp only [growthFun]; ring
  have hsum : ∑ j ∈ Finset.range n, Real.log ((ν (aIter t (j + 1) x) (conjBox U t)).toReal)
      = - ∑ j ∈ Finset.range n, growthFun U ν t (aIter t (j + 1) x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => hgf j)
  rw [hsum] at hlog
  have hgoal : Real.log a = Real.log c +
      ∑ j ∈ Finset.range n, growthFun U ν t (aIter t (j + 1) x) := by
    rw [hlog]; ring
  exact hgoal

end Work.EKLC6Core
