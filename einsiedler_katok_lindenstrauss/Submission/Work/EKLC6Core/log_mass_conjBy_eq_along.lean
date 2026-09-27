import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.covariant_iterate_along
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLC6Core.uminus_isHoro

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal

open Work.EKLContract

/-- `Work.EKLC6Core.log_mass_conjBy_eq` (Submission/Work/EKLC6Core/HcondSig_le_growth_plain.lean, ~line 135) with the full `A`-covariance `ACovariant ν X''` replaced by the covariance along the integer multiples of the single direction `t` (`ACovariantAlong ν t X''`). The mass of the box `conjBy (-(n • t)) S` at `x` is the mass of `S` at `aⁿx` divided by the product of the contracted-box masses along the orbit, hence its logarithm is `log ν (aⁿx) S + ∑_{i<n} growthFun (Uminus t) ν t (a^{i+1} x)`. The proof is line-for-line that of `Work.EKLC6Core.log_mass_conjBy_eq`: its only use of the covariance hypothesis is the call to `Work.EKLC6Core.covariant_iterate`, read at the single parameter `-t` at each step; replacing that call by the existing `Work.EKLC6Core.covariant_iterate_along` (identical statement with `ACovariantAlong ν t X''`) gives this statement. -/
theorem log_mass_conjBy_eq_along (t : Fin 3 → ℝ) {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') {n : ℕ} {x : Work.EKLContract.X3}
    (hxG : ∀ j : ℕ, j ≤ n + 1 →
      ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j]) x ∈ X' ∩ X'')
    {S : Set Work.EKLContract.SL3} (hS : MeasurableSet S)
    (hfin : 0 < ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) S ∧
      ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) S < ⊤) :
    Real.log ((ν x (Work.EKLC6Core.conjBy (-((n : ℝ) • t)) S)).toReal)
      = Real.log ((ν (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) S).toReal)
        + ∑ i ∈ Finset.range n,
            Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t
              (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[(i+1)]) x) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hit := covariant_iterate_along t hL hU hcov n x hxG hS
  have hbox : ∀ j ∈ Finset.range n,
      0 < ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x) (conjBox (Uminus t) t) ∧
      ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x) (conjBox (Uminus t) t) < ⊤ := by
    intro j hj
    simp only [Finset.mem_range] at hj
    exact conjBox_mass_pos hL hU t (hxG (j+1) (by omega)).1
  set P : ℝ≥0∞ := ∏ j ∈ Finset.range n,
      ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x) (conjBox (Uminus t) t) with hP
  have hPpos : 0 < P := by
    rw [hP, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro j hj
    exact (hbox j hj).1.ne'
  have hPtop : P < ⊤ := by
    rw [hP]
    exact ENNReal.prod_lt_top (fun j hj => (hbox j hj).2)
  have hsplit : ν x (conjBy (-((n : ℝ) • t)) S)
      = ν (((fun y : X3 => aDiag t • y)^[n]) x) S / P := by
    rw [ENNReal.eq_div_iff hPpos.ne' hPtop.ne, mul_comm]
    exact hit
  have hlogdiv : Real.log ((ν x (conjBy (-((n : ℝ) • t)) S)).toReal)
      = Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) S).toReal) - Real.log P.toReal := by
    rw [hsplit, ENNReal.toReal_div,
      Real.log_div (ENNReal.toReal_pos hfin.1.ne' hfin.2.ne).ne'
        (ENNReal.toReal_pos hPpos.ne' hPtop.ne).ne']
  have hPlog : Real.log P.toReal = ∑ j ∈ Finset.range n,
      Real.log ((ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x)
        (conjBox (Uminus t) t)).toReal) := by
    rw [hP, ENNReal.toReal_prod, Real.log_prod]
    intro j hj
    exact (ENNReal.toReal_pos (hbox j hj).1.ne' (hbox j hj).2.ne).ne'
  rw [hlogdiv, hPlog]
  have hgf : ∀ j ∈ Finset.range n,
      Real.log ((ν (((fun y : X3 => aDiag t • y)^[(j+1)]) x)
          (conjBox (Uminus t) t)).toReal)
        = - growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(j+1)]) x) := by
    intro j _
    simp only [growthFun]
    ring
  rw [Finset.sum_congr rfl hgf, Finset.sum_neg_distrib]
  ring

end Work.EKLC6Core
