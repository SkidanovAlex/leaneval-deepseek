import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLC6Core.box_facts

/-!
# `EKLC6Core.conjBox_neg_nsmul_toReal`

Taking logarithms of the telescoping identity `Work.EKLC6Core.covariant_mul` (Pisa 7.16 + 7.18
in the normalisation `ν x (B₁^U) = 1` of the frozen contract): along the `aDiag t`-orbit the
masses of the *big* boxes `conjBox U (-m t)` are the exponentials of the Birkhoff sums of the
pointwise information `growthFun U ν t x = -log ν x (conjBox U t)`:

`ν x (conjBox U (-m t)) = exp (∑_{j=1}^{m} growthFun U ν t (aDiag (j t) • x))`.

This is the statement that the equilibrium/entropy contribution `D_μ(a,U)(x)` of Pisa 7.6 is an
honest Birkhoff average (Pisa 7.18), and it is what lets the martingale convergence argument of
Pisa 7.6 be applied to the leaf-wise measures.

The two elementary inputs are the product identity `covariant_mul` (via `IsLeafwise.normalised`)
and the positivity/finiteness of the contracted box `conjBox_mass_pos` (which makes all the
`toReal`s involved positive, so that `log` and `exp` cancel).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Two elementary re-indexings -/

/-- The exponent vector `((j+1 : ℕ) : ℝ) • t` agrees with `((j : ℝ) + 1) • t`: the two ways of
writing "the next point of the orbit" that appear in `covariant_mul` and in the statement. -/
theorem aDiag_natCast_add_one_smul (t : Fin 3 → ℝ) (j : ℕ) :
    ((((j + 1 : ℕ)) : ℝ) • t : Fin 3 → ℝ) = ((j : ℝ) + 1) • t := by
  congr 1
  push_cast
  ring

/-- Sums over `Icc 1 m` are sums over `range m` of the shifted summand. -/
theorem sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, g k) = ∑ j ∈ Finset.range m, g (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega) g, Finset.sum_range_succ, ih]

/-! ## The main identity -/

theorem conjBox_neg_nsmul_toReal {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hcov : Work.EKLC6Core.ACovariant ν X'')
    (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (m : ℕ) {x : Work.EKLContract.X3}
    (hx : ∀ j : ℕ, j ≤ m + 2 →
      Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'') :
    (ν x (Work.EKLC6Core.conjBox U (-((m : ℝ) • t)))).toReal
      = Real.exp (∑ j ∈ Finset.Icc 1 m,
          Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag ((j : ℝ) • t) • x)) := by
  -- each one-step box along the orbit has positive, finite (hence positive real) mass
  have hpos : ∀ j ∈ Finset.range m,
      0 < ((ν (aDiag (((j : ℝ) + 1) • t) • x)) (conjBox U t)).toReal := by
    intro j hj
    have hjle : j + 1 ≤ m + 2 := by
      have := Finset.mem_range.mp hj
      omega
    have hmem : aDiag (((j : ℝ) + 1) • t) • x ∈ X' := by
      have h := (hx (j + 1) hjle).1
      rwa [aDiag_natCast_add_one_smul t j] at h
    obtain ⟨hp, hlt⟩ := conjBox_mass_pos (μ := μ) (ν := ν) (U := U) hL hU t hmem
    exact ENNReal.toReal_pos (ne_of_gt hp) (ne_of_lt hlt)
  -- the telescoping product identity of Pisa 7.16 + 7.18
  have hmul := covariant_mul (μ := μ) (U := U) (ν := ν) (X' := X') (X'' := X'') hL hcov
    (fun w => conjBox_measurable hU w) t m x hx
  -- hence the mass of the big box is the reciprocal of the product of the one-step masses
  have hval : (ν x (conjBox U (-((m : ℝ) • t)))).toReal
      = ((∏ j ∈ Finset.range m, (ν (aDiag (((j : ℝ) + 1) • t) • x)) (conjBox U t)).toReal)⁻¹ := by
    have h := congrArg ENNReal.toReal hmul
    simp only [ENNReal.toReal_mul, ENNReal.toReal_one] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [hval]
  -- re-index the sum along the orbit and turn the exponential of the sum into the product
  rw [sum_Icc_one_eq_sum_range (fun k => growthFun U ν t (aDiag ((k : ℝ) • t) • x)) m]
  simp only [aDiag_natCast_add_one_smul]
  rw [ENNReal.toReal_prod, Real.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [growthFun, Real.exp_neg, Real.exp_log (hpos j hj)]

end Work.EKLC6Core

end
