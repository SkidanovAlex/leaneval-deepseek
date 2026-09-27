import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.log_mass_conjBox_eq_sum
import Submission.Work.EKLC6Core.conjBox_smul_mass_mul_along

/-!
# `EKLC6Core.log_mass_conjBox_eq_sum_along`

The identity `Work.EKLC6Core.log_mass_conjBox_eq_sum` with the full `A`-covariance
`ACovariant ν X''` replaced by the covariance along the integer multiples of the single direction
`t` (`ACovariantAlong ν t X''`, EKL (4) restricted to `ℤ·t`):

`log ν x (conjBox (Uminus t) (-n t)) = ∑_{j<n} growthFun (Uminus t) ν t (aDiag ((j+1) t) · x)`.

The point is that the telescoping identity `covariant_mul` reads the covariance hypothesis at the
single parameter `-t` (once per step); `ACovariantAlong ν t X''` provides it at `z = -1`.  Hence
the whole argument of `covariant_mul` goes through verbatim, and the logarithmic bookkeeping is
the one already isolated in `log_mass_conjBox_eq_sum`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **One step of the covariance, reading `ACovariantAlong` at `z = -1`.**  This is
`covariant_step` with the `A`-covariance `ACovariant ν X''` replaced by
`ACovariantAlong ν t X''`, instantiated at the (single) parameter `-t`; it is
`covariant_step_along` at `z = -1`. -/
theorem covariant_step_along_neg {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} {t : Fin 3 → ℝ} (hL : IsLeafwise μ U ν X')
    (hcov : ACovariantAlong ν t X'') (hBox1 : MeasurableSet (Box1 U))
    {y : X3} (hy : y ∈ X' ∩ X'') (hy' : aDiag (-t) • y ∈ X' ∩ X'') {C : Set SL3}
    (hC : MeasurableSet C) :
    ν (aDiag (-t) • y) C * ν y (conjBox U t) = ν y (conjBy t C) := by
  have hz : ((-1 : ℤ) : ℝ) • t = -t := by simp
  have hstep := covariant_step_along hL hcov hBox1 (-1) hy (by rw [hz]; exact hy') hC
  rw [hz] at hstep
  simpa using hstep

/-- **Pisa 7.16 + 7.18 (normalised form), along a single direction.**  Along the `a`-orbit of `x`
the boxes telescope, with the `A`-covariance replaced by its restriction to the integer multiples
of `t`:

`ν x (conjBox U (-n t)) * ∏_{j<n} ν (a^{j+1}.x) (conjBox U t) = 1`. -/
theorem covariant_mul_along {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} (t : Fin 3 → ℝ) (hL : IsLeafwise μ U ν X')
    (hcov : ACovariantAlong ν t X'')
    (hBox : ∀ w : Fin 3 → ℝ, MeasurableSet (conjBox U w)) :
    ∀ (n : ℕ) (x : X3),
      (∀ j : ℕ, j ≤ n + 2 → aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'') →
      ν x (conjBox U (-((n : ℝ) • t))) *
        ∏ j ∈ Finset.range n,
          ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t) = 1 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Finset.range_zero, Finset.prod_empty, mul_one, Nat.cast_zero, zero_smul,
      neg_zero]
    have hxX' : x ∈ X' := by
      have h := (hx 0 (by omega)).1
      simpa [aDiag_zero, one_smul] using h
    rw [conjBox_zero, hL.normalised x hxX']
  | succ n ih =>
    intro x hx
    set y : X3 := aDiag t • x with hy_def
    have hy : y ∈ X' ∩ X'' := by
      have h := hx 1 (by omega)
      simpa [hy_def] using h
    have hx' : x ∈ X' ∩ X'' := by
      have h := hx 0 (by omega)
      simpa [aDiag_zero, one_smul] using h
    have hyx : ∀ j : ℕ, j ≤ n + 2 → aDiag ((j : ℝ) • t) • y ∈ X' ∩ X'' := by
      intro j hj
      have h := hx (j + 1) (by omega)
      have heq : aDiag ((j : ℝ) • t) • y = aDiag (((j : ℝ) + 1) • t) • x := by
        rw [hy_def, aDiag_smul_mul, succ_smul]
      rw [heq]
      simpa using h
    have hIH := ih y hyx
    have hyx0 : aDiag (-t) • y = x := by
      rw [hy_def, aDiag_smul_mul]
      have hzero : -t + t = (0 : Fin 3 → ℝ) := by funext i; simp
      rw [hzero, aDiag_zero, one_smul]
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    have hstep := covariant_step_along_neg (μ := μ) hL hcov (by simpa using hBox 0) hy
      (by rw [hyx0]; exact hx')
      (C := conjBox U (-(((n : ℝ) + 1) • t))) (hBox _)
    rw [hyx0] at hstep
    have hstep' : ν x (conjBox U (-(((n : ℝ) + 1) • t))) * ν y (conjBox U t) =
        ν y (conjBox U (-((n : ℝ) • t))) := by
      rw [hstep, conjBy_conjBox]
      rw [add_neg_succ_smul n t]
    have hprod : (∏ j ∈ Finset.range (n + 1),
          ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t)) =
        ν y (conjBox U t) *
          ∏ j ∈ Finset.range n, ν (aDiag (((j : ℝ) + 1) • t) • y) (conjBox U t) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      · rw [hy_def]
        simp only [Nat.cast_zero, zero_add, one_smul]
      · apply Finset.prod_congr rfl
        intro j _
        have hv : ((((j + 1 : ℕ) : ℝ) + 1) • t : Fin 3 → ℝ) = ((j : ℝ) + 1) • t + t := by
          ext i
          simp only [Pi.add_apply, Pi.smul_apply]
          push_cast
          ring
        have heq : aDiag ((((j + 1 : ℕ) : ℝ) + 1) • t) • x =
            aDiag (((j : ℝ) + 1) • t) • y := by
          rw [hy_def, aDiag_smul_mul, hv]
        rw [heq]
    rw [hcast, hprod, ← mul_assoc, hstep', hIH]

/-- The statement requested by the colleague: `log_mass_conjBox_eq_sum` with the full
`A`-covariance replaced by `ACovariantAlong ν t X''`. -/
theorem log_mass_conjBox_eq_sum_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (n : ℕ) (x : Work.EKLContract.X3)
    (hx : ∀ j : ℕ, j ≤ n + 2 →
      Work.EKLContract.aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'') :
    Real.log ((ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) (-(((n : ℝ)) • t)))).toReal)
      = ∑ j ∈ Finset.range n,
          Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t
            (Work.EKLContract.aDiag ((((j : ℝ) + 1)) • t) • x) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hmul := covariant_mul_along (ν := ν) (X' := X') (X'' := X'') t hL hcov
    (fun w => conjBox_measurable hU w) n x hx
  rw [log_toReal_of_mul_finset_prod_eq_one (Finset.range n)
    (ν x (conjBox (Uminus t) (-(((n : ℝ)) • t))))
    (fun j => ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox (Uminus t) t)) hmul]
  simp only [growthFun, Finset.sum_neg_distrib]

end Work.EKLC6Core

end
