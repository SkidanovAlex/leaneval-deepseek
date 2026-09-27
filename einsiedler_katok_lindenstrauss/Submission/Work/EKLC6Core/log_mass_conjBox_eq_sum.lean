import Mathlib
import Submission.Work.EKLC6Core.UBoxDef
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_measurable

/-!
# `EKLC6Core.log_mass_conjBox_eq_sum`

Taking logarithms of the telescoping product identity `Work.EKLC6Core.covariant_mul` (Pisa
7.16 + 7.18 in the normalisation `ν x (B₁^U) = 1` of the frozen contract): the logarithm of the
mass of the *big* box `conjBox (Uminus t) (-n t)` at `x` is the Birkhoff sum of the pointwise
information `growthFun (Uminus t) ν t` along the `aDiag t`-orbit of `x`:

`log ν x (conjBox (Uminus t) (-n t)) = ∑_{j<n} growthFun (Uminus t) ν t (aDiag ((j+1) t) · x)`.

This is the statement that the equilibrium/entropy contribution `D_μ(a,U)(x)` of Pisa 7.6 is an
honest Birkhoff average (Pisa 7.18), in the exact indexing of the orbit that `covariant_mul`
produces.

The only `ENNReal`-bookkeeping that is needed is that a finite product identity `M * ∏ c j = 1`
in `ℝ≥0∞` may be pushed through `toReal` factor by factor (this is unconditional, because
`toReal ⊤ = 0`), after which the product of the `toReal`s is nonzero and hence each factor is
strictly positive -- so that `Real.log_prod` applies.  In particular no probability/finiteness
hypothesis on `μ` is required.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Logarithms of a finite `ENNReal` product identity -/

/-- If `M * ∏_{j∈s} c j = 1` in `ℝ≥0∞`, then
`log M.toReal = -∑_{j∈s} log (c j).toReal`.

Indeed `toReal` is multiplicative for products (unconditionally, since `toReal ⊤ = 0`), so
`M.toReal * ∏ (c j).toReal = 1`; the product is then nonzero, hence each factor is nonzero, and
`Real.log_prod` together with `Real.log_inv` gives the claim. -/
theorem log_toReal_of_mul_finset_prod_eq_one {ι : Type*} (s : Finset ι) (M : ℝ≥0∞)
    (c : ι → ℝ≥0∞) (h : M * ∏ j ∈ s, c j = 1) :
    Real.log M.toReal = -∑ j ∈ s, Real.log (c j).toReal := by
  have htoReal : M.toReal * (∏ j ∈ s, (c j).toReal) = 1 := by
    have hh := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_one] using hh
  have hQne : (∏ j ∈ s, (c j).toReal) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at htoReal
    exact one_ne_zero htoReal.symm
  have hM : M.toReal = (∏ j ∈ s, (c j).toReal)⁻¹ := eq_inv_of_mul_eq_one_left htoReal
  have hfac : ∀ j ∈ s, (c j).toReal ≠ 0 := Finset.prod_ne_zero_iff.mp hQne
  rw [hM, Real.log_inv, Real.log_prod hfac]

/-! ## The main identity -/

theorem log_mass_conjBox_eq_sum {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (n : ℕ) (x : Work.EKLContract.X3)
    (hx : ∀ j : ℕ, j ≤ n + 2 →
      Work.EKLContract.aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'') :
    Real.log ((ν x (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) (-(((n : ℝ)) • t)))).toReal)
      = ∑ j ∈ Finset.range n,
          Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t
            (Work.EKLContract.aDiag ((((j : ℝ) + 1)) • t) • x) := by
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  -- the telescoping product identity of Pisa 7.16 + 7.18
  have hmul := covariant_mul (ν := ν) (X' := X') (X'' := X'') hL hcov
    (fun w => conjBox_measurable hU w) t n x hx
  rw [log_toReal_of_mul_finset_prod_eq_one (Finset.range n)
    (ν x (conjBox (Uminus t) (-(((n : ℝ)) • t))))
    (fun j => ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox (Uminus t) t)) hmul]
  simp only [growthFun, Finset.sum_neg_distrib]

end Work.EKLC6Core

end
