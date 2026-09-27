import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.conjBox_nsmul_mass`

The mass of the box `conjBox U (n t)` at `x` is the product of the masses of the *one-step*
box `conjBox U t` along the negative `aDiag t`-orbit of `x`:

`ν x (conjBox U (n t)) = ∏_{j<n} ν (aDiag (j t))⁻¹ x (conjBox U t)`.

This is the multiplicative (division-free) form of Pisa 7.16 + 7.18 in the normalisation of the
frozen contract: iterating the one-step covariance `Work.EKLC6Core.covariant_step` along the
orbit, the boxes `conjBox U (k t)` telescope, and the last term `conjBox U 0 = Box1 U` has mass
`1` by the normalisation field of `IsLeafwise`.  Taking logarithms turns this into the statement
that `n ↦ -log ν x (conjBox U (n t))` is a Birkhoff sum of `growthFun U ν t` along the orbit,
i.e. that the limit defining the entropy contribution `D_μ(a,U)` of Pisa 7.6 is a Birkhoff
average.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem conjBox_nsmul_mass {μ : MeasureTheory.Measure Work.EKLContract.X3} {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hcov : Work.EKLC6Core.ACovariant ν X'')
    (hBox : ∀ w : Fin 3 → ℝ, MeasurableSet (Work.EKLC6Core.conjBox U w)) (t : Fin 3 → ℝ) :
    ∀ (n : ℕ) (x : Work.EKLContract.X3),
      (∀ j : ℕ, j ≤ n → Work.EKLContract.aDiag (-(((j : ℝ)) • t)) • x ∈ X' ∩ X'') →
      ν x (Work.EKLC6Core.conjBox U (((n : ℝ)) • t)) =
        ∏ j ∈ Finset.range n,
          ν (Work.EKLContract.aDiag (-(((j : ℝ)) • t)) • x) (Work.EKLC6Core.conjBox U t) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have hx' : x ∈ X' := by
      have h := (hx 0 le_rfl).1
      simpa [aDiag_zero] using h
    simpa [aDiag_zero] using hL.normalised x hx'
  | succ n ih =>
    intro x hx
    -- the next point down the negative orbit
    set y : X3 := aDiag (-t) • x with hy
    have hx0 : x ∈ X' ∩ X'' := by
      have h := hx 0 (by omega)
      simpa [aDiag_zero] using h
    have hymem : y ∈ X' ∩ X'' := by
      have h := hx 1 (by omega)
      simpa [hy] using h
    -- stepping down by `t` from `j t` lands at `(j+1) t`
    have hyeq : ∀ j : ℕ, aDiag (-(((j:ℝ)) • t)) • y =
        aDiag (-((((j+1:ℕ)):ℝ) • t)) • x := by
      intro j
      have hfun : -(((j:ℝ)) • t) + (-t) = -((((j+1:ℕ)):ℝ) • t) := by
        have hc : ((((j + 1 : ℕ)) : ℝ) • t) = ((j:ℝ) • t + t) := by
          rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        rw [hc, neg_add]
      rw [hy, aDiag_smul_mul, hfun]
    -- the one-step covariance at the base point `x`
    have hstep := covariant_step hL hcov (by simpa using hBox 0) t hx0 hymem
      (C := conjBox U (((n:ℝ)) • t)) (hBox _)
    have hconj : conjBy t (conjBox U (((n:ℝ)) • t)) =
        conjBox U ((((n+1:ℕ)):ℝ) • t) := by
      rw [conjBy_conjBox]
      congr 1
      have hc : ((((n + 1 : ℕ)) : ℝ) • t) = ((n:ℝ) • t + t) := by
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      rw [hc, add_comm]
    rw [hconj] at hstep
    rw [← hy] at hstep
    rw [← hstep]
    -- the induction hypothesis at the shifted point `y`
    have hycond : ∀ j : ℕ, j ≤ n → aDiag (-(((j:ℝ)) • t)) • y ∈ X' ∩ X'' := by
      intro j hj
      rw [hyeq j]
      exact hx (j+1) (by omega)
    have hih := ih y hycond
    rw [hih]
    rw [Finset.prod_range_succ']
    have hprod : (∏ j ∈ Finset.range n,
          ν (aDiag (-(((j:ℝ)) • t)) • y) (conjBox U t))
        = ∏ j ∈ Finset.range n,
          ν (aDiag (-((((j+1:ℕ)):ℝ) • t)) • x) (conjBox U t) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hyeq j]
    rw [hprod]
    have hf0 : ν (aDiag (-((((0:ℕ)):ℝ) • t)) • x) (conjBox U t) = ν x (conjBox U t) := by
      simp [aDiag_zero]
    rw [hf0]

end Work.EKLC6Core
