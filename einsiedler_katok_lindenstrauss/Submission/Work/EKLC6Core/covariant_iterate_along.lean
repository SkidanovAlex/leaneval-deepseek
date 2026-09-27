import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.covariant_iterate
import Submission.Work.EKLC6Core.conjBox_smul_mass_mul_along

/-!
# `EKLC6Core.covariant_iterate_along` — the iterated covariance identity along `ℤ·t`

`covariant_iterate` iterates the one-step covariance `covariant_step` for an arbitrary measurable
test set `S`:

  `ν x (conjBy (-n t) S) * ∏_{j<n} ν (a^{j+1}.x) (conjBox U t) = ν (a^n.x) S`

for every `x` whose first `n+1` iterates lie in `X' ∩ X''`, under the full `A`-covariance
`ACovariant ν X''`.

Here the covariance hypothesis is weakened to the covariance along the integer multiples of a
*single* direction `t` (`ACovariantAlong ν t X''`, EKL (4) restricted to `ℤ·t`), which is the form
in which the covariance enters the entropy chain of `EKLC6Core` (`acovariantAlong_of_leafwise`).

The point (`conjBox_smul_mass_mul_along`) is that the one-step covariance uses the covariance
hypothesis at a *single* parameter only — namely at the parameter of the shift, here `-t = (-1)·t`
— so the whole telescoping of `covariant_iterate` goes through verbatim, reading `hcov` at that
one integer multiple at each step.  Only the two integer multiples `-t` and `t` are ever used, so
this is genuinely a weakening.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-- **One step of the iterated covariance, along the direction `t`.**  This is `covariant_step`
with the `A`-covariance `ACovariant ν X''` replaced by the covariance along the integer multiples
of the direction `t` (`ACovariantAlong ν t X''`): the covariance is read at the single parameter
`-t = (-1) · t`.

  `ν (aDiag (-t) · y) C * ν y (conjBox U t) = ν y (conjBy t C)`. -/
theorem covariant_step_along_neg {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} (t : Fin 3 → ℝ) (hL : IsLeafwise μ U ν X')
    (hcov : ACovariantAlong ν t X'') (hBox1 : MeasurableSet (Box1 U)) {y : X3}
    (hy : y ∈ X' ∩ X'') (hy' : aDiag (-t) • y ∈ X' ∩ X'') {C : Set SL3}
    (hC : MeasurableSet C) :
    ν (aDiag (-t) • y) C * ν y (conjBox U t) = ν y (conjBy t C) := by
  have hw : (((-1 : ℤ) : ℝ) • t : Fin 3 → ℝ) = -t := by
    funext i
    simp
  have hy'' : aDiag (((-1 : ℤ) : ℝ) • t) • y ∈ X' ∩ X'' := by
    rw [hw]
    exact hy'
  have hstep := covariant_step_along hL hcov hBox1 (-1) hy hy'' (C := C) hC
  simpa [hw] using hstep

/-! ## The iterated covariance along `ℤ · t`, in additive (`aDiag`) coordinates -/

/-- **Iterated one-step covariance along a single direction.**  For every `n` and every `x` whose
first `n+1` successors along `a = aDiag t` lie in `X' ∩ X''`,

  `ν x (conjBy (-n t) S) * ∏_{j<n} ν (a^{j+1}.x) (conjBox U t) = ν (a^n.x) S`,

under the covariance hypothesis along the integer multiples of `t` only. -/
theorem covariant_iterate_aDiag_along {μ : Measure X3} {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' X'' : Set X3} (hL : IsLeafwise μ U ν X') (hU : IsHoro U)
    (t : Fin 3 → ℝ) (hcov : ACovariantAlong ν t X'') :
    ∀ (n : ℕ) (x : X3),
      (∀ j : ℕ, j ≤ n + 1 → aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'') →
      ∀ {S : Set SL3}, MeasurableSet S →
        ν x (conjBy (-((n : ℝ) • t)) S) *
            ∏ j ∈ Finset.range n, ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t)
          = ν (aDiag ((n : ℝ) • t) • x) S := by
  intro n
  induction n with
  | zero =>
    intro x _ S _
    simp [aDiag_zero]
  | succ n ih =>
    intro x hx S hS
    have hsucc : (((n + 1 : ℕ) : ℝ) • t : Fin 3 → ℝ) = ((n : ℝ) + 1) • t := by
      rw [show (((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1) by push_cast; ring]
    rw [hsucc]
    have hx0 : x ∈ X' ∩ X'' := by
      have h := hx 0 (by omega)
      simpa [aDiag_zero] using h
    have hx1 : aDiag t • x ∈ X' ∩ X'' := by
      have h := hx 1 (by omega)
      have hv : (((1 : ℕ) : ℝ) • t : Fin 3 → ℝ) = t := by simp
      rw [hv] at h
      exact h
    have hcancel : aDiag (-t) • (aDiag t • x) = x := by
      rw [aDiag_smul_mul]
      have h0 : -t + t = (0 : Fin 3 → ℝ) := by funext i; simp
      rw [h0, aDiag_zero, one_smul]
    have hstep := covariant_step_along_neg t hL hcov (measurableSet_box1 hU) hx1
      (by rw [hcancel]; exact hx0) (C := conjBy (-(((n : ℝ) + 1) • t)) S)
      (measurableSet_conjBy _ hS)
    rw [hcancel] at hstep
    have hconj : conjBy t (conjBy (-(((n : ℝ) + 1) • t)) S) = conjBy (-((n : ℝ) • t)) S := by
      rw [← conjBy_add, add_neg_succ_smul]
    rw [hconj] at hstep
    have hy : ∀ j : ℕ, j ≤ n + 1 →
        aDiag ((j : ℝ) • t) • (aDiag t • x) ∈ X' ∩ X'' := by
      intro j hj
      have h := hx (j + 1) (by omega)
      have heq : aDiag ((j : ℝ) • t) • (aDiag t • x) = aDiag (((j + 1 : ℕ) : ℝ) • t) • x := by
        rw [aDiag_smul_mul, show (((j + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) by push_cast; ring,
          succ_smul]
      rw [heq]
      exact h
    have hIH := @ih (aDiag t • x) hy S hS
    have hprod_tail : (∏ j ∈ Finset.range (n + 1),
          ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t))
        = (∏ j ∈ Finset.range n,
              ν (aDiag (((j : ℝ) + 1) • t) • (aDiag t • x)) (conjBox U t)) *
            ν (aDiag t • x) (conjBox U t) := by
      rw [Finset.prod_range_succ']
      congr 1
      · refine Finset.prod_congr rfl (fun j _ => ?_)
        have hv : ((((j + 1 : ℕ) : ℝ) + 1) • t : Fin 3 → ℝ) = (((j : ℝ) + 1) • t + t) := by
          rw [show (((j + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) by push_cast; ring]
          rw [show ((((j : ℝ) + 1) + 1) • t) = (((j : ℝ) + 1) • t + t) by
            rw [add_smul, one_smul]]
        rw [hv, aDiag_smul_mul]
      · simp
    have hprod : (∏ j ∈ Finset.range (n + 1),
          ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t))
        = ν (aDiag t • x) (conjBox U t) *
            ∏ j ∈ Finset.range n,
              ν (aDiag (((j : ℝ) + 1) • t) • (aDiag t • x)) (conjBox U t) := by
      rw [hprod_tail]
      exact mul_comm _ _
    have hrhs : ν (aDiag ((n : ℝ) • t) • (aDiag t • x)) S =
        ν (aDiag (((n : ℝ) + 1) • t) • x) S := by
      rw [aDiag_smul_mul, succ_smul n t]
    calc ν x (conjBy (-(((n : ℝ) + 1) • t)) S) *
          ∏ j ∈ Finset.range (n + 1), ν (aDiag (((j : ℝ) + 1) • t) • x) (conjBox U t)
        = ν x (conjBy (-(((n : ℝ) + 1) • t)) S) *
            (ν (aDiag t • x) (conjBox U t) *
              ∏ j ∈ Finset.range n,
                ν (aDiag (((j : ℝ) + 1) • t) • (aDiag t • x)) (conjBox U t)) := by
          rw [hprod]
      _ = (ν x (conjBy (-(((n : ℝ) + 1) • t)) S) * ν (aDiag t • x) (conjBox U t)) *
              ∏ j ∈ Finset.range n,
                ν (aDiag (((j : ℝ) + 1) • t) • (aDiag t • x)) (conjBox U t) := by
          rw [mul_assoc]
      _ = ν (aDiag t • x) (conjBy (-((n : ℝ) • t)) S) *
              ∏ j ∈ Finset.range n,
                ν (aDiag (((j : ℝ) + 1) • t) • (aDiag t • x)) (conjBox U t) := by
          rw [hstep]
      _ = ν (aDiag ((n : ℝ) • t) • (aDiag t • x)) S := hIH
      _ = ν (aDiag (((n : ℝ) + 1) • t) • x) S := by rw [hrhs]

/-! ## The requested statement -/

theorem covariant_iterate_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') :
    ∀ (n : ℕ) (x : Work.EKLContract.X3),
      (∀ j : ℕ, j ≤ n + 1 → (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j] x ∈ X' ∩ X'') →
      ∀ {S : Set Work.EKLContract.SL3}, MeasurableSet S →
        ν x (Work.EKLC6Core.conjBy (-((n : ℝ) • t)) S) *
            ∏ j ∈ Finset.range n,
              ν ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j+1] x)
                (Work.EKLC6Core.conjBox U t)
          = ν ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n] x) S := by
  intro n x hx S hS
  have hx' : ∀ j : ℕ, j ≤ n + 1 → aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'' := by
    intro j hj
    rw [← iterate_aDiag t j x]
    exact hx j hj
  have hmain := covariant_iterate_aDiag_along hL hU t hcov n x hx' hS
  simpa only [iterate_aDiag, Nat.cast_add, Nat.cast_one] using hmain

end

end Work.EKLC6Core
