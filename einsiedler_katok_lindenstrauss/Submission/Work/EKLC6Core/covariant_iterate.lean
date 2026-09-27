import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.covariant_iterate` — the iterated covariance identity for an arbitrary test set

`Covariant.lean` proves the one-step covariance of a leaf-wise system (`covariant_step`, Pisa
7.16/7.18 in normalised form) `ν (a⁻¹.y) C * ν y (conjBox U t) = ν y (conjBy t C)` together with
its specialisation to the box `C = conjBox U (-n t)` (`covariant_mul`).  Here we iterate the
one-step identity for an **arbitrary** measurable test set `S`:

  `ν x (conjBy (-n t) S) * ∏_{j<n} ν (a^{j+1}.x) (conjBox U t) = ν (a^n.x) S`

for every `x` whose first `n+1` iterates lie in `X' ∩ X''`.  The proof is the same telescoping as
in `covariant_mul`, but with the constant of `ACovariant` cancelled by the normalisation at each
step (`covariant_step`), which is exactly what allows an arbitrary right-hand side `S`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-! ## Auxiliary API -/

/-- The iterate of the diagonal flow on `X₃` is the diagonal flow of the accumulated exponent. -/
theorem iterate_aDiag (t : Fin 3 → ℝ) (n : ℕ) (x : X3) :
    (fun y : X3 => aDiag t • y)^[n] x = aDiag ((n : ℝ) • t) • x := by
  induction n with
  | zero => simp [aDiag_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 : (((n : ℝ) + 1) • t) = t + (n : ℝ) • t := by rw [succ_smul, add_comm]
    rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by push_cast; ring, h1, aDiag_smul_mul]

/-- The conjugate `conjBy t S` of a Borel set is Borel (conjugation is a homeomorphism). -/
theorem measurableSet_conjBy (t : Fin 3 → ℝ) {S : Set SL3} (hS : MeasurableSet S) :
    MeasurableSet (conjBy t S) := by
  rw [← preimage_conj_neg t S]
  exact hS.preimage (measurable_conj (-t))

/-! ## The iterated covariance, in additive (`aDiag`) coordinates -/

/-- **Iterated one-step covariance.**  For every `n` and every `x` whose first `n+1` successors
along `a = aDiag t` lie in `X' ∩ X''`,

  `ν x (conjBy (-n t) S) * ∏_{j<n} ν (a^{j+1}.x) (conjBox U t) = ν (a^n.x) S`. -/
theorem covariant_iterate_aDiag {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} (hL : IsLeafwise μ U ν X') (hU : IsHoro U) (hcov : ACovariant ν X'')
    (t : Fin 3 → ℝ) :
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
    have hstep := covariant_step hL hcov (measurableSet_box1 hU) t hx1
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

theorem covariant_iterate {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'') :
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
  have hmain := covariant_iterate_aDiag hL hU hcov t n x hx' hS
  simpa only [iterate_aDiag, Nat.cast_add, Nat.cast_one] using hmain

end

end Work.EKLC6Core
