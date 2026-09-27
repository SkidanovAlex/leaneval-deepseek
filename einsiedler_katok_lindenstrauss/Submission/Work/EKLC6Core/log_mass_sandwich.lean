import Mathlib
import Submission.Work.EKLC6Core.radius_independence

/-!
# `EKLC6Core.log_mass_sandwich` — the pointwise two-sided estimate for the leafwise boxes

This is the pointwise estimate (extracted from `Work.EKLC6Core.radius_independence`) which is
the heart of the radius independence of the exponential rate of the leafwise boxes
(Pisa 7.18).

Hypotheses: `μ` is a probability, `(μ, ν)` is a leaf-wise system for the horospherical subgroup
`U` on `X'`, `ν` is `A`-covariant on `X''`, the diagonal element `aDiag t` contracts `U`, and
the test set `V r ∩ U` is trapped between two conjugated boxes
`conjBox U (k•t) ⊆ V r ∩ U ⊆ conjBox U (-(k•t))`.

Conclusion: for `x` whose `aDiag t`-orbit (from `x`) stays in `X' ∩ X''`, and for `k ≤ n`,

`exp(-∑_{i=1}^{k} g(a^{n-k+i} x)) ≤ ν (a^{n} x) (V r ∩ U) ≤ exp(∑_{i=1}^{k} g(a^{n+i} x))`,

where `g = growthFun U ν t`.

The proof combines the telescoping product identity `conjBox_neg_nsmul_toReal` (Pisa 7.16 + 7.18)
with the two inclusions of the sandwich, and takes logarithms.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem log_mass_sandwich {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariant ν X'')
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    {r : ℝ} {k : ℕ}
    (hsmall : Work.EKLC6Core.conjBox U ((k : ℝ) • t) ⊆
        Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3))
    (hbig : Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ⊆
        Work.EKLC6Core.conjBox U (-((k : ℝ) • t)))
    {x : Work.EKLContract.X3}
    (horb : ∀ m j : ℕ, Work.EKLContract.aDiag ((j : ℝ) • t) •
        (Work.EKLContract.aDiag ((m : ℝ) • t) • x) ∈ X' ∩ X'')
    {n : ℕ} (hn : k ≤ n) :
    -(∑ i ∈ Finset.Icc 1 k,
        Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag (((n - k + i : ℕ) : ℝ) • t) • x))
      ≤ Real.log ((ν (Work.EKLContract.aDiag ((n : ℝ) • t) • x)
          (Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3))).toReal) ∧
    Real.log ((ν (Work.EKLContract.aDiag ((n : ℝ) • t) • x)
          (Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3))).toReal)
      ≤ ∑ i ∈ Finset.Icc 1 k,
        Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag (((n + i : ℕ) : ℝ) • t) • x) := by
  -- mass of the "big" box at `aDiag (n•t) • x` is the exponential of a Birkhoff sum
  have hFn : (ν (aDiag ((n : ℝ) • t) • x)
        (conjBox U (-((k : ℝ) • t)))).toReal
      = Real.exp (∑ i ∈ Finset.Icc 1 k,
          growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) := by
    have h := conjBox_neg_nsmul_toReal hL hcov hU hcontr (m := k)
        (x := aDiag ((n : ℝ) • t) • x) (fun j _ => horb n j)
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [aDiag_smul_mul, ri_add_smul_nat]
  have hFne : ν (aDiag ((n : ℝ) • t) • x) (conjBox U (-((k : ℝ) • t))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hFn
    exact (Real.exp_ne_zero _) hFn.symm
  have hmLtop : ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFne (measure_mono hbig)
  have hMle : (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal
      ≤ Real.exp (∑ i ∈ Finset.Icc 1 k,
          growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) := by
    calc (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal
        ≤ (ν (aDiag ((n : ℝ) • t) • x) (conjBox U (-((k : ℝ) • t)))).toReal :=
          ENNReal.toReal_mono hFne (measure_mono hbig)
      _ = Real.exp (∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n + i : ℕ) : ℝ) • t) • x)) := hFn
  -- the orbit points of `x` (at exponent `m • t`) lie in `X' ∩ X''`
  have horbm : ∀ m : ℕ, aDiag ((m : ℝ) • t) • x ∈ X' ∩ X'' := by
    intro m
    simpa only [Nat.cast_zero, zero_smul, aDiag_zero, one_smul] using horb m 0
  -- the reciprocal identity for the contracted box
  have hprod : ν (aDiag ((n : ℝ) • t) • x) (conjBox U ((k : ℝ) • t)) *
      ν (aDiag (((n - k : ℕ) : ℝ) • t) • x) (conjBox U (-((k : ℝ) • t))) = 1 := by
    have h := conjBox_smul_mass_mul hL hcov hU ((k : ℝ) • t)
      (y := aDiag (((n - k : ℕ) : ℝ) • t) • x) (horbm (n - k)) (by
        rw [aDiag_smul_mul, ri_add_smul_nat' t hn]
        exact horbm n)
    rwa [show aDiag ((k : ℝ) • t) •
          (aDiag (((n - k : ℕ) : ℝ) • t) • x) = aDiag ((n : ℝ) • t) • x from by
        rw [aDiag_smul_mul, ri_add_smul_nat' t hn]] at h
  have hD : (ν (aDiag (((n - k : ℕ) : ℝ) • t) • x)
        (conjBox U (-((k : ℝ) • t)))).toReal
      = Real.exp (∑ i ∈ Finset.Icc 1 k,
          growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)) := by
    have h := conjBox_neg_nsmul_toReal hL hcov hU hcontr (m := k)
        (x := aDiag (((n - k : ℕ) : ℝ) • t) • x) (fun j _ => horb (n - k) j)
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [aDiag_smul_mul, ri_add_smul_nat]
  have hMge : Real.exp
        (-(∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)))
      ≤ (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal := by
    have hC : (ν (aDiag ((n : ℝ) • t) • x) (conjBox U ((k : ℝ) • t))).toReal
        = Real.exp (-(∑ i ∈ Finset.Icc 1 k,
            growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x))) := by
      have hto : (ν (aDiag ((n : ℝ) • t) • x) (conjBox U ((k : ℝ) • t))).toReal
          * Real.exp (∑ i ∈ Finset.Icc 1 k,
              growthFun U ν t (aDiag (((n - k + i : ℕ) : ℝ) • t) • x)) = 1 := by
        rw [← hD, ← ENNReal.toReal_mul, hprod, ENNReal.toReal_one]
      rw [Real.exp_neg]
      exact eq_inv_of_mul_eq_one_left hto
    rw [← hC]
    exact ENNReal.toReal_mono hmLtop (measure_mono hsmall)
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) hMge
    rwa [Real.log_exp] at h
  · have hMpos : 0 < (ν (aDiag ((n : ℝ) • t) • x) (V r ∩ (U : Set SL3))).toReal :=
      lt_of_lt_of_le (Real.exp_pos _) hMge
    have h := Real.log_le_log hMpos hMle
    rwa [Real.log_exp] at h

end Work.EKLC6Core
