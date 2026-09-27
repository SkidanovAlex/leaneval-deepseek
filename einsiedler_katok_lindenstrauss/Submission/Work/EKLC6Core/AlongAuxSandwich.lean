import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.conjBox_neg_nsmul_toReal_along
import Submission.Work.EKLC6Core.conjBox_smul_mass_mul_along
import Submission.Work.EKLC6Core.log_mass_sandwich

/-!
# `EKLC6Core.log_mass_sandwich_alongAux`

`Work.EKLC6Core.log_mass_sandwich` with the full `A`-covariance `ACovariant ν X''` replaced by
the covariance along the integer multiples of the single direction `t`
(`ACovariantAlong ν t X''`).  The proof is line-for-line the one of `log_mass_sandwich`; the two
covariance inputs `conjBox_neg_nsmul_toReal` and `conjBox_smul_mass_mul` are replaced by their
`_along` versions `conjBox_neg_nsmul_toReal_along` and `conjBox_smul_mass_mul_along`, which are
already proved in this workspace.

(The module `Submission.Work.EKLC6Core.log_mass_sandwich_along` states the same lemma, but its
file still contains an unfinished proof; this copy is self-contained and complete so that it can
be used in the entropy chain.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem log_mass_sandwich_alongAux {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'')
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
    have h := conjBox_neg_nsmul_toReal_along hL hcov hU hcontr (m := k)
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
    have h := conjBox_smul_mass_mul_along hL hcov hU ((k : ℝ) • t)
      ⟨(k : ℤ), by push_cast; rfl⟩
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
    have h := conjBox_neg_nsmul_toReal_along hL hcov hU hcontr (m := k)
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

end
