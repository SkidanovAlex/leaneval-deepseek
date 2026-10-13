import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.htU_near_zero
import Submission.Work.Elliptic.htU_near_pi2
import Submission.Work.Elliptic.exists_bound_of_continuousOn_Ioo
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
import Submission.Work.Elliptic.continuousWithinAt_htPP_zero
import Submission.Work.Elliptic.continuousWithinAt_htPP_pi2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- If `|a| ≤ C` with `0 ≤ C` then `a ^ 2 ≤ C ^ 2`. -/
private lemma sq_le_sq_of_abs_le {a C : ℝ} (hC : 0 ≤ C) (h : |a| ≤ C) : a ^ 2 ≤ C ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg hC]
  exact h

theorem hardy_two_regular (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    ContinuousOn (Work.Elliptic.htPP f) (Set.Icc 0 (π / 2)) ∧
    IntervalIntegrable (Work.Elliptic.htEE f) volume 0 (π / 2) ∧
    IntervalIntegrable (Work.Elliptic.htNN f) volume 0 (π / 2) ∧
    IntervalIntegrable (fun θ => (deriv (deriv f) θ) ^ 2) volume 0 (π / 2) := by
  have hpi : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  have hle : (0 : ℝ) ≤ π / 2 := hpi.le
  obtain ⟨hCU, hcomp1, hcomp2, hid1, hid2, hcu, hcu1, hcu2, hcf2⟩ := htU_interior_facts f hf
  -- ## crude global bound for the second derivative of `f` on the closed interval
  have hg2c : ContinuousOn (iteratedDerivWithin 2 f (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
    hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hpi)
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hg2c
  have hGf : ∃ Cf : ℝ, ∀ x ∈ Set.Ioo 0 (π / 2), |deriv (deriv f) x| ≤ Cf := by
    refine ⟨C2, fun x hx => ?_⟩
    rw [hcomp2 x hx]
    simpa [Real.norm_eq_abs] using hC2 x (Ioo_subset_Icc_self hx)
  -- ## endpoint bounds
  obtain ⟨Cz, δz, _hCznn, hδz, _hfz, _hdfz, _hddz, huz, huz1, hsz⟩ :=
    htU_near_zero f hf h0 hcomp1 hcomp2 hid1 hid2
  obtain ⟨Cp, δp, _hCpnn, hδp, _hfp, _hdfp, _hddp, hup, hup1, hsp⟩ :=
    htU_near_pi2 f hf h1 hcomp1 hcomp2 hid1 hid2
  -- ## global bounds on `(0, π/2)`
  have hGu : ∃ C, ∀ x ∈ Set.Ioo 0 (π / 2), |htU f x| ≤ C :=
    exists_bound_of_continuousOn_Ioo hpi hcu
      ⟨Cz, δz, hδz, fun x hx => huz x (by simpa using hx)⟩
      ⟨Cp, δp, hδp, fun x hx => hup x (by simpa using hx)⟩
  have hGu1 : ∃ C, ∀ x ∈ Set.Ioo 0 (π / 2), |deriv (htU f) x| ≤ C :=
    exists_bound_of_continuousOn_Ioo hpi hcu1
      ⟨Cz, δz, hδz, fun x hx => huz1 x (by simpa using hx)⟩
      ⟨Cp, δp, hδp, fun x hx => hup1 x (by simpa using hx)⟩
  have hsinIoo : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (π / 2)) := by fun_prop
  have hGs : ∃ C, ∀ x ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * x) * deriv (deriv (htU f)) x| ≤ C :=
    exists_bound_of_continuousOn_Ioo hpi (hsinIoo.mul hcu2)
      ⟨Cz, δz, hδz, fun x hx => hsz x (by simpa using hx)⟩
      ⟨Cp, δp, hδp, fun x hx => hsp x (by simpa using hx)⟩
  obtain ⟨Cu, hCu⟩ := hGu
  obtain ⟨Cu1, hCu1⟩ := hGu1
  obtain ⟨Cs, hCs⟩ := hGs
  obtain ⟨Cf, hCf⟩ := hGf
  have hpt : (π / 4) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hCunn : 0 ≤ Cu := le_trans (abs_nonneg _) (hCu _ hpt)
  have hCu1nn : 0 ≤ Cu1 := le_trans (abs_nonneg _) (hCu1 _ hpt)
  have hCsnn : 0 ≤ Cs := le_trans (abs_nonneg _) (hCs _ hpt)
  have hCfnn : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf _ hpt)
  -- ## `htNN` is bounded on `(0, π/2)`
  have hbNN : ∀ x ∈ Set.Ioo 0 (π / 2),
      |htNN f x| ≤ 10 * Cs ^ 2 + 159 * Cu1 ^ 2 + 160 * Cu ^ 2 := by
    intro x hx
    have hs2 : (Real.sin (2 * x)) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * x)
    have hu2 : (htU f x) ^ 2 ≤ Cu ^ 2 := sq_le_sq_of_abs_le hCunn (hCu x hx)
    have hu12 : (deriv (htU f) x) ^ 2 ≤ Cu1 ^ 2 := sq_le_sq_of_abs_le hCu1nn (hCu1 x hx)
    have hs2' : (Real.sin (2 * x) * deriv (deriv (htU f)) x) ^ 2 ≤ Cs ^ 2 :=
      sq_le_sq_of_abs_le hCsnn (hCs x hx)
    have hA : 10 * (Real.sin (2 * x)) ^ 2 * (deriv (deriv (htU f)) x) ^ 2 ≤ 10 * Cs ^ 2 := by
      nlinarith [hs2']
    have hB : (79 + 80 * (Real.sin (2 * x)) ^ 2) * (deriv (htU f) x) ^ 2
        ≤ 159 * Cu1 ^ 2 := by
      have hb : 79 + 80 * (Real.sin (2 * x)) ^ 2 ≤ 159 := by nlinarith [hs2]
      nlinarith [hb, hu12]
    have hC : 160 * (Real.sin (2 * x)) ^ 2 * (htU f x) ^ 2 ≤ 160 * Cu ^ 2 := by
      nlinarith [hs2, hu2]
    have hnn : 0 ≤ 10 * (Real.sin (2 * x)) ^ 2 * (deriv (deriv (htU f)) x) ^ 2
        + (79 + 80 * (Real.sin (2 * x)) ^ 2) * (deriv (htU f) x) ^ 2
        + 160 * (Real.sin (2 * x)) ^ 2 * (htU f x) ^ 2 := by positivity
    rw [show htNN f x = 10 * (Real.sin (2 * x)) ^ 2 * (deriv (deriv (htU f)) x) ^ 2
        + (79 + 80 * (Real.sin (2 * x)) ^ 2) * (deriv (htU f) x) ^ 2
        + 160 * (Real.sin (2 * x)) ^ 2 * (htU f x) ^ 2 from rfl,
      abs_of_nonneg hnn]
    linarith
  -- ## `htEE` is bounded on `(0, π/2)`
  have hbEE : ∀ x ∈ Set.Ioo 0 (π / 2),
      |htEE f x| ≤ 10 * Cf ^ 2 + Cu1 ^ 2 + (10 * Cs ^ 2 + 159 * Cu1 ^ 2 + 160 * Cu ^ 2) := by
    intro x hx
    have hf2 : (deriv (deriv f) x) ^ 2 ≤ Cf ^ 2 := sq_le_sq_of_abs_le hCfnn (hCf x hx)
    have hf2' : 0 ≤ (deriv (deriv f) x) ^ 2 := sq_nonneg _
    have hu12' : 0 ≤ (deriv (htU f) x) ^ 2 := sq_nonneg _
    have hu12 : (deriv (htU f) x) ^ 2 ≤ Cu1 ^ 2 := sq_le_sq_of_abs_le hCu1nn (hCu1 x hx)
    have hnn := hbNN x hx
    have hnn2 : htNN f x ≤ 10 * Cs ^ 2 + 159 * Cu1 ^ 2 + 160 * Cu ^ 2 :=
      le_trans (le_abs_self _) hnn
    have hnn0 : 0 ≤ htNN f x := htNN_nonneg f x
    have hkey : htEE f x = 10 * (deriv (deriv f) x) ^ 2 - (deriv (htU f) x) ^ 2 - htNN f x := rfl
    rw [hkey, abs_le]
    constructor <;> linarith
  -- ## continuity of the three integrands on `(0, π/2)`
  have hcosIoo : ContinuousOn (fun x : ℝ => Real.cos (2 * x)) (Set.Ioo 0 (π / 2)) := by fun_prop
  have hs2c : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ 2) (Set.Ioo 0 (π / 2)) :=
    hsinIoo.pow 2
  have hNNc : ContinuousOn (htNN f) (Set.Ioo 0 (π / 2)) := by
    have hA : ContinuousOn (fun x : ℝ =>
        10 * (Real.sin (2 * x)) ^ 2 * (deriv (deriv (htU f)) x) ^ 2) (Set.Ioo 0 (π / 2)) :=
      (hs2c.const_mul 10).mul (hcu2.pow 2)
    have hB : ContinuousOn (fun x : ℝ =>
        (79 + 80 * (Real.sin (2 * x)) ^ 2) * (deriv (htU f) x) ^ 2) (Set.Ioo 0 (π / 2)) :=
      (continuousOn_const.add (hs2c.const_mul 80)).mul (hcu1.pow 2)
    have hC : ContinuousOn (fun x : ℝ =>
        160 * (Real.sin (2 * x)) ^ 2 * (htU f x) ^ 2) (Set.Ioo 0 (π / 2)) :=
      (hs2c.const_mul 160).mul (hcu.pow 2)
    change ContinuousOn (fun x : ℝ => 10 * (Real.sin (2 * x)) ^ 2
        * (deriv (deriv (htU f)) x) ^ 2 + (79 + 80 * (Real.sin (2 * x)) ^ 2)
        * (deriv (htU f) x) ^ 2 + 160 * (Real.sin (2 * x)) ^ 2 * (htU f x) ^ 2)
        (Set.Ioo 0 (π / 2))
    exact (hA.add hB).add hC
  have hEEc : ContinuousOn (htEE f) (Set.Ioo 0 (π / 2)) := by
    change ContinuousOn (fun x : ℝ => 10 * (deriv (deriv f) x) ^ 2
        - (deriv (htU f) x) ^ 2 - htNN f x) (Set.Ioo 0 (π / 2))
    exact ((hcf2.pow 2).const_mul 10).sub (hcu1.pow 2) |>.sub hNNc
  have hPPc : ContinuousOn (htPP f) (Set.Ioo 0 (π / 2)) := by
    have hsc : ContinuousOn (fun x : ℝ => Real.sin (2 * x) * Real.cos (2 * x))
        (Set.Ioo 0 (π / 2)) := hsinIoo.mul hcosIoo
    have hA : ContinuousOn (fun x : ℝ =>
        40 * Real.sin (2 * x) * Real.cos (2 * x) * (deriv (htU f) x) ^ 2)
        (Set.Ioo 0 (π / 2)) := ((hsinIoo.const_mul 40).mul hcosIoo).mul (hcu1.pow 2)
    have hB : ContinuousOn (fun x : ℝ =>
        80 * (Real.sin (2 * x)) ^ 2 * (htU f x) * deriv (htU f) x) (Set.Ioo 0 (π / 2)) :=
      ((hs2c.const_mul 80).mul hcu).mul hcu1
    change ContinuousOn (fun x : ℝ => 40 * Real.sin (2 * x) * Real.cos (2 * x)
        * (deriv (htU f) x) ^ 2 - 80 * (Real.sin (2 * x)) ^ 2 * (htU f x)
        * deriv (htU f) x) (Set.Ioo 0 (π / 2))
    exact hA.sub hB
  -- ## continuity of `htPP f` on the closed interval
  have hPPc' : ContinuousOn (htPP f) (Set.Icc 0 (π / 2)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0]
      exact continuousWithinAt_htPP_zero f Cu Cu1 hCu hCu1
    · rcases eq_or_lt_of_le hx.2 with hxp | hxp
      · rw [hxp]
        exact continuousWithinAt_htPP_pi2 f Cu Cu1 hCu hCu1
      · exact (hPPc x ⟨hx0, hxp⟩).mono_of_mem_nhdsWithin
          (nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨hx0, hxp⟩))
  refine ⟨hPPc', ?_, ?_, ?_⟩
  · exact intervalIntegrable_of_continuousOn_Ioo_of_bound hle hEEc _ (fun x hx => hbEE x hx)
  · exact intervalIntegrable_of_continuousOn_Ioo_of_bound hle hNNc _ (fun x hx => hbNN x hx)
  · refine intervalIntegrable_of_continuousOn_Ioo_of_bound hle (hcf2.pow 2) (Cf ^ 2) (fun x hx => ?_)
    have h : (deriv (deriv f) x) ^ 2 ≤ Cf ^ 2 := sq_le_sq_of_abs_le hCfnn (hCf x hx)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact h

end Work.Elliptic
