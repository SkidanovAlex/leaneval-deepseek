/-
# `Transfer/E2pkg/RadS.lean` — weighted `L²`-integrability of the `D_z`-iterates of `radS`

For `f ∈ CoerAdm α` and `j ≤ 3`,

  `∫_0^∞ (D_z^j (radS α f)(z))² w(z)² dz < ∞`,

the radial input of the `ℋ^n`-membership of the second summand `Γ(θ)·radS α f z` of the
transfer defect `E2 α f`.  The pointwise majorant is `RadSBnd.SmajA`, whose integral is finite
by `E1Parts.L12f_DzdIter_sq_w_sq_integrable_Ioi`, `E1Parts.Qang_sq_w_sq_integrable_Ioi` and
`E1Parts.ampB_DzdIter_sq_w_sq_integrable_Ioi`; the a.e. strong measurability of the integrand
comes from its continuity on `(0,∞)` (`AuxE2.radS_contDiffOn_three`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSBnd
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five
import Submission.Work.H2.T1Q.PwBdQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Integrability of the majorant -/

/-- The majorant `SmajA α f j K` is integrable on `(0,∞)` for `j ≤ 3`. -/
theorem integrableOn_SmajA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ 3) (K : ℝ) :
    IntegrableOn (SmajA α f j K) IoiA := by
  have hL : IntegrableOn (fun z : ℝ => ∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      IoiA := by
    refine MeasureTheory.integrable_finsetSum _ fun b hb => ?_
    have hbj : j - b ≤ 3 := by
      have := Finset.mem_range.mp hb
      omega
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable_Ioi α hα hα1 hf
      (j - b) hbj
  have hQ : IntegrableOn (fun z : ℝ => ∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) IoiA := by
    refine MeasureTheory.integrable_finsetSum _ fun b hb => ?_
    have hbj : j - b ≤ 4 := by
      have := Finset.mem_range.mp hb
      omega
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_sq_w_sq_integrable_Ioi α hα hα1
      hf.reg.1 (Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hf.reg.1 hf.reg.2.1)
      (i := j - b) hbj
  have hB : IntegrableOn (fun z : ℝ =>
      (Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) IoiA := by
    refine Work.FTS.CoercivityFix.Transfer.E1Parts.ampB_DzdIter_sq_w_sq_integrable_Ioi α hα hα1
      (c := j + 1) ?_
    omega
  have hmain : IntegrableOn (fun z : ℝ =>
      ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2)) IoiA :=
    ((hL.const_mul _).add (hQ.const_mul _)).add (hB.const_mul _)
  exact hmain.const_mul 3

/-! ## The main statement -/

/-- **Weighted `L²`-integrability of the `D_z`-iterates of `radS`.** -/
theorem radS_DzdIter_sq_w_sq_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ j ≤ 3, IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  obtain ⟨K, hKnn, hKbd⟩ := ampA_dzdIter_bound α hα hα1
  have hsmR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radS α f) IoiA :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1
      (Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five α hα hα1
        hf.reg.1 hf.reg.2.1 hf.l12)
  intro j hj
  have hMaj : IntegrableOn (SmajA α f j K) IoiA := integrableOn_SmajA α hα hα1 hf hj K
  have hMajIz : IntegrableOn (SmajA α f j K) Work.Spaces.Iz :=
    hMaj.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    have hcontR : ContinuousOn (fun z : ℝ =>
        Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) IoiA := by
      rw [DzdIter_eq_Zop_iter]
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
        (b := j) (n := 0) (hu := hsmR.of_le (Nat.cast_le.mpr hj))
    have hwcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) IoiA := by
      have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
      rw [hfun]
      exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
    exact Work.H2.T1Q.aesm_Iz_of_continuousOn (hcontR.pow 2 |>.mul hwcont)
  have hbound : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ‖(Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2‖ ≤ SmajA α f j K z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz0 with h | h
    · subst h
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      rw [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      have h0 : SmajA α f j K 0 = 0 := by
        simp only [SmajA, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
          Finset.sum_const_zero, add_zero]
      rw [h0]
    · exact radS_sq_le_SmajA α hα hα1 hf hj hKnn hKbd z h
  exact Integrable.mono' hMajIz haesm hbound

end Work.FTS.CoercivityFix.Transfer.E2pkg
