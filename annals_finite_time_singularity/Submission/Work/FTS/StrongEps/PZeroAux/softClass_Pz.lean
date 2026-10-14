import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.classC_Pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

/-! ## Elementary facts about the correction profile `bump` -/


/-- `bump` is supported in the box `[1/2,1] × [π/8,3π/8]`, strictly inside the open quadrant. -/
theorem classC_Pz_suppIn_bump : Work.FTS.GalBasis.SuppIn bump (1 / 2) 1 (π / 8) := by
  intro z θ h
  by_contra hne
  have hne' : bump z θ ≠ 0 := hne
  rw [bump_ne_zero_iff] at hne'
  obtain ⟨hz, hth⟩ := hne'
  rcases h with h | h
  · exact h ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  · refine h ⟨?_, ?_⟩
    · linarith [hth.1, Real.pi_pos]
    · linarith [hth.2]

/-- `bump` is `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2` (it is `C^∞` everywhere). -/
theorem classC_Pz_smoothQuad_bump : Work.FTS.LocData.SmoothQuad bump :=
  contDiffOn_iff_forall_nat_le.mpr (fun m _ => (contDiff_bump m).contDiffOn)

/-- **`bump ∈ ℋᵏ`** for every `α` and every `k`, by the box support of `bump`. -/
theorem classC_Pz_hkMem_bump (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k bump :=
  Work.FTS.GalLimit.Closure.hkMem_of_suppIn α k (by norm_num) (by norm_num)
    (by linarith [Real.pi_pos]) classC_Pz_smoothQuad_bump classC_Pz_suppIn_bump





/-! ## The main theorem -/


end Work.FTS.StrongEps.PZeroAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false

/-! ## Elementary auxiliary facts about `bump` -/

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h := hf.forall n
  have hfun : Function.uncurry (fun z θ : ℝ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [hfun]
  exact contDiffOn_const.mul h



/-- The bump profile lies in `ℋ^k` for every `k`: it is smooth on the open quadrant and
supported in the compact box `[1/2,1] × [π/4,3π/8]`, so its `ℋ^k`-integrand is dominated by
the integrable majorant `4 M / (z+1)²`. -/
theorem HkMem_bump (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := by
  obtain ⟨M0, hM0nn, hM0⟩ := Work.FTS.StrongEps.exists_bound_HkIntegrand_bump α k
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := Work.FTS.StrongEps.bump) (M := fun z θ => 4 * M0 * (z + 1) ^ (-2 : ℝ))
    (Work.FTS.StrongEps.continuousOn_HkIntegrand_bump α k) ?_ ?_ ?_
  · intro z hz
    refine MeasureTheory.integrableOn_const (hs := ?_)
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · have hbase : MeasureTheory.IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ))
        (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : MeasureTheory.IntegrableOn
        (fun x : ℝ => (4 * M0) * (π / 2) * (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hbase.const_mul _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, 4 * M0 * (z + 1) ^ (-2 : ℝ))
          = (4 * M0) * (π / 2) * (z + 1) ^ (-2 : ℝ) := by
      intro z _
      rw [MeasureTheory.setIntegral_const, Work.Spaces.volume_real_Iθ, smul_eq_mul]
      ring
    have hcon : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, 4 * M0 * (z + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    have hae : Set.Ici (0 : ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
    rw [Work.Spaces.Iz]
    exact hcon.congr_set_ae hae
  · intro z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    rcases le_or_gt z 1 with hz1 | hz1
    · have hp : (4 : ℝ)⁻¹ ≤ (z + 1) ^ (-2 : ℝ) := by
        have h1 : (2 : ℝ) ^ (-2 : ℝ) ≤ (z + 1) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
        have h2 : ((2 : ℝ) ^ (-2 : ℝ)) = (4 : ℝ)⁻¹ := by norm_num
        rw [h2] at h1
        exact h1
      have : M0 ≤ 4 * M0 * (z + 1) ^ (-2 : ℝ) := by nlinarith [hp, hM0nn]
      exact le_trans (hM0 z θ) this
    · rw [Work.FTS.StrongEps.HkIntegrand_bump_eq_zero_of_not_mem α k (Or.inr (Or.inl hz1))]
      exact mul_nonneg (mul_nonneg (by norm_num) hM0nn) (Real.rpow_nonneg (by linarith) _)


/-! ## The projection preserves the mollifier class -/


end Work.FTS.StrongEps.PZeroAux
end
end
