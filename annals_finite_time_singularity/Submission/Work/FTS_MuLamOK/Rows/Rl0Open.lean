import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAll
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSupO
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-!
# Row 15 of the §8 table, `T2` vocabulary: `N₂^{ss}`

`N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*` is the star-star piece of the second-order row.  Its weighted
form on the open quadrant is the product

  `((z+1)³/z²)·N₂^{ss} = (2·C15 α θ)·G15 α Φs z θ`

(`Work.FTS.NonlinRows.N2ss_weighted_eq`), a `θ`-only angular factor times the weighted star
coefficient `G15 = ((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)`, whose `𝒲^{4,∞}`-membership (the field `UszW` of
`VocabO2.StarPkgo2`) is exactly what the primed interface provides and what this row consumes.

The proof is the two-step scheme of the sibling rows 10/11: the pointwise `ℋ⁴`-bounds of the
open representative `N2ssO` (`Work.FTS.NonlinRows.row15_ptBound`, proved in
`NRow15T2Aux/Bound.lean`) are fed to the open-quadrant transfer
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, and the result is transported to `N₂^{ss}` itself
along the agreement of the two functions on the open quadrant
(`HkIntegrand_congr`, `HkSq_congr_open`).
-/


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.zslot_le_gain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.GainSlot

set_option maxHeartbeats 1000000

/-! ## Two elementary facts about the routed kernel derivative `KdK ρ ε a b`

The routed density `Λ = LamFull ρ ε c M` of `GainDefs.lean` is supported in the closed ball of
radius `ε` (it is a rescaled kernel whose density is supported in the unit ball).  We need the
same for the routed kernel derivative `KdK ρ ε a b = ∂₁^a∂₂^b (Jker ρ ε)`, together with the
integrability of `|KdK|` against any function continuous on that ball — this is the input of the
weighted Cauchy–Schwarz core `StepFacts.SlotAux.srb_cs_core`. -/

/-- The routed kernel derivative vanishes off the ball of radius `ε`. -/
private theorem KdK_eq_zero_of_notMem_ball {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall 0 ε) : Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p = 0 := by
  rw [Work.FTS.StrongEps.EpsE4Thr.Kd_Jker_scale hρ ε a b p]
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  have hzero : Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b (ε⁻¹ • p) = 0 := by
    by_contra hne
    have h1 := Work.FTS.StrongEps.EpsE4Thr.Kdr_support hρ a b (ε⁻¹ • p) hne
    have hq1 : |(ε⁻¹ • p).1| ≤ 1 := by
      have : (ε⁻¹ • p).1 ^ 2 ≤ 1 := by linarith [sq_nonneg (ε⁻¹ • p).2]
      rwa [sq_le_one_iff_abs_le_one] at this
    have hq2 : |(ε⁻¹ • p).2| ≤ 1 := by
      have : (ε⁻¹ • p).2 ^ 2 ≤ 1 := by linarith [sq_nonneg (ε⁻¹ • p).1]
      rwa [sq_le_one_iff_abs_le_one] at this
    have hqle : max |(ε⁻¹ • p).1| |(ε⁻¹ • p).2| ≤ 1 := max_le hq1 hq2
    have hgt : 1 < max |(ε⁻¹ • p).1| |(ε⁻¹ • p).2| := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hε.le)]
      rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr hε.le)]
      have h1 : (1 : ℝ) = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      rw [h1]
      exact mul_lt_mul_of_pos_left hmax (by positivity)
    linarith
  rw [show Work.FTS.StrongEps.Jker (Work.FTS.StrongEps.EpsE4Thr.Kdr ρ a b) ε p = 0 from by
    simp only [Work.FTS.StrongEps.Jker, hzero, mul_zero], mul_zero]

/-- `|KdK ρ ε a b|` is integrable against any function continuous on the ball of radius `ε`
(the kernel derivative is continuous and supported there). -/
private theorem integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ)
    {B : ℝ × ℝ → ℝ} (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p) := by
  have hcont : Continuous (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|) :=
    (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε a b).abs
  have hon : IntegrableOn (fun p : ℝ × ℝ => |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (hcont.continuousOn.mul hB).integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_ball hρ hε a b hp, abs_zero, zero_mul]

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `zslot_le_gain`.
`Λ := LamFull ρ ε c M` dominates every routed kernel derivative up to order `M` (see
`GainDefs.lean`: `abs_KdK_mul_exp_le_LamFull`, `integral_abs_KdK_le_KgainBig`,
`LamFull_nonneg`).  Template: `StepFacts/slot_route_bounds.lean` + `StepFacts/SlotBounds.lean:zslot_le`;
the routed identity is `Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ a 0 0 0 le_rfl le_rfl`,
whose `iteratedDeriv`-kernel is `KdK ρ ε a 0` (`Work.FTS.StrongEps.Kd_eq`), and the `i = 0` slot of
`HkIntegrand α k f` supplies the leftover. -/
theorem zslot_le_gain {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) {M k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    {a : ℕ} (ha : a ≤ M) :
    ENNReal.ofReal ((Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  -- the routed identity: `D_z^a (J_ε f)` against the kernel derivative `KdK ρ ε a 0`
  have hroute : Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p
          * f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    have h := Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ a 0 0 0
      (Nat.zero_le a) le_rfl
    simp only [Work.Spaces.mixed_zero_right] at h
    rw [h]
    simp only [Nat.sub_zero, pow_zero, one_mul, iteratedDeriv_zero, Work.Spaces.DzIter_zero]
    congr 1
    ext p
    simp only [Work.FTS.StrongEps.EpsE4Thr.KdK, Work.FTS.StrongEps.Kd_eq, iteratedDeriv_zero]
  have hW₀ : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Work.FTS.StrongEps.StepFacts.srb_wdiv_nonneg hz hθ
  -- continuity of the two shifted factors on the ball of radius `ε`
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) := by
    have hbase : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed 0 0 f q.1 q.2)
        (Work.FTS.StrongEps.Kz z ε ×ˢ Work.FTS.StrongEps.Kth θ ε) :=
      (Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad hf 0 0).mono
        (Work.FTS.StrongEps.Kz_prod_Kth_subset_Quad hz hε hθ)
    have hh := Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball (ε := ε) hz hθ hbase
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using hh
  have hWcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
        / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun x y => Work.Spaces.w x / (Real.sin (2 * y)) ^ (Work.Spaces.eta / 2))
      (Work.FTS.StrongEps.HkSqAux.continuousOn_wdiv_region (z := z) (ε := ε) hz hε hθ)
  -- the three integrability inputs of the Cauchy–Schwarz core
  have hKint : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|) := by
    simpa using integrable_abs_KdK_mul hρ hε a 0 (B := fun _ : ℝ × ℝ => (1 : ℝ))
      continuousOn_const
  have hQ : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p| * Real.exp (2 * c * (|p.1| + |p.2|))
        * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have hB : ContinuousOn (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))
        * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2)
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      (Work.FTS.StrongEps.StepFacts.srb_continuous_exp_two c).continuousOn.mul
        ((hGcont.mul hWcont).pow 2)
    simpa only [mul_assoc] using integrable_abs_KdK_mul hρ hε a 0 hB
  have hK2 : Integrable (fun p : ℝ × ℝ =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
        * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have hB : ContinuousOn (fun p : ℝ × ℝ =>
        (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      (hGcont.mul continuousOn_const).pow 2
    exact integrable_abs_KdK_mul hρ hε a 0 hB
  -- the weighted Cauchy–Schwarz core
  have hslot := Work.FTS.StrongEps.StepFacts.srb_cs_core
    (K := fun p : ℝ × ℝ => Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p)
    (G := fun p : ℝ × ℝ =>
      f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (W := fun p : ℝ × ℝ => Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
      / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2))
    (W₀ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
    (c := c) (M := Work.Spaces.DzIter a (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
    hW₀ hW hKint hQ hK2 hroute
  -- the constants and the pointwise domination by `Λ · HkIntegrand`
  have hK : 0 ≤ ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p| :=
    integral_nonneg fun p => abs_nonneg _
  have hKK : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|)
      ≤ Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M :=
    Work.FTS.StrongEps.EpsE4Thr.integral_abs_KdK_le_KgainBig hρ hε ha (Nat.zero_le M)
  have hF : ∀ p : ℝ × ℝ, 0 ≤ |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (Work.FTS.StrongEps.EpsE4Thr.LamFull_nonneg hρ hε M p)
      (Work.Spaces.HkIntegrand_nonneg α k f _ _)
  have hFF : ∀ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p
        * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
        * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p :=
      Work.FTS.StrongEps.EpsE4Thr.abs_KdK_mul_exp_le_LamFull hρ hε hε1 hc (by omega) p
    have h2 : (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
      have := Work.Spaces.sq_le_HkIntegrand_z α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2) 0 (Nat.zero_le k)
      simpa only [Work.Spaces.DzIter_zero] using this
    exact mul_le_mul h1 h2 (sq_nonneg _) (Work.FTS.StrongEps.EpsE4Thr.LamFull_nonneg hρ hε M p)
  have hfinal : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p
        * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    lintegral_congr_ae (Eventually.of_forall fun p =>
      ENNReal.ofReal_mul (Work.FTS.StrongEps.EpsE4Thr.LamFull_nonneg hρ hε M p))
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (Work.FTS.StrongEps.StepFacts.ofReal_mul_integral_le_lintegral hK
      (Work.FTS.StrongEps.EpsE4Thr.KgainBig_nonneg hρ ε M) hKK hF hF' hFF)).trans ?_
  rw [hfinal]

end Work.FTS.StrongEps.EpsE4Thr.GainSlot
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LimGdot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot)

set_option autoImplicit false




end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StrongEpsP.EpsGlue_of_glueP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.StrongEps.StrongEpsP
end
-- ===== merged: Submission.Work.FTS.StrongEps.StrongEpsP.FirstStepP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.StrongEps.StrongEpsP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkFstarBlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

open Work.FTS.Galerkin (Fn)
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The block `N₄^{g*} + N₅^{g*}` of the level-three right-hand side

`N₄^{g*}` (row 21) and `N₅^{g*}` (row 25a) are the two rows of the nonlinear right-hand side in
which the angular moment `FK f` of the perturbation `f` multiplies the *star* profile `F_*`.
Since `F_* α z θ = α (Γ(θ)/c α)·2 hKer z` with `hKer z = z/(1+z)²`, their sum factors as

  `N₄^{g*} α f z θ + N₅^{g*} α f z θ = aProf α θ · rProf f z`

(`N4gs_add_N5gs_factor`), with the *single* angular profile `aProf` and the *single* radial
factor `r f z = FK f z · hKer z`.  Everything therefore reduces to the `θ`/`z`-separation
estimate for an angular `×` radial product:

* the angular profile `aProf` and its `D_θ`-iterates up to order `4` are `O(α)` with an explicit
  majorant whose square times `sin(2θ)^{-γ}` is integrable with an `O(1/α)` bound (`AngProfAll`);
* the radial factor `r = FK f · hKer` is honest in `ℋ⁴` with an `α`-independent bound by the
  `ℋ⁴`-norm of `FK f` (`HKerRadialMul`), because `hKer` is a fixed bounded `C^∞` radial
  multiplier (`ZslotSupBound6`);
* `Xₙ α (aProf · r) ≤ K · Xₙ α r` (`XN_ang_rad_le_gen`, via `AngProfAll`);
* the descent from level `4` to level `3` uses the pointwise monotonicity of the integrand plus
  the open-quadrant continuity of the level-`3` integrand (`contHkAngRad`).

The `C^{m}`-smoothness (`m ≤ 5`) of `z ↦ FK f z` on `(0,∞)` needed for the Leibniz rules is
`contDiffOn_FK` of `NfkAux.Basic` (`SmoothOpen f` + `HkMem α 6 f`, i.e. the `HQo α 6` field of
`H6Adm`).
-/

/-! ## The factorisation of the block -/

/-- **`N₄^{g*} + N₅^{g*}` is a product of an angular profile and a radial function.**

`∂_θF_* = (α/c)·F_*'(z)·Γ'(θ)` with `F_*'(z) = 2 hKer z` (so that `FK f · ∂_θF_*` carries the
radial factor `FK f · hKer`), and `F_* = α(Γ/c)·2 hKer`; with `D_θΓ = sin(2θ)·Γ'` this gives

`N₄^{g*} = -(α/c)·D_θΓ(θ) · (FK f z · hKer z)`,
`N₅^{g*} = -(2α/c)·sin²θ·Γ(θ) · (FK f z · hKer z)`,

whence the sum.  The identity is unconditional (no regularity hypothesis is used). -/
theorem N4gs_add_N5gs_factor (α : ℝ) (g : Fn) :
    (fun z θ => Work.FTS.Nonlin.N4gs α g z θ + Work.FTS.Nonlin.N5gs α g z θ)
      = fun z θ => aProf α θ * rProf g z := by
  funext z θ
  have hF : Work.FM.Fstar z = 2 * Work.Spaces.hKer z := by
    rw [Work.FM.Fstar, Work.Spaces.hKer_apply]; ring
  rw [Work.FTS.Nonlinear.Pieces.RNP.N4gs_factor]
  simp only [Work.FTS.Nonlin.N5gs, Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf,
    Work.FTS.StrongPersist.L3Rhs.NfkAux.rProf, Work.Construction.Fstar, hF]
  ring

/-! ## The target -/

theorem NfkFstarBlock : ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
    ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (MK : ℝ),
      0 < α → α ≤ 1 →
      Work.FTS.StrongPersist.H6Adm α f →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK f z) →
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK f z) ≤ MK →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ) ∧
      Work.Spaces.HkSq α 3
          (fun z θ => Work.FTS.Nonlin.N4gs α f z θ + Work.FTS.Nonlin.N5gs α f z θ)
        ≤ C * α ^ (-Cpow) * (1 + MK) ^ 2 := by
  obtain ⟨K₀, K₁, K₂, KA, hK₀, hK₁, hK₂, hKA, hang⟩ := AngProfAll
  obtain ⟨KR, hKR, hrad⟩ := HKerRadialMul
  refine ⟨(KA * (Real.sqrt KR + 1)) ^ 2 + 1, 0, by positivity, le_refl 0, ?_⟩
  intro α f MK hα hα1 hadm hmemFK hXnFK
  -- ### the smoothness of the datum, and of the angular moment `FK f`
  have hsmO : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hadm.reg.2
  have hFK4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_FK hα hα1 hsmO hmem6 4 (by norm_num)
  -- ### the two separation children
  obtain ⟨hcontR, hmemr, hSqr⟩ := hrad α hα hα1 (fun z => Work.Construction.FK f z) hFK4 hmemFK
  obtain ⟨hcontA, ha0, ha1, hGnn, hGint, _hMint, hXnSep⟩ := hang α hα hα1
  -- ### level-four membership of `aProf · rProf`
  have hmem4 : Work.Spaces.HkMem α 4 (fun z θ => aProf α θ * rProf f z) :=
    Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le (α := α) (a := aProf α) (r := rProf f)
      (B0 := K₀ * α) (B1 := K₁ * α) (G := Gprof α)
      (by positivity) (by positivity) hGnn ha0 ha1 hGint
      Work.FTS.NonlinRows.AuxAngRad.integrableOn_smE hmemr hcontA hcontR
  -- ### level-three membership of `aProf · rProf`
  have hcont3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 3 (fun z θ => aProf α θ * rProf f z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contHkAngRad 3 α (aProf α) (rProf f)
      (fun i hi => hcontA i (le_trans hi (by norm_num)))
      (fun b hb => hcontR b (le_trans hb (by norm_num)))
  have hmem3 : Work.Spaces.HkMem α 3 (fun z θ => aProf α θ * rProf f z) :=
    Work.FTS.LocData.HkMem_of_majorant α 3 (f := fun z θ => aProf α θ * rProf f z)
      (M := fun z θ => Work.Spaces.HkIntegrand α 4 (fun z θ => aProf α θ * rProf f z) z θ)
      hcont3 hmem4.1 hmem4.2
      (fun z _ θ _ => Work.FTS.StrongLWP.HkIntegrand_mono α _ (by norm_num) z θ)
  -- ### the norm bound
  have hMKnn : 0 ≤ MK := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hXnFK
  have hsqFK : Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z) ≤ MK ^ 2 := by
    have hnn : 0 ≤ Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z) :=
      Work.Spaces.HkSq_nonneg α 4 _
    calc Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z)
        = (Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z))) ^ 2 :=
          (Real.sq_sqrt hnn).symm
      _ ≤ MK ^ 2 := by
          refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 2
          simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm] using hXnFK
  have hXn_r : Work.FTS.Nonlin.Xn α (fun z θ => rProf f z) ≤ Real.sqrt KR * MK := by
    have h1 : Work.Spaces.HkSq α 4 (fun z _ => rProf f z)
        ≤ KR * Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z) := hSqr
    have h2 : Work.FTS.Nonlin.Xn α (fun z θ => rProf f z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => rProf f z)) := rfl
    rw [h2]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => rProf f z))
        ≤ Real.sqrt (KR * Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK f z)) :=
          Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (KR * MK ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          exact mul_le_mul_of_nonneg_left hsqFK hKR.le
      _ = Real.sqrt KR * |MK| := by
          rw [Real.sqrt_mul hKR.le, Real.sqrt_sq_eq_abs]
      _ = Real.sqrt KR * MK := by rw [abs_of_nonneg hMKnn]
  have hXn_ar : Work.FTS.Nonlin.Xn α (fun z θ => aProf α θ * rProf f z)
      ≤ KA * (Real.sqrt KR * MK) := by
    have h5 := hXnSep (fun z => rProf f z) hmemr
    have h6 : KA * Work.FTS.Nonlin.Xn α (fun z θ => rProf f z)
        ≤ KA * (Real.sqrt KR * MK) :=
      mul_le_mul_of_nonneg_left hXn_r hKA.le
    linarith
  -- ### the value bound
  have hSq4ar : Work.Spaces.HkSq α 4 (fun z θ => aProf α θ * rProf f z)
      = (Work.FTS.Nonlin.Xn α (fun z θ => aProf α θ * rProf f z)) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    exact (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)).symm
  have hSq3 : Work.Spaces.HkSq α 3 (fun z θ => aProf α θ * rProf f z)
      ≤ (KA * (Real.sqrt KR * MK)) ^ 2 := by
    refine le_trans (Work.FTS.StrongLWP.HkSq_mono_of_mem (α := α) (k := 4) (k' := 3)
      (by norm_num) hmem4) ?_
    rw [hSq4ar]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn_ar 2
  rw [N4gs_add_N5gs_factor α f]
  refine ⟨hmem3, ?_⟩
  have hfin : (KA * (Real.sqrt KR * MK)) ^ 2
      ≤ ((KA * (Real.sqrt KR + 1)) ^ 2 + 1) * α ^ (-(0 : ℝ)) * (1 + MK) ^ 2 := by
    rw [neg_zero, Real.rpow_zero, mul_one]
    have h1 : Real.sqrt KR * MK ≤ (Real.sqrt KR + 1) * (1 + MK) := by
      nlinarith [Real.sqrt_nonneg KR, hMKnn]
    have h2 : KA * (Real.sqrt KR * MK) ≤ KA * (Real.sqrt KR + 1) * (1 + MK) := by
      have h2' : KA * (Real.sqrt KR * MK) ≤ KA * ((Real.sqrt KR + 1) * (1 + MK)) :=
        mul_le_mul_of_nonneg_left h1 hKA.le
      linarith [h2']
    have h3 : (KA * (Real.sqrt KR * MK)) ^ 2
        ≤ (KA * (Real.sqrt KR + 1) * (1 + MK)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hKA.le (mul_nonneg (Real.sqrt_nonneg KR) hMKnn)) h2 2
    have h4 : (KA * (Real.sqrt KR + 1) * (1 + MK)) ^ 2
        = (KA * (Real.sqrt KR + 1)) ^ 2 * (1 + MK) ^ 2 := by ring
    have h5 : (KA * (Real.sqrt KR + 1)) ^ 2 * (1 + MK) ^ 2
        ≤ ((KA * (Real.sqrt KR + 1)) ^ 2 + 1) * (1 + MK) ^ 2 := by
      nlinarith [sq_nonneg (1 + MK), sq_nonneg (KA * (Real.sqrt KR + 1))]
    rw [h4] at h3
    linarith [h3, h5]
  exact le_trans hSq3 hfin

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.Rl0Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK.Rows

open Work.FTS.StrongPersist.H6Pair6Aux (A₀ B₀ B₀_nonneg)

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem Rl0Open : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) := by
  refine ⟨10 ^ 5, by norm_num, ?_⟩
  intro α f hα hα1 hso hmem
  -- ## the three delivered analytic inputs
  have hsup : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 f z| ≤ 3 * Work.FTS.Nonlin.Xn α f :=
    Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hso hmem
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (A₀ α (Work.FTS.Nonlin.Xn α f) * Work.Spaces.HkIntegrand α 4 f r θ
              + B₀ α (Work.FTS.Nonlin.Xn α f) * (1 / (1 + r)) ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open hα hα1 hso hsup
  have hcont : ContinuousOn
      (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α f) f))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hso hmem
  -- ## notation
  set X : ℝ := Work.FTS.Nonlin.Xn α f with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 f
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ with hΨ
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  set Φ : ℝ → ℝ := fun r =>
    7 * (A₀ α X * Ψ r
      + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) with hΦ
  -- ## the weighted angular energy of `N₀` is dominated by `Φ`
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
          * ((1 + r) / r) ^ 2 ≤ Φ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by
      simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
    have hΦr : Φ r = 7 * (A₀ α X * Ψ r
        + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) := by rw [hΦ]
    rw [hweq, ← MeasureTheory.integral_mul_const, hΦr]
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hstep : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
            * Work.Spaces.w r)
        ≤ ∫ θ in Work.Spaces.Iθ,
          7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
            + B₀ α X * (1 / (1 + r)) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
      · refine (((hmem.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
        refine MeasureTheory.integrableOn_const ?_
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top
      · rw [hIoo2]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => by simpa only [hX] using hpt r hr θ hθ)
    refine hstep.trans ?_
    have hintA : MeasureTheory.IntegrableOn
        (fun θ => A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iθ :=
      (hmem.1 r hzr).const_mul (A₀ α X)
    have hintB : MeasureTheory.IntegrableOn
        (fun θ => B₀ α X * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hvalPsi : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) = Ψ r := rfl
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
      MeasureTheory.integral_const_mul, Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra, hvalPsi]
    exact le_of_eq (by ring)
  -- ## slice integrability of the squared `N₀`
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by
      simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hslice : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hr0
    have hmaj : MeasureTheory.Integrable
        (fun θ => 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (((hmem.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
        ≤ (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
          * Work.Spaces.w r := by
          nlinarith [hW1,
            sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)]
      _ ≤ 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2) := by
          simpa only [hX] using hpt r hr θ hθ
  -- ## a.e. strong measurability of the weighted angular energy
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.aesm_weighted_energy_of_continuousOn hcont
  -- ## integrability of the majorant `Φ`
  have hΦint : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    exact (h1.add h2).const_mul 7
  -- ## the zero-mode bound from the pointwise domination
  have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := Work.Construction.N0 α (Work.Construction.Ftot α f) f)
    hsl hmeas hΦint hbd
  -- ## evaluation of `∫Φ`
  have hΨval : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = X ^ 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = Work.Spaces.HkSq α 4 f := by
      rw [hΨ, Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : X ^ 2 = Work.Spaces.HkSq α 4 f := by
      rw [hX, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [h1, h2]
  have hΦval : (∫ r in Set.Ioi (0 : ℝ), Φ r)
      = 7 * (A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
          * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    rw [hΦ, MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hΨval]
  have hInt_le : (∫ r in Set.Ioi (0 : ℝ), Φ r)
      ≤ 7 * (A₀ α X * X ^ 2 + Real.pi * B₀ α X) := by
    rw [hΦval]
    have hc2 : (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
    have hB2 : ((Real.pi / 2) * B₀ α X) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
        ≤ ((Real.pi / 2) * B₀ α X) * 2 :=
      mul_le_mul_of_nonneg_left hc2 (mul_nonneg (by positivity) (B₀_nonneg α X))
    have he : ((Real.pi / 2) * B₀ α X) * 2 = Real.pi * B₀ α X := by ring
    nlinarith [hB2]
  -- ## the final numeric comparison
  calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) := hmain
    _ ≤ 3 * Real.sqrt (7 * (A₀ α X * X ^ 2 + Real.pi * B₀ α X)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hInt_le) (by norm_num)
    _ ≤ 10 ^ 5 * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) := by
        have h := rl0_final (α := α) (X := X) hα hα1 hX0
        rw [hX] at h
        exact h

end Work.FTS_MuLamOK.Rows

end
end
