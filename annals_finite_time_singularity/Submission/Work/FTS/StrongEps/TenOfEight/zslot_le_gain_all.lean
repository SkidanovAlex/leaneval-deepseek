import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.TenOfEight.LamAllDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.zslot_le_gain
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.StepFacts.slot_route_bounds
import Submission.Work.FTS.StrongEps.StepFacts.SlotBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.TenOfEight

set_option maxHeartbeats 1000000

/-! ## Two elementary facts about the routed kernel derivative `KdK ρ ε a b`

The routed density `Λ = LamAll ρ ε c M` of `LamAllDefs.lean` is supported in the closed ball of
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

/-- `Work.FTS.StrongEps.TenOfEight.zslot_le_gain_all` (namespace `Work.FTS.StrongEps.TenOfEight`).

**Recipe.** Copy `Submission/Work/FTS/StrongEps/EpsE4Thr/GainSlot/zslot_le_gain.lean` into the
new file (including its private helpers `KdK_eq_zero_of_notMem_ball` and
`integrable_abs_KdK_mul`, which are `private` and hence must be reproduced), then
(i) drop the hypothesis `hε1 : ε ≤ 1`,
(ii) replace the density `Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M` everywhere by
`Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M` (defined in
`Submission/Work/FTS/StrongEps/TenOfEight/LamAllDefs.lean`),
(iii) replace the two uses of `LamFull_nonneg hρ hε M` by `LamAll_nonneg hρ hε M` and the use
of `abs_KdK_mul_exp_le_LamFull hρ hε hε1 hc (by omega) p` by
`abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p`
(both live in `Work.FTS.StrongEps.TenOfEight`).
Nothing else changes: the mass constants `KgainBig`/`Ksm` are unchanged. -/
theorem zslot_le_gain_all {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) (hc : 0 ≤ c) {M k : ℕ} {f : ℝ → ℝ → ℝ}
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
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p)
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
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (LamAll_nonneg hρ hε M p)
      (Work.Spaces.HkIntegrand_nonneg α k f _ _)
  have hFF : ∀ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p
        * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a 0 p|
        * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p :=
      abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p
    have h2 : (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
      have := Work.Spaces.sq_le_HkIntegrand_z α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2) 0 (Nat.zero_le k)
      simpa only [Work.Spaces.DzIter_zero] using this
    exact mul_le_mul h1 h2 (sq_nonneg _) (LamAll_nonneg hρ hε M p)
  have hfinal : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p
        * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    lintegral_congr_ae (Eventually.of_forall fun p =>
      ENNReal.ofReal_mul (LamAll_nonneg hρ hε M p))
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (Work.FTS.StrongEps.StepFacts.ofReal_mul_integral_le_lintegral hK
      (Work.FTS.StrongEps.EpsE4Thr.KgainBig_nonneg hρ ε M) hKK hF hF' hFF)).trans ?_
  rw [hfinal]

end Work.FTS.StrongEps.TenOfEight
