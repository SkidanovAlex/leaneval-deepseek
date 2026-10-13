import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainSlot.mslot_le_gain
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## Auxiliary facts about the routed kernel derivatives `KdK ρ ε a b`

The routed kernel derivative `KdK ρ ε a b = ∂₁^a ∂₂^b (Jker ρ ε)` is smooth and supported in the
closed ball of radius `ε` (it is a derivative of the rescaled admissible kernel `Jker ρ ε`);
hence `|KdK ρ ε a b|` is integrable against any function which is continuous on that ball.  This is
the integrability input of the weighted Cauchy–Schwarz core `StepFacts.srb_cs_core`. -/

/-- The routed kernel derivative `KdK ρ ε a b` vanishes outside the closed ball of radius `ε`. -/
private theorem KdK_eq_zero_of_notMem_ball {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ} (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    EpsE4Thr.KdK ρ ε a b p = 0 := by
  rw [EpsE4Thr.Kd_Jker_scale hρ ε a b p]
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  have hzero : EpsE4Thr.Kdr ρ a b (ε⁻¹ • p) = 0 := by
    by_contra hne
    have h1 := EpsE4Thr.Kdr_support hρ a b (ε⁻¹ • p) hne
    have hq1 : |(ε⁻¹ • p).1| ≤ 1 := by
      have : (ε⁻¹ • p).1 ^ 2 ≤ 1 := by linarith [sq_nonneg (ε⁻¹ • p).2]
      rwa [sq_le_one_iff_abs_le_one] at this
    have hq2 : |(ε⁻¹ • p).2| ≤ 1 := by
      have : (ε⁻¹ • p).2 ^ 2 ≤ 1 := by linarith [sq_nonneg (ε⁻¹ • p).1]
      rwa [sq_le_one_iff_abs_le_one] at this
    have hgt : 1 < max |(ε⁻¹ • p).1| |(ε⁻¹ • p).2| := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hε.le)]
      rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr hε.le)]
      have h1 : (1 : ℝ) = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      rw [h1]
      exact mul_lt_mul_of_pos_left hmax (by positivity)
    linarith [max_le hq1 hq2]
  rw [show Jker (EpsE4Thr.Kdr ρ a b) ε p = 0 from by
    simp only [Jker, hzero, mul_zero], mul_zero]

/-- `|KdK ρ ε a b|` is integrable against any function continuous on the ball of radius `ε`. -/
private theorem integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (a b : ℕ) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p| * B p) := by
  have hcont : Continuous (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p|) :=
    (EpsE4Thr.KdK_continuous hρ ε a b).abs
  have hon : IntegrableOn (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (hcont.continuousOn.mul hB).integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_ball hρ hε a b hp, abs_zero, zero_mul]

/-! ## The routed slot bound in `ℝ`

The routed identity of `Work.FTS.StrongEps.mixed_Jeps_kernel_partial` (all `j` `z`-derivatives and
all `i` `θ`-derivatives moved onto the kernel) writes the slot `mixed j i (J_ε f) z θ` as
`2^i ∫ p, KdK ρ ε j i p · f(zShift, thShift)`; the weighted Cauchy–Schwarz core
`StepFacts.srb_cs_core` then gives the real inequality which the `ℝ≥0∞`-conversion of the target
statement turns into the claimed `lintegral` bound. -/

private lemma mjeps_core {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε α c : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) (j i : ℕ) :
    (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * epsW α z θ) ^ 2
      ≤ ((4 : ℝ) ^ i * ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε j i p|)
        * ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε j i p| * Real.exp (2 * c * (|p.1| + |p.2|))
            * (f (zShift z p.1) (thShift θ p.2)
                * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2 := by
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hself : epsW α z θ = Work.Spaces.Wt α z θ := epsW_eq_Wt_of_mem_Iθ hθIθ
  have hsh : ∀ p : ℝ × ℝ, epsW α (zShift z p.1) (thShift θ p.2)
      = Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := fun p =>
    epsW_eq_Wt_of_mem_Iθ ⟨(thShift_mem hθ).1.le, (thShift_mem hθ).2.le⟩
  have hW₀ : 0 ≤ epsW α z θ := by
    rw [hself]
    exact StepFacts.srb_Wt_nonneg α hz hθ
  have hWeps : ∀ p : ℝ × ℝ, epsW α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * epsW α (zShift z p.1) (thShift θ p.2) := by
    intro p
    rw [hself, hsh p]
    exact hW p
  have hGcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) := by
    have h := HkSqAux.continuousOn_shift_ball hz hθ
      (HkSqAux.continuousOn_mixed_region hz hε hθ hf 0 0)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  have hWcont : ContinuousOn (fun p : ℝ × ℝ => epsW α (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) := by
    have hWc : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (HkSqAux.continuousOn_Wt_region (α := α) hz hε hθ)
    exact hWc.congr (fun p _ => hsh p)
  have hKint : Integrable (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε j i p|) := by
    simpa only [mul_one] using
      integrable_abs_KdK_mul hρ hε j i (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
  have hQint : Integrable (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε j i p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
    have hB : ContinuousOn (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))
        * (f (zShift z p.1) (thShift θ p.2)
            * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2)
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      (StepFacts.srb_continuous_exp_two c).continuousOn.mul ((hGcont.mul hWcont).pow 2)
    simpa only [mul_assoc] using integrable_abs_KdK_mul hρ hε j i hB
  have hK2int : Integrable (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε j i p|
      * (f (zShift z p.1) (thShift θ p.2) * epsW α z θ) ^ 2) :=
    integrable_abs_KdK_mul hρ hε j i ((hGcont.mul continuousOn_const).pow 2)
  have hroute : Work.Spaces.mixed j i (Jeps ρ ε f) z θ
      = (2 : ℝ) ^ i * ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
          * f (zShift z p.1) (thShift θ p.2) := by
    have hKd : ∀ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
        = iteratedDeriv j (fun s : ℝ => iteratedDeriv i
            (fun t : ℝ => Jker ρ ε (s, t)) p.2) p.1 :=
      fun p => congrFun (Kd_eq (Jker ρ ε) j i) p
    have h := mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ j i 0 0
      (Nat.zero_le j) (Nat.zero_le i)
    simp only [Nat.sub_zero, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] at h
    rw [h]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun p => by simp only [hKd p])
  have hcs := StepFacts.srb_cs_core
    (K := fun p : ℝ × ℝ => EpsE4Thr.KdK ρ ε j i p)
    (G := fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
    (W := fun p : ℝ × ℝ => epsW α (zShift z p.1) (thShift θ p.2))
    (W₀ := epsW α z θ) (c := c)
    (M := ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
      * f (zShift z p.1) (thShift θ p.2))
    hW₀ hWeps hKint hQint hK2int rfl
  have h4 : ((2 : ℝ) ^ i) ^ 2 = (4 : ℝ) ^ i := by
    rw [pow_two, ← pow_add, show i + i = 2 * i from by ring, pow_mul]
    norm_num
  have hroute' : (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * epsW α z θ) ^ 2
      = (((2 : ℝ) ^ i * ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
            * f (zShift z p.1) (thShift θ p.2)) * epsW α z θ) ^ 2 := by
    rw [hroute]
  rw [hroute']
  calc (((2 : ℝ) ^ i * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
            * f (zShift z p.1) (thShift θ p.2))) * epsW α z θ) ^ 2
      = ((2 : ℝ) ^ i) ^ 2 * (((∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
            * f (zShift z p.1) (thShift θ p.2))) * epsW α z θ) ^ 2 := by ring
    _ = (4 : ℝ) ^ i * (((∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε j i p
            * f (zShift z p.1) (thShift θ p.2))) * epsW α z θ) ^ 2 := by rw [h4]
    _ ≤ (4 : ℝ) ^ i * ((∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε j i p|)
          * ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε j i p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (f (zShift z p.1) (thShift θ p.2)
                  * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = ((4 : ℝ) ^ i * ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε j i p|)
          * ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε j i p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (f (zShift z p.1) (thShift θ p.2)
                  * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2 := by ring

theorem MixedJepsEpsWpt (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ {ε α c : ℝ}, 0 < ε → ∀ {f : ℝ → ℝ → ℝ},
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
      ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      (∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) →
      ∀ j i : ℕ,
      ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ ENNReal.ofReal (4 ^ i * ∫ p : ℝ × ℝ,
              |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|)
          * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|
                * Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
  intro ε α c hε f hf z θ hz hθ hW j i
  have hcore := mjeps_core (ρ := ρ) (ε := ε) (α := α) (c := c) (f := f) (z := z) (θ := θ)
    hρ hε hf hz hθ hW j i
  have hK'nn : 0 ≤ (4 : ℝ) ^ i * ∫ p : ℝ × ℝ,
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| :=
    mul_nonneg (by positivity) (integral_nonneg fun p => abs_nonneg _)
  have hFnn : ∀ p : ℝ × ℝ, 0 ≤ |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
          * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  refine (ENNReal.ofReal_le_ofReal hcore).trans ?_
  rw [ENNReal.ofReal_mul hK'nn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (StepFacts.ofReal_integral_le_lintegral_ofReal hFnn).trans (le_of_eq ?_)
  exact lintegral_congr fun p =>
    ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)

end

end Work.FTS.StrongEps.EpsSqTools
