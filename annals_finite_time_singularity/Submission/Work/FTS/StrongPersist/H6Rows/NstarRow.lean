import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.MixedJepsEpsWpt =====
section

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
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NstarRow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `N_*`-row

`Construction.Nstar μ lam g = -μg - (μ+λ+μλ)·D_zg`, and the paper's `λ = lamfun μ` makes
`μ+λ+μλ = -μ`, so `N_* = μ(D_zg - g)`.  Its pairing against `g` is bounded by
`(|μ| + |μ+λ+μλ|)` times the two self-pairings; the `D_z`-self-pairing is the *proved*
`H6Pair6Aux.ip6_dz_self` (the lossless radial IBP), the other is Cauchy–Schwarz. -/

/-- **The `N_*`-row**: `|IP6 α (N_star μ λ f) f| ≤ C·(|μ| + |μ+λ+μλ|)·|f|²_{ℋ⁶}`.  No elliptic
data enters: only `HkMem α 7 f` (needed by the `D_z`-self-pairing, which must integrate by parts
across the order-seven slots) and the two bonding lemmas. -/
theorem nstar_pair_le : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (μ lam : ℝ) (f : Fn),
      Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      |IP6 1 1 1 1 1 1 1 1 1 1 α
          (fun z θ => -μ * f z θ - (μ + lam + μ * lam) * Work.Spaces.Dz f z θ) f|
        ≤ C * (|μ| + |μ + lam + μ * lam|) * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Cd, αd, hCd0, hαd0, hdz_self⟩ := H6Pair6Aux.ip6_dz_self
  obtain ⟨CC, hCC0, hCS⟩ := IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 1 one_pos
  refine ⟨max Cd CC, min αd 1, lt_of_lt_of_le hCd0 (le_max_left Cd CC),
    lt_min hαd0 one_pos, ?_⟩
  intro α hα μ lam f hf h7
  have hα0 : 0 < α := hα.1
  have hαd : α ∈ Set.Ioc 0 αd := ⟨hα0, le_trans hα.2 (min_le_left _ _)⟩
  have hα1 : α ∈ Set.Ioc 0 1 := ⟨hα0, le_trans hα.2 (min_le_right _ _)⟩
  have h6 : Work.Spaces.HkMem α 6 f := hf.2
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -μ * f z θ) :=
    smoothOpen_const_mul' (-μ) hsmf
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(μ + lam + μ * lam) * Work.Spaces.Dz f z θ) :=
    smoothOpen_const_mul' (-(μ + lam + μ * lam)) hsmf.Dz
  have hm1 : Work.Spaces.HkMem α 6 (fun z θ => -μ * f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-μ) h6
  have hm2 : Work.Spaces.HkMem α 6 (fun z θ => -(μ + lam + μ * lam) * Work.Spaces.Dz f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-(μ + lam + μ * lam))
      (Work.FTS.IPGen.HkMem_Dz_le hsmf h7)
  have hcongr : (fun z θ => -μ * f z θ - (μ + lam + μ * lam) * Work.Spaces.Dz f z θ)
      = fun z θ => (-μ * f z θ) + (-(μ + lam + μ * lam) * Work.Spaces.Dz f z θ) := by
    funext z θ
    ring
  rw [hcongr]
  rw [IP6_add 1 1 1 1 1 1 1 1 1 1 α hα0 hsm1 hsm2 hsmf hm1 hm2 h6]
  rw [IP6_smul 1 1 1 1 1 1 1 1 1 1 α (-μ) f f,
    IP6_smul 1 1 1 1 1 1 1 1 1 1 α (-(μ + lam + μ * lam)) (Work.Spaces.Dz f) f]
  have hA1 : |IP6 1 1 1 1 1 1 1 1 1 1 α f f| ≤ CC * Work.Spaces.HkSq α 6 f := by
    have h := hCS α hα1 f f hf hf
    have hs : Xn6 α f * Xn6 α f = Work.Spaces.HkSq α 6 f := by
      rw [← sq, Work.FTS.StrongPersist.Xn6_sq]
    calc |IP6 1 1 1 1 1 1 1 1 1 1 α f f| ≤ CC * Xn6 α f * Xn6 α f := h
      _ = CC * (Xn6 α f * Xn6 α f) := by ring
      _ = CC * Work.Spaces.HkSq α 6 f := by rw [hs]
  have hA2 : |IP6 1 1 1 1 1 1 1 1 1 1 α (Work.Spaces.Dz f) f|
      ≤ Cd * Work.Spaces.HkSq α 6 f := hdz_self α hαd f hf h7
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  set A1 := IP6 1 1 1 1 1 1 1 1 1 1 α f f with hA1def
  set A2 := IP6 1 1 1 1 1 1 1 1 1 1 α (Work.Spaces.Dz f) f with hA2def
  have h1 : |(-μ) * A1| ≤ |μ| * (CC * Work.Spaces.HkSq α 6 f) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hA1 (abs_nonneg μ)
  have h2 : |(-(μ + lam + μ * lam)) * A2| ≤ |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hA2 (abs_nonneg _)
  have h3 : |(-μ) * A1 + (-(μ + lam + μ * lam)) * A2|
      ≤ |μ| * (CC * Work.Spaces.HkSq α 6 f)
        + |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f) :=
    le_trans (abs_add_le _ _) (add_le_add h1 h2)
  have hCdSq : 0 ≤ Cd * Work.Spaces.HkSq α 6 f := mul_nonneg hCd0.le hSq0
  have hCCSq : 0 ≤ CC * Work.Spaces.HkSq α 6 f := mul_nonneg hCC0.le hSq0
  have h4 : |μ| * (CC * Work.Spaces.HkSq α 6 f)
      + |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f)
      ≤ max Cd CC * (|μ| + |μ + lam + μ * lam|) * Work.Spaces.HkSq α 6 f := by
    have ha : CC ≤ max Cd CC := le_max_right _ _
    have hb : Cd ≤ max Cd CC := le_max_left _ _
    have h5 : |μ| * (CC * Work.Spaces.HkSq α 6 f) ≤ |μ| * (max Cd CC * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hSq0) (abs_nonneg μ)
    have h6' : |μ + lam + μ * lam| * (Cd * Work.Spaces.HkSq α 6 f)
        ≤ |μ + lam + μ * lam| * (max Cd CC * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hSq0) (abs_nonneg _)
    have hsum : |μ| * (max Cd CC * Work.Spaces.HkSq α 6 f)
        + |μ + lam + μ * lam| * (max Cd CC * Work.Spaces.HkSq α 6 f)
        = max Cd CC * (|μ| + |μ + lam + μ * lam|) * Work.Spaces.HkSq α 6 f := by ring
    linarith [h5, h6', hsum.le, hsum.ge]
  simpa only [hA1def, hA2def] using le_trans h3 h4



end Work.FTS.StrongPersist
end
end
