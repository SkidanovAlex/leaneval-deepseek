import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits
import Submission.Work.FTS.EllipticEst.I1Ae.RIFCollar
import Submission.Work.FTS.EllipticEst.I1Ae.RIFPsi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

/-- **The collar bound.**  The `θ`-integral of the cut-off derivative term is bounded by the
`U`-energy and the `V`-energy *restricted to the transition window* of `ψ ε`. -/
private theorem psideriv_bound {u : ℝ → ℝ → ℝ} {M ε z : ℝ} (hMpos : 0 < M) (hε : 0 < ε)
    (hε8 : ε ≤ Real.pi / 8)
    (hM : ∀ θ : ℝ, |deriv (ψ ε) θ| ≤ M / ε)
    (hNint : MeasureTheory.IntegrableOn
      (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo)
    (hUint : MeasureTheory.IntegrableOn (fun θ => sigE θ * (U u z θ) ^ 2) Iθo)
    (hVint : MeasureTheory.IntegrableOn (fun θ => sigE θ * (V u z θ) ^ 2) Iθo)
    (hUc : ContinuousOn (fun θ => U u z θ) Iθo)
    (hVc : ContinuousOn (fun θ => V u z θ) Iθo) :
    |∫ θ in Iθo, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ)|
      ≤ 4 * M * Real.sqrt (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
          * Real.sqrt (Wmass u ε z) := by
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hεnn : 0 ≤ ε := le_of_lt hε
  have hsigc : ContinuousOn (fun θ : ℝ => Real.sqrt (sigE θ)) Iθo :=
    Real.continuous_sqrt.comp_continuousOn sigE_continuousOn_Iθo
  set W : Set ℝ := Iθo ∩ win ε with hW
  have hWsub : W ⊆ Iθo := fun θ hθ => hθ.1
  have hWmeas : MeasurableSet W := measurableSet_Ioo.inter (measurableSet_win ε)
  -- ## the integrand vanishes off the window
  have hgzero : ∀ θ : ℝ, θ ∉ win ε → sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ) = 0 := by
    intro θ hθ
    rw [deriv_cut_eq_zero_of_notMem_win hε hθ, mul_zero, zero_mul]
  -- ## the integral over `Iθo` is the integral over the window
  have hL : (∫ θ in Iθo, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ))
      = ∫ θ in W, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ) := by
    have h1 : (∫ θ in Iθo, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ))
        = ∫ θ in Iθo, (win ε).indicator
            (fun θ => sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ)) θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by
        by_cases hw : θ ∈ win ε
        · rw [Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem hw, hgzero θ hw])
    rw [h1, MeasureTheory.setIntegral_indicator (measurableSet_win ε), hW]
  -- ## the comparison functions
  set A : ℝ → ℝ := fun θ => (M / ε) * Real.sqrt (sigE θ) * |U u z θ| with hA
  set B : ℝ → ℝ := fun θ => Real.sqrt (sigE θ) * |V u z θ| with hB
  have hA2 : MeasureTheory.MemLp A 2 (MeasureTheory.volume.restrict W) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact (((hsigc.const_mul (M / ε)).mul hUc.abs).mono hWsub).aestronglyMeasurable hWmeas
    · have h : MeasureTheory.IntegrableOn
          (fun θ => (M / ε) ^ 2 * (sigE θ * (U u z θ) ^ 2)) W :=
        integrableOn_mono (hUint.const_mul ((M / ε) ^ 2)) hWsub
      refine h.congr_fun (fun θ hθ => ?_) hWmeas
      rw [hA]
      have hs : 0 ≤ sigE θ := Work.FTS.EllipticEst.AeI1Fts.sigE_nonneg
        ⟨le_of_lt hθ.1.1, le_of_lt hθ.1.2⟩
      simp only []
      rw [sq_mul_sqrt hs, sq_abs]
  have hB2 : MeasureTheory.MemLp B 2 (MeasureTheory.volume.restrict W) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact ((hsigc.mul hVc.abs).mono hWsub).aestronglyMeasurable hWmeas
    · have h : MeasureTheory.IntegrableOn (fun θ => sigE θ * (V u z θ) ^ 2) W :=
        integrableOn_mono hVint hWsub
      refine h.congr_fun (fun θ hθ => ?_) hWmeas
      rw [hB]
      have hs : 0 ≤ sigE θ := Work.FTS.EllipticEst.AeI1Fts.sigE_nonneg
        ⟨le_of_lt hθ.1.1, le_of_lt hθ.1.2⟩
      simp only []
      rw [sq_sqrt_mul hs, sq_abs]
  have hA0 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict W), 0 ≤ A θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hWmeas] with θ hθ
    rw [hA]
    exact mul_nonneg (mul_nonneg (div_nonneg hMnn hεnn) (Real.sqrt_nonneg _)) (abs_nonneg _)
  have hB0 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict W), 0 ≤ B θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hWmeas] with θ hθ
    rw [hB]
    exact mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict W),
      |sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ)| ≤ A θ * B θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hWmeas] with θ hθ
    have hs : 0 ≤ sigE θ := Work.FTS.EllipticEst.AeI1Fts.sigE_nonneg
      ⟨le_of_lt hθ.1.1, le_of_lt hθ.1.2⟩
    have hss : Real.sqrt (sigE θ) * Real.sqrt (sigE θ) = sigE θ := Real.mul_self_sqrt hs
    rw [hA, hB]
    simp only []
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs]
    have hkey : sigE θ * |deriv (ψ ε) θ| * (|U u z θ| * |V u z θ|)
        ≤ sigE θ * (M / ε) * (|U u z θ| * |V u z θ|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM θ) hs)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc sigE θ * |deriv (ψ ε) θ| * (|U u z θ| * |V u z θ|)
        ≤ sigE θ * (M / ε) * (|U u z θ| * |V u z θ|) := hkey
      _ = (M / ε) * (Real.sqrt (sigE θ) * Real.sqrt (sigE θ)) * (|U u z θ| * |V u z θ|) := by
          rw [hss]; ring
      _ = ((M / ε) * Real.sqrt (sigE θ) * |U u z θ|) * (Real.sqrt (sigE θ) * |V u z θ|) := by
          ring
  have hCS := Work.FTS.H2.CS1D hA2 hB2 hA0 hB0 (g := fun θ => sigE θ * deriv (ψ ε) θ
    * (U u z θ * V u z θ)) hpt
  -- ## the two `L²` norms
  have hAsq : (∫ θ in W, (A θ) ^ 2) = (M / ε) ^ 2 * (∫ θ in W, sigE θ * (U u z θ) ^ 2) := by
    have h1 : (∫ θ in W, (A θ) ^ 2) = ∫ θ in W, (M / ε) ^ 2 * (sigE θ * (U u z θ) ^ 2) := by
      rw [hA]
      refine MeasureTheory.setIntegral_congr_fun hWmeas (fun θ hθ => ?_)
      have hs : 0 ≤ sigE θ := Work.FTS.EllipticEst.AeI1Fts.sigE_nonneg
        ⟨le_of_lt hθ.1.1, le_of_lt hθ.1.2⟩
      simp only []
      rw [sq_mul_sqrt hs, sq_abs]
    rw [h1, MeasureTheory.integral_const_mul]
  have hBsq : (∫ θ in W, (B θ) ^ 2) = Wmass u ε z := by
    have h1 : (∫ θ in W, (B θ) ^ 2) = ∫ θ in W, sigE θ * (V u z θ) ^ 2 := by
      rw [hB]
      refine MeasureTheory.setIntegral_congr_fun hWmeas (fun θ hθ => ?_)
      have hs : 0 ≤ sigE θ := Work.FTS.EllipticEst.AeI1Fts.sigE_nonneg
        ⟨le_of_lt hθ.1.1, le_of_lt hθ.1.2⟩
      simp only []
      rw [sq_sqrt_mul hs, sq_abs]
    rw [h1, Wmass, hW]
    exact (MeasureTheory.setIntegral_indicator (measurableSet_win ε)
      (f := fun θ => sigE θ * (V u z θ) ^ 2) (s := Iθo)).symm
  -- ## the window bound for the `U`-energy
  have hUwin : (∫ θ in W, sigE θ * (U u z θ) ^ 2)
      ≤ 16 * ε ^ 2 * (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) := by
    have hle : ∀ θ ∈ W, sigE θ * (U u z θ) ^ 2
        ≤ 16 * ε ^ 2 * ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) := by
      intro θ hθ
      have h := sigE_mul_le_window hε hε8 hθ.2 (U u z θ)
      linarith [h]
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => 16 * ε ^ 2 * ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)) W :=
      integrableOn_mono (s := W) (t := Iθo) (hNint.const_mul (16 * ε ^ 2)) hWsub
    have h1 : (∫ θ in W, sigE θ * (U u z θ) ^ 2)
        ≤ ∫ θ in W, 16 * ε ^ 2 * ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) :=
      MeasureTheory.setIntegral_mono_on (integrableOn_mono hUint hWsub) hdom hWmeas hle
    have h2 : (∫ θ in W, 16 * ε ^ 2 * ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
        = 16 * ε ^ 2 * (∫ θ in W, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) :=
      MeasureTheory.integral_const_mul _ _
    have h3 : (∫ θ in W, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
        ≤ ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ :=
      MeasureTheory.setIntegral_mono_set hNint
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
          mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sig2_nonneg_of_mem
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)))
        (Filter.Eventually.of_forall (fun θ hθ => hWsub hθ))
    calc (∫ θ in W, sigE θ * (U u z θ) ^ 2)
        ≤ ∫ θ in W, 16 * ε ^ 2 * ((U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) := h1
      _ = 16 * ε ^ 2 * (∫ θ in W, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) := h2
      _ ≤ 16 * ε ^ 2 * (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  -- ## conclusion
  have hNnn : 0 ≤ ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sig2_nonneg_of_mem
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  have hstep : Real.sqrt (∫ θ in W, sigE θ * (U u z θ) ^ 2)
      ≤ 4 * ε * Real.sqrt (∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) := by
    have h4 : Real.sqrt ((4 * ε) ^ 2 * (∫ θ in Iθo,
          (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
        = 4 * ε * Real.sqrt (∫ θ in Iθo,
            (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [← h4]
    refine Real.sqrt_le_sqrt ?_
    have h16 : 16 * ε ^ 2 = (4 * ε) ^ 2 := by ring
    rw [← h16]
    exact hUwin
  rw [hAsq, hBsq] at hCS
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hCS
  rw [hL]
  calc |∫ θ in W, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ)|
      ≤ (M / ε) * Real.sqrt (∫ θ in W, sigE θ * (U u z θ) ^ 2)
          * Real.sqrt (Wmass u ε z) := hCS
    _ ≤ (M / ε) * (4 * ε * Real.sqrt (∫ θ in Iθo,
          (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)) * Real.sqrt (Wmass u ε z) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (by positivity))
          (Real.sqrt_nonneg _)
    _ = 4 * M * Real.sqrt (∫ θ in Iθo,
          (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) * Real.sqrt (Wmass u ε z) := by
        rw [show (M / ε) * (4 * ε * Real.sqrt (∫ θ in Iθo,
              (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ))
            = 4 * M * Real.sqrt (∫ θ in Iθo,
              (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) from by
          field_simp]

/-- The `σ`-weighted square of a slice, in the factor order used by the estimates. -/
theorem slice_integrable_sq' {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => sigE θ * (f z θ) ^ 2) Iθo :=
  (slice_integrable_sq hm hz).congr_fun (fun θ _ => by rw [mul_comm]) measurableSet_Ioo

/-- The `N`-energy slice `∫_θ U²cos²(2θ)σ₂` at fixed `z`. -/
def Nz (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ

/-- The `σ`-weighted `V`-energy slice at fixed `z`. -/
def Vsl (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2

/-- The cut-off derivative term at fixed `z`, `ε`. -/
def Seps (u : ℝ → ℝ → ℝ) (ε z : ℝ) : ℝ :=
  ∫ θ in Iθo, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ)

/-- **The cut-off derivative term vanishes as `ε → 0⁺`.**  With the radial cut-off `χ_n` frozen,
the integral of `σ·(ψ ε)'(θ)·U·V` tends to `0`: the derivative costs `1/ε` while the transition
window contributes only `ε` (because `σ ≤ 16ε²σ₂cos²(2θ)` there). -/
theorem psideriv_tendsto_zero {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u))
    (hV : Work.Spaces.HkMem α 0 (V u))
    (hNslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo)
    (hNfin : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
      (Set.Ioi (0 : ℝ)))
    (n : ℕ) :
    Filter.Tendsto (fun ε : ℝ => ∫ z in Set.Ioi (0 : ℝ),
        χ n z * (Work.Spaces.w z) ^ 2 * Seps u ε z)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  obtain ⟨M, hMpos, hM⟩ := exists_bound_deriv_cut
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- ## the slice facts, for a.e. `z`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
          (fun θ => (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) Iθo
        ∧ MeasureTheory.IntegrableOn (fun θ => sigE θ * (U u z θ) ^ 2) Iθo
        ∧ MeasureTheory.IntegrableOn (fun θ => sigE θ * (V u z θ) ^ 2) Iθo
        ∧ ContinuousOn (fun θ => U u z θ) Iθo
        ∧ ContinuousOn (fun θ => V u z θ) Iθo := by
    filter_upwards [hNslice, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hNs hz
    refine ⟨hNs, slice_integrable_sq' hU hz, slice_integrable_sq' hV hz, ?_, ?_⟩
    · exact ((AeI1Fts.smoothOpen_U hS).continuousOn).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => by
          rw [Work.FTS.EllipticEst.mem_Q0]
          exact ⟨hz, hθ.1, hθ.2⟩)
    · exact ((AeI1Fts.smoothOpen_V hS).continuousOn).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => by
          rw [Work.FTS.EllipticEst.mem_Q0]
          exact ⟨hz, hθ.1, hθ.2⟩)
  -- ## the dominator
  set Φ : ℝ → ℝ := fun z => 2 * M * ((Work.Spaces.w z) ^ 2 * Nz u z
      + (Work.Spaces.w z) ^ 2 * Vsl u z) with hΦ
  have hPhi : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Nz u z) (Set.Ioi (0 : ℝ)) :=
      hNfin.congr_fun (fun z _ => by rw [Nz]) measurableSet_Ioi
    have h2 : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Vsl u z) (Set.Ioi (0 : ℝ)) :=
      (integrable_w2_Vsl (α := α) (u := u) hV).congr_fun (fun z _ => by rw [Vsl])
        measurableSet_Ioi
    rw [hΦ]
    exact (h1.add h2).const_mul (2 * M)
  -- ## the pointwise bound
  have hbound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖χ n z * (Work.Spaces.w z) ^ 2 * Seps u ε z‖ ≤ Φ z := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds (show (0 : ℝ) < Real.pi / 8 by positivity))]
      with ε hε hε8
    filter_upwards [hae] with z hz
    obtain ⟨hNs, hUs, hVs, hUc, hVc⟩ := hz
    have hSeps : |Seps u ε z|
        ≤ 4 * M * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z) := by
      rw [Seps, Nz]
      exact psideriv_bound hMpos hε hε8.le (hM ε hε) hNs hUs hVs hUc hVc
    have hWle : Wmass u ε z ≤ Vsl u z := by
      rw [Vsl]; exact Wmass_le_Vsl hVs
    have hWnn : 0 ≤ Wmass u ε z := Wmass_nonneg u ε z
    have hNnn : 0 ≤ Nz u z := by
      rw [Nz]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sig2_nonneg_of_mem
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
    have hVnn : 0 ≤ Vsl u z := by
      rw [Vsl]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
        sigE_mul_sq_nonneg hθ _)
    have hchib : |χ n z| ≤ 1 := by
      rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)]
      exact Work.FTS.EllipticEst.cut_le_one n z
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw2]
    have hchib' : |χ n z| * (Work.Spaces.w z) ^ 2 ≤ (Work.Spaces.w z) ^ 2 := by
      calc |χ n z| * (Work.Spaces.w z) ^ 2 ≤ 1 * (Work.Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_right hchib hw2
        _ = (Work.Spaces.w z) ^ 2 := one_mul _
    have hstep : |χ n z| * (Work.Spaces.w z) ^ 2 * |Seps u ε z|
        ≤ (Work.Spaces.w z) ^ 2 * (4 * M * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z)) :=
      mul_le_mul hchib' hSeps (abs_nonneg _) hw2
    have hAM : 2 * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z) ≤ Nz u z + Wmass u ε z := by
      have h1 := two_mul_le_add_sq (Real.sqrt (Nz u z)) (Real.sqrt (Wmass u ε z))
      rwa [Real.sq_sqrt hNnn, Real.sq_sqrt hWnn] at h1
    calc |χ n z| * (Work.Spaces.w z) ^ 2 * |Seps u ε z|
        ≤ (Work.Spaces.w z) ^ 2 * (4 * M * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z)) :=
          hstep
      _ = 2 * M * ((Work.Spaces.w z) ^ 2
            * (2 * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z))) := by ring
      _ ≤ 2 * M * ((Work.Spaces.w z) ^ 2 * (Nz u z + Wmass u ε z)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAM hw2) (by positivity)
      _ ≤ 2 * M * ((Work.Spaces.w z) ^ 2 * Nz u z + (Work.Spaces.w z) ^ 2 * Vsl u z) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [hw2, hWle]
      _ = Φ z := by rw [hΦ]
  -- ## the convergence
  have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Filter.Tendsto (fun ε : ℝ => χ n z * (Work.Spaces.w z) ^ 2 * Seps u ε z)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
    filter_upwards [hae] with z hz
    obtain ⟨hNs, hUs, hVs, hUc, hVc⟩ := hz
    -- the bound is `w²·4M√Nz·√(Wmass)`, which tends to `0` with `Wmass`
    have hsq : Filter.Tendsto (fun ε : ℝ => Real.sqrt (Wmass u ε z))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
      have h0 := Wmass_tendsto_zero (u := u) (z := z) hVs
      have hcomp : Filter.Tendsto (fun ε : ℝ => Real.sqrt (Wmass u ε z))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (Real.sqrt 0)) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp h0
      simpa using hcomp
    have hup : Filter.Tendsto (fun ε : ℝ => |χ n z| * (Work.Spaces.w z) ^ 2
        * (4 * M * Real.sqrt (Nz u z)) * Real.sqrt (Wmass u ε z))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
      have := hsq.const_mul (|χ n z| * (Work.Spaces.w z) ^ 2 * (4 * M * Real.sqrt (Nz u z)))
      simpa only [mul_zero] using this
    -- squeeze
    have hbd : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ‖Seps u ε z‖ ≤ 4 * M * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
        (isOpen_Iio.mem_nhds (show (0 : ℝ) < Real.pi / 8 by positivity))]
        with ε hε hε8
      rw [Real.norm_eq_abs, Seps, Nz]
      exact psideriv_bound hMpos hε hε8.le (hM ε hε) hNs hUs hVs hUc hVc
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun ε : ℝ => |χ n z| * (Work.Spaces.w z) ^ 2
      * (4 * M * Real.sqrt (Nz u z)) * Real.sqrt (Wmass u ε z))
      (Filter.Eventually.of_forall (fun ε => norm_nonneg _)) ?_ ?_
    · filter_upwards [hbd, self_mem_nhdsWithin] with ε hb _
      rw [Real.norm_eq_abs]
      calc |χ n z * (Work.Spaces.w z) ^ 2 * Seps u ε z|
          = |χ n z| * (Work.Spaces.w z) ^ 2 * |Seps u ε z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
        _ ≤ |χ n z| * (Work.Spaces.w z) ^ 2
              * (4 * M * Real.sqrt (Nz u z) * Real.sqrt (Wmass u ε z)) :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (sq_nonneg _))
        _ = |χ n z| * (Work.Spaces.w z) ^ 2
              * (4 * M * Real.sqrt (Nz u z)) * Real.sqrt (Wmass u ε z) := by ring
    · exact hup
  -- ## dominated convergence
  have haesm : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), MeasureTheory.AEStronglyMeasurable
      (fun z => χ n z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => sigE p.2 * deriv (ψ ε) p.2 * (U u p.1 p.2 * V u p.1 p.2)) nuQ := by
      have hderiv : Continuous (fun θ : ℝ => deriv (ψ ε) θ) :=
        (SliceMixedAux.cut_contDiff ε).continuous_deriv (by norm_num)
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          sigE p.2 * deriv (ψ ε) p.2 * (U u p.1 p.2 * V u p.1 p.2))
          Work.FTS.EllipticEst.Q0 := by
        refine (((sigE_continuousOn_Iθo.comp continuous_snd.continuousOn (fun p hp =>
          (Work.FTS.EllipticEst.mem_Q0.mp hp).2))).mul
            ((hderiv.comp continuous_snd).continuousOn)).mul
          (((AeI1Fts.smoothOpen_U hS).continuousOn).mul
            ((AeI1Fts.smoothOpen_V hS).continuousOn))
      have h := Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hcont
      rw [nuFts_eq_nuQ] at h
      exact h
    have h1 := hjoint.integral_prod_right'
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => χ n z * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hχ : Measurable (fun z : ℝ => χ n z) :=
        (Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable
      have hw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
        have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
          funext z; rw [Work.Spaces.w]
        rw [hfun]
        fun_prop
      exact (hχ.mul hw).aestronglyMeasurable
    exact (h2.mul h1 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => χ n z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Iθo, sigE θ * deriv (ψ ε) θ * (U u z θ * V u z θ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (l := nhdsWithin 0 (Set.Ioi (0 : ℝ)))
    (F := fun (ε : ℝ) (z : ℝ) => χ n z * (Work.Spaces.w z) ^ 2 * Seps u ε z)
    (f := fun _ => (0 : ℝ)) Φ haesm hbound hPhi hlim
  simpa only [MeasureTheory.integral_zero, Seps] using hmain

end Work.FTS.EllipticEst.I1Ae
