import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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

/-! ## The vanishing of the angular cut-off derivative term -/

/-- The window mass `∫_θ 1_{win ε}(θ)·σ(θ)·V(z,θ)²`. -/
def Wmass (u : ℝ → ℝ → ℝ) (ε z : ℝ) : ℝ :=
  ∫ θ in Iθo, (win ε).indicator (fun θ => sigE θ * (V u z θ) ^ 2) θ

theorem measurableSet_win (ε : ℝ) : MeasurableSet (win ε) :=
  measurableSet_Icc.union measurableSet_Icc

/-- Restricting an `IntegrableOn` statement to a smaller set. -/
theorem integrableOn_mono {f : ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn f t) (hst : s ⊆ t) :
    MeasureTheory.IntegrableOn f s :=
  MeasureTheory.IntegrableOn.mono_set (s := s) (t := t) h hst

/-- `σ(θ)·f² ≥ 0` on the open angular interval. -/
theorem sigE_mul_sq_nonneg {θ : ℝ} (hθ : θ ∈ Iθo) (f : ℝ) :
    0 ≤ sigE θ * f ^ 2 :=
  mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg f)

theorem Wmass_nonneg (u : ℝ → ℝ → ℝ) (ε z : ℝ) : 0 ≤ Wmass u ε z := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => ?_)
  by_cases h : θ ∈ win ε
  · rw [Set.indicator_of_mem h]
    exact sigE_mul_sq_nonneg hθ _
  · rw [Set.indicator_of_notMem h]

theorem Wmass_le_Vsl {u : ℝ → ℝ → ℝ} {ε z : ℝ}
    (hV : MeasureTheory.IntegrableOn (fun θ => sigE θ * (V u z θ) ^ 2) Iθo) :
    Wmass u ε z ≤ ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2 := by
  have hI : MeasureTheory.IntegrableOn
      ((win ε).indicator (fun θ => sigE θ * (V u z θ) ^ 2)) Iθo := by
    refine MeasureTheory.Integrable.mono' hV (hV.1.indicator (measurableSet_win ε)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hg : 0 ≤ sigE θ * (V u z θ) ^ 2 := sigE_mul_sq_nonneg hθ _
    by_cases h : θ ∈ win ε
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg hg]
    · rw [Set.indicator_of_notMem h]
      show ‖(0 : ℝ)‖ ≤ sigE θ * (V u z θ) ^ 2
      rw [norm_zero]
      exact sigE_mul_sq_nonneg hθ _
  have hle : ∀ θ ∈ Iθo, (win ε).indicator (fun θ => sigE θ * (V u z θ) ^ 2) θ
      ≤ sigE θ * (V u z θ) ^ 2 := by
    intro θ hθ
    by_cases h : θ ∈ win ε
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact sigE_mul_sq_nonneg hθ _
  exact MeasureTheory.setIntegral_mono_on hI hV measurableSet_Ioo hle

theorem Wmass_tendsto_zero {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hV : MeasureTheory.IntegrableOn (fun θ => sigE θ * (V u z θ) ^ 2) Iθo) :
    Filter.Tendsto (fun ε : ℝ => Wmass u ε z) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθo),
      Filter.Tendsto (fun ε : ℝ => (win ε).indicator (fun θ => sigE θ * (V u z θ) ^ 2) θ)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hmem : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), θ ∉ win ε := by
      have h1 : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), ε < min θ (Real.pi / 2 - θ) :=
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds
          (lt_min hθ.1 (by linarith [hθ.2, Real.pi_pos])))
      filter_upwards [h1] with ε hε hmem
      rcases hmem with h | h
      · linarith [h.2, lt_of_lt_of_le hε (min_le_left θ (Real.pi / 2 - θ))]
      · linarith [h.1, lt_of_lt_of_le hε (min_le_right θ (Real.pi / 2 - θ))]
    exact Filter.Tendsto.congr' (hmem.mono fun ε hε => (Set.indicator_of_notMem hε _).symm)
      tendsto_const_nhds
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Iθo) (l := nhdsWithin 0 (Set.Ioi (0 : ℝ)))
    (F := fun ε θ => (win ε).indicator (fun θ => sigE θ * (V u z θ) ^ 2) θ)
    (f := fun _ => (0 : ℝ)) (bound := fun θ => ‖sigE θ * (V u z θ) ^ 2‖)
    (Filter.Eventually.of_forall fun ε => hV.1.indicator (measurableSet_win ε))
    (Filter.Eventually.of_forall fun ε => by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      by_cases h : θ ∈ win ε
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]
        show ‖(0 : ℝ)‖ ≤ ‖sigE θ * (V u z θ) ^ 2‖
        rw [norm_zero]
        exact norm_nonneg _)
    hV.norm hlim
  simpa only [Wmass, MeasureTheory.integral_zero] using hmain

/-- `σ` is continuous on the open angular interval. -/
theorem sigE_continuousOn_Iθo : ContinuousOn sigE Iθo := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine (hsin.rpow_const (p := -(Work.Spaces.eta)) ?_).congr (fun θ _ => rfl)
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

/-- On its transition window, the derivative of the angular cut-off is dominated by
`(M/ε)·1_{win ε}`. -/
theorem abs_deriv_le_window {ε M θ : ℝ} (hε : 0 < ε)
    (hM : ∀ θ : ℝ, |deriv (ψ ε) θ| ≤ M / ε) :
    |deriv (ψ ε) θ| ≤ (M / ε) * (win ε).indicator (fun _ => (1 : ℝ)) θ := by
  by_cases h : θ ∈ win ε
  · rw [Set.indicator_of_mem h, mul_one]; exact hM θ
  · rw [Set.indicator_of_notMem h, mul_zero, deriv_cut_eq_zero_of_notMem_win hε h, abs_zero]

/-- `(b·√a·c)² = b²·(a·c²)`. -/
theorem sq_mul_sqrt {b c a : ℝ} (ha : 0 ≤ a) :
    (b * Real.sqrt a * c) ^ 2 = b ^ 2 * (a * c ^ 2) := by
  calc (b * Real.sqrt a * c) ^ 2 = b ^ 2 * (Real.sqrt a) ^ 2 * c ^ 2 := by ring
    _ = b ^ 2 * a * c ^ 2 := by rw [Real.sq_sqrt ha]
    _ = b ^ 2 * (a * c ^ 2) := by ring

/-- `(√a·c)² = a·c²`. -/
theorem sq_sqrt_mul {c a : ℝ} (ha : 0 ≤ a) :
    (Real.sqrt a * c) ^ 2 = a * c ^ 2 := by
  calc (Real.sqrt a * c) ^ 2 = (Real.sqrt a) ^ 2 * c ^ 2 := by ring
    _ = a * c ^ 2 := by rw [Real.sq_sqrt ha]

end Work.FTS.EllipticEst.I1Ae
