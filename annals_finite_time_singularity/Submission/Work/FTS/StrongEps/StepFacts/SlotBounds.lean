/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/SlotBounds.lean`

The three **routed top slots** of the one-order smoothing estimate: each slot of order exactly `m`
of `J_ε u` is bounded, in the shape `ofReal (slot) ≤ ofReal Mmax * Jint`, by the routed
integration-by-parts identities of `mixed_Jeps_route_z` / `DthIter_Jeps_route_theta` combined
with the pointwise slot bounds `slot_route_bounds`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools
import Submission.Work.FTS.StrongEps.StepFacts.TopSq
import Submission.Work.FTS.StrongEps.StepFacts.KernelFacts
import Submission.Work.FTS.StrongEps.StepFacts.PointwiseStep
import Submission.Work.FTS.StrongEps.StepFacts.mixed_Jeps_route_z
import Submission.Work.FTS.StrongEps.StepFacts.DthIter_Jeps_route_theta
import Submission.Work.FTS.StrongEps.StepFacts.slot_route_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The `z`-routed mixed top slot (`1 ≤ j`, `1 ≤ i`, `i + j = m`). -/
theorem slot_z_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i) (hij : i + j = m) :
    ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
  have hroute := mixed_Jeps_route_z ρ hρ hε hu hz hθ j i hj
  have hslot := (slot_route_bounds ρ hρ hε hu).1 hz hθ hj hi hroute hW
  have hK : (0 : ℝ) ≤ ∫ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1| :=
    integral_nonneg fun p => abs_nonneg _
  have hKK : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
      ≤ Mmax ρ ε := by
    have h1 : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
        = M1 ρ ε := by
      rw [M1]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall fun p => (K1_eq_abs_deriv ρ hρ hε p).symm)
    rw [h1]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hF : ∀ p : ℝ × ℝ, 0 ≤
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
      (Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _)
  have hFF : ∀ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
        ≤ Psi ρ ε p :=
      (K1_eq_abs_deriv ρ hρ hε p).ge.trans (K1_le_Psi ρ hρ.moll.nonneg hε p)
    have h2 : (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (m - 1) u _ _ i (j - 1) hi (by omega)
    calc |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed (j - 1) i u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (ofReal_mul_integral_le_lintegral hK (Mmax_nonneg ρ ε) hKK hF hF' hFF)).trans ?_
  exact mul_le_mul_right (lintegral_prod_eq_Jint ρ hρ hε) _

/-- The pure `D_z^m`-slot (the `i = 0` case of the top `z`-slot). -/
theorem zslot_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                ^ (Work.Spaces.eta / 2))) :
    ENNReal.ofReal ((Work.Spaces.DzIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
  have hcomm : Work.Spaces.DzIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
      = ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    have h := mixed_Jeps_route_z ρ hρ hε hu hz hθ m 0 (by omega)
    simpa only [Work.Spaces.mixed_zero_right] using h
  have hslot := (slot_route_bounds ρ hρ hε hu).2.1 hz hθ (j := m) (by omega) hcomm hW
  have hK : (0 : ℝ) ≤ ∫ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1| :=
    integral_nonneg fun p => abs_nonneg _
  have hKK : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
      ≤ Mmax ρ ε := by
    have h1 : (∫ p : ℝ × ℝ, |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
        = M1 ρ ε := by
      rw [M1]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall fun p => (K1_eq_abs_deriv ρ hρ hε p).symm)
    rw [h1]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hF : ∀ p : ℝ × ℝ, 0 ≤
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
              ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
      (Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _)
  have hFF : ∀ p : ℝ × ℝ,
      |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
              ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
        ≤ Psi ρ ε p :=
      (K1_eq_abs_deriv ρ hρ hε p).ge.trans (K1_le_Psi ρ hρ.moll.nonneg hε p)
    have h2 : (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
              ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_z α (m - 1) u _ _ (m - 1) le_rfl
    calc |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (ofReal_mul_integral_le_lintegral hK (Mmax_nonneg ρ ε) hKK hF hF' hFF)).trans ?_
  exact mul_le_mul_right (lintegral_prod_eq_Jint ρ hρ hε) _

/-- The `θ`-routed top slot `D_θ^m` (`m ≥ 2`). -/
theorem slot_theta_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c z θ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {m : ℕ} (hm : 2 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    ENNReal.ofReal ((Work.Spaces.DthIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Mmax ρ ε) * Jint ρ ε α c u m z θ := by
  have hcomm : Work.Spaces.DthIter m (Work.FTS.StrongEps.Jeps ρ ε u) z θ
      = 2 * ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2
          * Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
    DthIter_Jeps_route_theta ρ hρ hε hu hz hθ m (by omega)
  have hslot := (slot_route_bounds ρ hρ hε hu).2.2 hz hθ (i := m) (by omega) hcomm hW
  have hK0 : 0 ≤ (∫ p : ℝ × ℝ,
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|) :=
    integral_nonneg fun p => abs_nonneg _
  have hK : (0 : ℝ) ≤ 4 * (∫ p : ℝ × ℝ,
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|) := by
    linarith
  have hKK : 4 * (∫ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|)
      ≤ Mmax ρ ε := by
    have h1 : (∫ p : ℝ × ℝ, |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|)
        = M2 ρ ε := by
      rw [M2]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall fun p => (K2_eq_abs_deriv ρ hρ hε p).symm)
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hF : ∀ p : ℝ × ℝ, 0 ≤
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF' : ∀ p : ℝ × ℝ, 0 ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
      (Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _)
  have hFF : ∀ p : ℝ × ℝ,
      |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
      * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
        ≤ Psi ρ ε p :=
      (K2_eq_abs_deriv ρ hρ hε p).ge.trans (K2_le_Psi ρ hρ.moll.nonneg hε p)
    have h2 : (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α (m - 1) u
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        (m - 1) 0 (by omega) (le_refl (m - 1))
      simpa only [Work.Spaces.mixed_zero_left] using h
    calc |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DthIter (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (sq_nonneg _)
      _ ≤ Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)
  refine ((ENNReal.ofReal_le_ofReal hslot).trans
    (ofReal_mul_integral_le_lintegral hK (Mmax_nonneg ρ ε) hKK hF hF' hFF)).trans ?_
  exact mul_le_mul_right (lintegral_prod_eq_Jint ρ hρ hε) _

end Work.FTS.StrongEps.StepFacts
