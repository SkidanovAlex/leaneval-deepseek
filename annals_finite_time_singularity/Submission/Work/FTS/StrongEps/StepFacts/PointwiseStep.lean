/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/PointwiseStep.lean`

The **pointwise one-order smoothing step** for the log-coordinate mollifier `J_ε`: at every point
of the open quadrant, the level-`m` integrand of `J_ε u` is dominated by `ε⁻¹`-priced averages of
the level-`m-1` integrand of `u`.

The estimate is assembled from

* `Chain.ofReal_GJ_le` at level `m-1` for the slots of order `≤ m-1` of `J_ε u` (they are
  literally the slots of `HkIntegrand α (m-1) (J_ε u)`, and the mollifier is `L²`-bounded with the
  probability kernel `Jker ρ ε`, no price);
* `TopSq` (`HkIntegrand α m f ≤ HkIntegrand α (m-1) f + TopSq α m f`) for the leftover slots of
  order exactly `m`;
* the *routed* slot bounds `slot_route_bounds` — obtained from the integration-by-parts identities
  `mixed_Jeps_route_z` and `DthIter_Jeps_route_theta` — for the top slots, where one derivative
  is moved onto the kernel `Jker ρ ε`;
* the domination `|∂_i Jker ρ ε| ≤ Ψ`, `Jker ρ ε ≤ Ψ` of the routed densities by the single
  rescaled kernel `Ψ = Jker (ε⁻¹ ρ̃) ε` (`KernelFacts`);
* the `ℝ≥0∞`-bookkeeping converting the real slot bounds into `lintegral` bounds (no integrability
  side conditions).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.HkSqAux.slot_sq_bound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools
import Submission.Work.FTS.StrongEps.StepFacts.TopSq
import Submission.Work.FTS.StrongEps.StepFacts.KernelFacts
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

variable {ρ : ℝ × ℝ → ℝ} {ε α c z θ : ℝ} {m : ℕ} {u : ℝ → ℝ → ℝ}

/-- The constant multiplying `ε⁻¹` in the pointwise step: `B = 200 Dm`. -/
def Bconst (ρ : ℝ × ℝ → ℝ) : ℝ := 200 * Dm ρ

theorem Bconst_pos (ρ : ℝ × ℝ → ℝ) : 0 < Bconst ρ := by
  have h1 : (1 : ℝ) ≤ Dm ρ := le_max_left _ _
  rw [Bconst]
  linarith

theorem Mmax_nonneg (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : 0 ≤ Mmax ρ ε :=
  le_trans zero_le_one (le_max_left _ _)

theorem one_le_ofReal_Mmax (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Mmax ρ ε) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- The reference `lintegral` of the pointwise step: the density `Ψ` against the shift gain and
the level-`m-1` integrand of `u` at the shifted point. -/
def Jint (ρ : ℝ × ℝ → ℝ) (ε α c : ℝ) (u : ℝ → ℝ → ℝ) (m : ℕ) (z θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
    * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
    * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))

theorem Psi_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    0 ≤ Psi ρ ε p :=
  mul_nonneg (inv_nonneg.mpr hε.le)
    (Jker_nonneg_of_nonneg (rhoTilde_nonneg ρ hρ.moll.nonneg) ε p)

/-- The shift gain is nonnegative. -/
theorem exp_nonneg (c : ℝ) (p : ℝ × ℝ) : 0 ≤ Real.exp (2 * c * (|p.1| + |p.2|)) :=
  (Real.exp_pos _).le

/-! ## The generic `ofReal`-conversion for a real slot bound -/

/-- **The conversion of a real slot bound into an `ℝ≥0∞` bound.**  If `a ≤ K ∫ F` with `K, F`
nonnegative and `K ≤ K'`, `F ≤ F'` pointwise, then `ofReal a ≤ ofReal K' * ∫⁻ ofReal F'`. -/
theorem ofReal_mul_integral_le_lintegral {K K' : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hKK : K ≤ K') {F F' : ℝ × ℝ → ℝ} (hF : ∀ p, 0 ≤ F p) (hF' : ∀ p, 0 ≤ F' p)
    (hFF : ∀ p, F p ≤ F' p) :
    ENNReal.ofReal (K * ∫ p : ℝ × ℝ, F p) ≤ ENNReal.ofReal K' * ∫⁻ p, ENNReal.ofReal (F' p) := by
  have hmid : ENNReal.ofReal (∫ p : ℝ × ℝ, F p) ≤ ∫⁻ p, ENNReal.ofReal (F' p) :=
    (ofReal_integral_le_lintegral_ofReal hF).trans
      (lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hFF p))
  calc ENNReal.ofReal (K * ∫ p : ℝ × ℝ, F p)
      = ENNReal.ofReal K * ENNReal.ofReal (∫ p : ℝ × ℝ, F p) := ENNReal.ofReal_mul hK
    _ ≤ ENNReal.ofReal K * ∫⁻ p, ENNReal.ofReal (F' p) :=
        mul_le_mul_right hmid _
    _ ≤ ENNReal.ofReal K' * ∫⁻ p, ENNReal.ofReal (F' p) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hKK) _

/-- The `lintegral` of `ofReal` of the product `Ψ · e^{2c|p|} · G` is `Jint`. -/
theorem lintegral_prod_eq_Jint (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c : ℝ}
    (hε0 : 0 < ε) {u : ℝ → ℝ → ℝ} {m : ℕ} {z θ : ℝ} :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
        * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)))
      ≤ Jint ρ ε α c u m z θ := by
  rw [Jint]
  refine lintegral_mono fun p => ?_
  have hP : 0 ≤ Psi ρ ε p := Psi_nonneg ρ hρ hε0 p
  have he : 0 ≤ Real.exp (2 * c * (|p.1| + |p.2|)) := (Real.exp_pos _).le
  have hG : 0 ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
      (Work.FTS.StrongEps.thShift θ p.2) := Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _
  rw [ENNReal.ofReal_mul (mul_nonneg hP he), ENNReal.ofReal_mul hP]


end Work.FTS.StrongEps.StepFacts
