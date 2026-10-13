/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted Cauchy–Schwarz inequality for the mollifier kernel `Jker`

`Work.FTS.StrongEps.sq_integral_Jker_mul_le` is the elementary estimate behind every
`L²`-boundedness statement of the `E1` chapter:

  `(∫ p, Jker ρ ε p * g p)² ≤ ∫ p, Jker ρ ε p * (g p)²`

for an admissible mollifier `ρ` (`IsMollKernel ρ`: continuous, supported in the unit ball,
nonnegative, total mass `1`), a positive scale `ε`, and `g` continuous on the closed ball of
radius `ε`.

Since `Jker ρ ε p = ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)` is a nonnegative function of total mass `1`, this is
the Cauchy–Schwarz (Jensen) inequality for the probability density `Jker ρ ε`.  It is proved
here in the completed–square form: for `m := ∫ p, Jker ρ ε p * g p` the integrand of

  `∫ p, Jker ρ ε p * (g p - m)²`

is nonnegative, and expanding the square gives `∫ p, Jker ρ ε p * (g p)² - m² ≥ 0`.  Finite
integrability of all the pieces is automatic because `Jker ρ ε` is supported in the compact ball
of radius `ε`, on which `g` is continuous.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false

/-! ## The abstract weighted Cauchy–Schwarz inequality -/

/-- **Cauchy–Schwarz (completed–square form) for a probability density.**  If `k` is a
nonnegative integrable function of total mass `1`, and `k A`, `k A²` are integrable, then
`(∫ k A)² ≤ ∫ k A²`.

The proof expands `∫ k (A - m)² ≥ 0` for `m := ∫ k A`. -/
theorem sq_integral_mul_le_of_prob {α : Type*} [MeasurableSpace α] {μ : Measure α} {k A : α → ℝ}
    (hk_nn : ∀ p, 0 ≤ k p) (hk_int : Integrable k μ)
    (hA_int : Integrable (fun p => k p * A p) μ)
    (hA2_int : Integrable (fun p => k p * (A p) ^ 2) μ)
    (hk_mass : ∫ p, k p ∂μ = 1) :
    (∫ p, k p * A p ∂μ) ^ 2 ≤ ∫ p, k p * (A p) ^ 2 ∂μ := by
  set m : ℝ := ∫ p, k p * A p ∂μ with hm
  have hsq : 0 ≤ ∫ p, k p * (A p - m) ^ 2 ∂μ :=
    integral_nonneg fun p => mul_nonneg (hk_nn p) (sq_nonneg _)
  have hexp : ∫ p, k p * (A p - m) ^ 2 ∂μ
      = (∫ p, k p * (A p) ^ 2 ∂μ) - m ^ 2 := by
    have hI1 : Integrable (fun p => k p * (A p) ^ 2 - (2 * m) * (k p * A p)) μ :=
      hA2_int.sub (hA_int.const_mul (2 * m))
    have hI2 : Integrable (fun p => m ^ 2 * k p) μ := hk_int.const_mul (m ^ 2)
    calc ∫ p, k p * (A p - m) ^ 2 ∂μ
        = ∫ p, (k p * (A p) ^ 2 - (2 * m) * (k p * A p)) + m ^ 2 * k p ∂μ :=
          integral_congr_ae (Eventually.of_forall fun p => by ring)
      _ = (∫ p, k p * (A p) ^ 2 - (2 * m) * (k p * A p) ∂μ) + ∫ p, m ^ 2 * k p ∂μ := by
          rw [integral_add hI1 hI2]
      _ = ((∫ p, k p * (A p) ^ 2 ∂μ) - ∫ p, (2 * m) * (k p * A p) ∂μ)
            + ∫ p, m ^ 2 * k p ∂μ := by
          rw [integral_sub hA2_int (hA_int.const_mul (2 * m))]
      _ = ((∫ p, k p * (A p) ^ 2 ∂μ) - (2 * m) * ∫ p, k p * A p ∂μ)
            + m ^ 2 * ∫ p, k p ∂μ := by
          rw [integral_const_mul, integral_const_mul]
      _ = (∫ p, k p * (A p) ^ 2 ∂μ) - m ^ 2 := by
          rw [← hm, hk_mass]; ring
  linarith

/-! ## Integrability of `Jker ρ ε * A` for `A` continuous on the ball -/

/-- **Global integrability of a kernel–test-function product.**  If `A` is continuous on the
closed ball of radius `ε`, then `p ↦ Jker ρ ε p * A p` is integrable on all of `ℝ²`: it is
integrable on the ball by compactness, and it vanishes off the ball since the kernel does. -/
theorem integrable_Jker_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ × ℝ → ℝ} (hA : ContinuousOn A (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => Jker ρ ε p * A p) :=
  (integrableOn_Jker_mul_ball hρ hε hA).integrable_of_forall_notMem_eq_zero
    (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])

/-- The kernel is nonnegative. -/
theorem Jker_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) (ε : ℝ) :
    ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p :=
  fun _ => mul_nonneg (sq_nonneg _) (hρ.nonneg _)

/-! ## The estimate -/

theorem sq_integral_Jker_mul_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * g p) ^ 2
      ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * (g p) ^ 2 :=
  sq_integral_mul_le_of_prob (μ := volume) (k := fun p : ℝ × ℝ => Jker ρ ε p) (A := g)
    (Jker_nonneg ρ hρ ε) (Jker_integrable hρ hε)
    (integrable_Jker_mul ρ hρ hε hg)
    (integrable_Jker_mul ρ hρ hε (hg.pow 2))
    (Jker_integral_eq_one ρ hρ hε)

end Work.FTS.StrongEps.HkSqAux
