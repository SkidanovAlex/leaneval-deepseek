import ChallengeDeps
import Submission.Work.KinPSuperadd.Superadd
import Submission.Work.KinPSuperadd.fubini_abox_two
import Submission.Work.KinPSuperadd.integral_abox_one_slot
import Submission.Work.SmallBoxA0.g0w0Mass_nonneg_general
import Submission.Work.SmallBoxA0.one_lt_chiSup_sq
import Submission.Work.SmallBoxBlockBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Work.KernelL2
open Submission BoseGases
set_option autoImplicit false
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The iterated Coulomb integral of the scattering numerator is integrable.**

Since `g₀ = v(1−w₀)` is nonnegative a.e. and the Newton representation
(`scattering_newton_representation`)

`w₀ x = (1/(8π))·∫ y, g₀ y·‖x−y‖⁻¹`

holds for a.e. `x`, the inner integral `∫ y, g₀ x·g₀ y·‖x−y‖⁻¹` equals
`g₀ x · (8π·w₀ x) = 8π·(g₀ x·w₀ x)` for a.e. `x`.  Hence the whole iterated
integrand is a.e. equal to `8π·g₀·w₀`, which is integrable
(`g0w0_integrable`). -/
lemma integrable_coulomb_iter_g0 {R : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    Integrable (fun x : ℝ³ => ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹) := by
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  -- Newton representation of the chosen scattering solution, in terms of `g₀`.
  have hrep : ∀ᵐ x : ℝ³,
      (Classical.choose h) x =
        (1 / (8 * π)) * (∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹) := by
    have h0 := scattering_newton_representation (v := v) (w := Classical.choose h) (R := R)
      hR hvrad hv_supp hrad₀ hw₀
    filter_upwards [h0] with x hx
    simpa [g0] using hx
  have hGw : Integrable (fun x : ℝ³ => g0 v h x * Classical.choose h x) :=
    g0w0_integrable hR hv_nonneg hvrad hv_supp h
  refine Integrable.congr (hGw.const_mul (8 * π)) ?_
  filter_upwards [hrep] with x hx
  -- pull the `x`-factor out of the inner integral
  have hinner : (∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)
      = g0 v h x * (∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹) := by
    rw [show (fun y : ℝ³ => g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹)
          = fun y : ℝ³ => g0 v h x * (g0 v h y * (‖x - y‖ : ℝ)⁻¹) from by
        funext y; ring]
    exact MeasureTheory.integral_const_mul _ _
  -- the Newton representation, solved for the inner integral
  have hwI : 8 * π * (Classical.choose h) x =
      ∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹ := by
    have hc : (8 : ℝ) * π ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    calc 8 * π * (Classical.choose h) x
        = 8 * π * ((1 / (8 * π)) * (∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹)) := by rw [hx]
      _ = ∫ y : ℝ³, g0 v h y * (‖x - y‖ : ℝ)⁻¹ := by
            rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]
  show 8 * π * (g0 v h x * (Classical.choose h) x)
      = ∫ y : ℝ³, g0 v h x * g0 v h y * (‖x - y‖ : ℝ)⁻¹
  rw [hinner, ← hwI]
  ring

end Work.KernelL2
