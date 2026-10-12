import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.W1_g0_finite
import Submission.Work.BoseRowsFS.cross_chat_coulomb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.mass_identity` — FS `eq:I2-integral`, exact cross (mass) form

For a nonnegative radial potential `v` of range `R`, in the dilute regime
`R ≤ ℓ·chiR0`, with a scattering solution `h : ScatSol v` and
`W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g₀)`, `g₀ = g₀ v h`, `ω = Classical.choose h`,

  `(2π)⁻³ ∫ k, Ŵ₁(k)·ĝ₀(k)/(2‖k‖²) dk = ∫ W₁ ω`.

This is exactly the **cross** Fourier–Coulomb identity: the momentum integrand
`Ŵ₁·ĝ₀/(2‖k‖²)` is `Ŵ₁` tested against the Fourier transform of
`ω = (8π)⁻¹(‖·‖⁻¹ * g₀)` (Newton representation), and Plancherel gives `∫W₁ω`.  The
x-space side `∬W₁(x)g₀(y)/‖x−y‖ = 8π∫W₁ω` is the already-proved
`Work.BoseFixR.lintegral_W1_g0_eq`; the momentum-space cross identity is
`Work.BoseRowsFS.cross_chat_coulomb`, and the three finiteness facts it needs are
`Work.BoseRowsFS.W1_g0_finite`.
-/

namespace Work.BoseRowsFS

open MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem mass_identity {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ((2 * Real.pi) ^ 3)⁻¹
        * (∫ k, Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) k / (2 * ‖k‖ ^ 2))
      = ∫ x, Work.BoseFixR.W1fun v h ℓ x * Classical.choose h x := by
  -- the two kernels, their integrability, a.e. nonnegativity and evenness
  have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hUint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hWnn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixR.W1fun v h ℓ x :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hUnn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hWe : ∀ x : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x :=
    fun x => Work.BoseB7AK.C3Q.I2_W1fun_neg hvrad h x
  have hUe : ∀ x : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.g0 v h (-x) = Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_even hvrad h
  -- the three Coulomb double integrals are finite
  have hfin := W1_g0_finite hR hℓ hv_nonneg hvrad hv_supp h hRℓ
  have hP := hfin.1
  have hRfin := hfin.2.1
  have hX := hfin.2.2
  -- the cross Fourier-Coulomb identity
  have hcross := cross_chat_coulomb hWint hUint hWnn hUnn hWe hUe hP hRfin hX
  rw [hcross]
  -- the x-space Newton identity
  simp only [Work.BoseFixR.W1fun]
  rw [Work.BoseFixR.lintegral_W1_g0_eq (v := v) h (R := R) (ℓ := ℓ)
    hR hv_nonneg hvrad hv_supp hRℓ hℓ]
  -- arithmetic: `(1/(8π))·(8π·A) = A`
  have hA0 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x * Classical.choose h x := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hWnn,
      (Submission.BoseGases.chosen_w0_bounds_ae (v := v) (R := R)
        hR hv_nonneg hvrad hv_supp h).1] with x hx hw
    exact mul_nonneg hx hw
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 8 * Real.pi),
    ENNReal.toReal_ofReal hA0]
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ (by positivity : (8 : ℝ) * Real.pi ≠ 0), one_mul]

end Work.BoseRowsFS
