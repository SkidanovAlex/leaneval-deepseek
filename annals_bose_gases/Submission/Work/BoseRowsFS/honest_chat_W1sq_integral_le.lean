import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honest_chat_W1sq_integral_le` — the continuum bound of row 1

FS's `eq:I2-integral`, in the uniform-in-`ℓ` form needed by
`Work.BoseRowsFS.RowSumW1sq_of_lattice`'s hypothesis `hcont`:

    ∃ KE ≥ 0, ∀ ℓ ≥ 1, R ≤ ℓ·chiR0,
      (2π)⁻³ ∫  Ŵ₁(p)²/(2‖p‖²) dp ≤ KE · a v,      Ŵ₁ = chat (W1fun v h ℓ).

## Route

`Work.BoseB7AK.C3Q.I2_integral_bound` gives
`|(2π)⁻³∫Ŵ₁²/(2‖p‖²) − ∫g₀ω| ≤ C(R/ℓ)²·∫g₀ω` with an absolute `C`, and
`Submission.BoseGases.chosen_gomega_integral_bounds` gives
`0 ≤ ∫g₀ω ≤ 8π·a v`.  Hence, since `R ≤ ℓ·chiR0` and `ℓ > 0` give
`(R/ℓ)² ≤ chiR0²`,

    (2π)⁻³∫Ŵ₁²/(2‖p‖²) ≤ (1 + C·chiR0²)·∫g₀ω ≤ (1 + C·chiR0²)·8π·a v.

The constant `KE` does not depend on `ℓ`, which is what the uniform lattice
comparison `Work.BoseRowsFS.honest_lattice_W1sq_le_uniform` needs to be composed
with.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseRowsFS

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem honest_chat_W1sq_integral_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (R : ℝ) (hR : 0 < R) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ KE : ℝ, 0 ≤ KE ∧ ∀ (ℓ : ℝ), 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ((2 * Real.pi) ^ 3)⁻¹
          * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / (2 * ‖p‖ ^ 2))
        ≤ KE * _root_.BoseGases.a v := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseB7AK.C3Q.I2_integral_bound
  refine ⟨(1 + C * Submission.BoseGases.chiR0 ^ 2) * (8 * Real.pi), by positivity, ?_⟩
  intro ℓ hℓ hRℓ
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hkey := hC hR hℓ0 hv_nonneg hvrad hv_supp h hRℓ
  obtain ⟨hI0, hIle⟩ :=
    Submission.BoseGases.chosen_gomega_integral_bounds hR hv_nonneg hvrad hv_supp h
  set A : ℝ := ((2 * Real.pi) ^ 3)⁻¹
      * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / (2 * ‖p‖ ^ 2))
    with hA
  set I : ℝ := ∫ x, (v x * (1 - Classical.choose h x)) * Classical.choose h x with hI
  have hratio : (R / ℓ) ^ 2 ≤ Submission.BoseGases.chiR0 ^ 2 := by
    have h1 : R / ℓ ≤ Submission.BoseGases.chiR0 := by
      rw [div_le_iff₀ hℓ0, mul_comm]
      exact hRℓ
    have h2 : (0 : ℝ) ≤ R / ℓ := le_of_lt (div_pos hR hℓ0)
    exact pow_le_pow_left₀ h2 h1 2
  have hCI : C * (R / ℓ) ^ 2 * I ≤ C * Submission.BoseGases.chiR0 ^ 2 * I := by
    have h3 : C * (R / ℓ) ^ 2 ≤ C * Submission.BoseGases.chiR0 ^ 2 :=
      mul_le_mul_of_nonneg_left hratio hC0
    exact mul_le_mul_of_nonneg_right h3 hI0
  have hA2 : A ≤ (1 + C * Submission.BoseGases.chiR0 ^ 2) * I := by
    have h4 : A - I ≤ C * (R / ℓ) ^ 2 * I := (abs_le.mp hkey).2
    linarith [h4, hCI]
  calc ((2 * Real.pi) ^ 3)⁻¹
        * (∫ p, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / (2 * ‖p‖ ^ 2))
      = A := rfl
    _ ≤ (1 + C * Submission.BoseGases.chiR0 ^ 2) * I := hA2
    _ ≤ (1 + C * Submission.BoseGases.chiR0 ^ 2) * (8 * Real.pi * _root_.BoseGases.a v) := by
        refine mul_le_mul_of_nonneg_left hIle ?_
        nlinarith [hC0, sq_nonneg Submission.BoseGases.chiR0]
    _ = ((1 + C * Submission.BoseGases.chiR0 ^ 2) * (8 * Real.pi)) * _root_.BoseGases.a v := by
        ring

end Work.BoseRowsFS
