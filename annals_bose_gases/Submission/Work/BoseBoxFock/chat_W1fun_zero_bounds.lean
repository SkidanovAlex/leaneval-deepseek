import ChallengeDeps
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBoxFock.W1fun_L1_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem chat_W1fun_zero_bounds (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ ℓ : ℝ, 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      (0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 ∧
        Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 ≤ Cw * BoseGases.a v ∧
        0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0) := by
  refine ⟨16 * Real.pi, by positivity, fun ℓ hℓ hRℓ => ⟨?_, ?_, ?_⟩⟩
  · -- `Ŵ₁(0) = ∫W₁ ≥ 0` (a.e.-nonnegativity of `W₁ = wScaled ℓ (g₀ v h)`)
    rw [Work.BoseB7AK.W1rows.chat_zero]
    simpa [Work.BoseFixR.W1fun] using
      Submission.BoseGases.wScaled_g0_mass_nonneg hR hv hvrad hv_supp h (ℓ := ℓ)
  · -- `Ŵ₁(0) ≤ |Ŵ₁(0)| ≤ 16π·(a v)`
    calc Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0
        ≤ |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0| := le_abs_self _
      _ ≤ 16 * Real.pi * BoseGases.a v :=
          Work.BoseB7AK.W1rows.W1hat_abs_le (v := v) (h := h) (R := R) (ℓ := ℓ)
            hR hℓ hv hvrad hv_supp hRℓ 0
  · -- `0 ≤ Ŵ₁ω(0)` (the `W1omega0_rows` row of the interface)
    obtain ⟨C, hC, hnn, -⟩ := Work.BoseB7AK.W1rows.W1omega0_rows (v := v) (h := h)
      (R := R) (ℓ := ℓ) hR hℓ hv hvrad hv_supp hRℓ
    exact hnn

end Work.BoseBoxFock
