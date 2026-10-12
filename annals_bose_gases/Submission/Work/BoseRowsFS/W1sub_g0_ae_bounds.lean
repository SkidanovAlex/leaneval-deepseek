import ChallengeDeps
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

/-- The a.e. two-sided bound on the difference `W₁ − g₀` (`W₁ = wScaled ℓ (g₀) = Work.BoseFixR.W1fun v h ℓ`, `g₀ = Submission.BoseGases.g0 v h = v(1−ω)`, `ω = Classical.choose h`): `0 ≤ W₁ − g₀ ≤ 2C₁(R/ℓ)²·g₀` a.e., combining the sharp a.e. sandwich `Work.BoseB7AK.C3Q.W1_sharp_ae_aux` (`W₁ ≤ (1+2C₁(R/ℓ)²)g₀`) with the lower sandwich `g₀ ≤ W₁` a.e. (`Work.BoseB7AK.C3Q.I2_g0_le_W1fun_ae`) and `g₀ ≥ 0` a.e. (`Submission.BoseGases.g0_nonneg_ae`). -/
theorem W1sub_g0_ae_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ C₁ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ t : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C₁ * ‖t‖ ^ 2)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x ∧
        Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x
          ≤ (2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by
  have hsharp :=
    Work.BoseB7AK.C3Q.W1_sharp_ae_aux hR hℓ hC₁0 hC₁ hv_nonneg hvrad hv_supp h hRℓ
  have hlow :=
    Work.BoseB7AK.C3Q.I2_g0_le_W1fun_ae hR hℓ hv_nonneg hvrad hv_supp h hRℓ
  filter_upwards [hsharp, hlow] with x hx _hxl
  obtain ⟨-, hWle⟩ := hx
  refine ⟨by linarith, ?_⟩
  nlinarith [hWle]

end Work.BoseRowsFS
