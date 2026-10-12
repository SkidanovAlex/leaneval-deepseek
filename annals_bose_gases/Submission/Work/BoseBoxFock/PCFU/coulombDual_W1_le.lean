import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.coulInt_W1fun_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

theorem coulombDual_W1_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ‖∫ x : EuclideanSpace ℝ (Fin 3), ((Work.BoseFixR.W1fun v h ℓ x : ℝ) : ℂ) * ψ x‖ ^ 2
      ≤ 64 * Real.pi * BoseGases.a v
        * ∑ j : Fin 3, ∫ x, ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  -- The Coulomb energy bound of `W₁ = wScaled ℓ (g₀)` in the dilute regime.
  obtain ⟨hJint, hJle⟩ :=
    coulInt_W1fun_le (v := v) (h := h) (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hℓ hRℓ
  -- The two remaining hypotheses of the duality theorem for `W₁`.
  have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hW0 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixR.W1fun v h ℓ x :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hdual :=
    Work.BoseBoxFock.L1Tails.coulombDual (W := Work.BoseFixR.W1fun v h ℓ)
      hWint hW0 hJint hψ hψc
  -- Nonnegativity of the kinetic content.
  have hKnn :
      0 ≤ ∑ j : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
            ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => by positivity))
  refine hdual.trans ?_
  calc (4 * Real.pi)⁻¹
          * (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
              Work.BoseBoxFock.coulInt (Work.BoseFixR.W1fun v h ℓ) p)
          * (∑ j : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
              ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ (4 * Real.pi)⁻¹ * (256 * Real.pi ^ 2 * BoseGases.a v)
          * (∑ j : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
              ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hJle (by positivity)) hKnn
    _ = 64 * Real.pi * BoseGases.a v
          * (∑ j : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
              ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
        have hc : (4 * Real.pi)⁻¹ * (256 * Real.pi ^ 2 * BoseGases.a v)
            = 64 * Real.pi * BoseGases.a v := by
          field_simp
          ring
        rw [hc]

end Work.BoseBoxFock.PCFU
