import Mathlib
import Submission.Work.BoseBoxFock.pairGc23DirDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pgW_L2_le` — the `L²` bound on the weight of the clean `pairGc23` fibre

The weight `pgW p Θ₀ A B` (`pairGc23DirDefs`) is the product

    z ↦ star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)

of the two kernel-box factors with the free state factor, i.e. *not* including the parametric kernel
factor `pgKer`.  This module proves the Cauchy–Schwarz-type `L²` estimate used in `pairGc23DirV2`:

    ∫_{pairS23 ℓ p} ‖pgW p Θ₀ A B z‖² ≤ cA² cB² · pinL2 ℓ Θ₀ ,

i.e. the two kernel factors contribute only their sup bounds `cA`, `cB` while the state factor
contributes its full `L²` content `pinL2 ℓ Θ₀ = ∫_{abox n ℓ} ‖Θ₀‖²`.

The proof is the pointwise bound `‖pgW z‖² = ‖A z.2.1‖²‖B z.2.2‖²‖Θ₀(…)‖² ≤ cA²cB²‖Θ₀(…)‖²`
(monotonicity of the integral against the integrable majorant, which is continuous on the compact
box `pairS23`) followed by the change of variables
`pairS23_integral_sq_eq_pinL2` of `pairGc23Aux`.

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

theorem pgW_L2_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    (∫ z in Work.BoseBoxFock.pairS23 ℓ p, ‖Work.BoseBoxFock.pgW p Θ₀ A B z‖ ^ 2)
      ≤ cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 ℓ Θ₀ := by
  have hΘ₀c : Continuous Θ₀ := hΘ₀.continuous
  have hcont : Continuous (fun z :
      (pairFib23 n p → EuclideanSpace ℝ (Fin 3)) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2) :=
    ((hΘ₀c.comp (continuous_insertCoord2_joint_pg23 p)).norm.pow 2)
  have hIntg : IntegrableOn (fun z :
      (pairFib23 n p → EuclideanSpace ℝ (Fin 3)) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2)
      (pairS23 ℓ p) :=
    (continuous_const.mul hcont).continuousOn.integrableOn_compact (isCompact_pairS23 hℓ p)
  have hpt : ∀ z :
      (pairFib23 n p → EuclideanSpace ℝ (Fin 3)) × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
      ‖pgW p Θ₀ A B z‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2 := by
    intro z
    rw [show ‖pgW p Θ₀ A B z‖ ^ 2
        = ‖A z.2.1‖ ^ 2 * ‖B z.2.2‖ ^ 2 * ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2 from by
      simp [pgW, mul_pow]]
    have h1 : ‖A z.2.1‖ ^ 2 ≤ cA ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hAb _) 2
    have h2 : ‖B z.2.2‖ ^ 2 ≤ cB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBb _) 2
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  calc (∫ z in pairS23 ℓ p, ‖pgW p Θ₀ A B z‖ ^ 2)
      ≤ ∫ z in pairS23 ℓ p, cA ^ 2 * cB ^ 2 * ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) hIntg
          (Filter.Eventually.of_forall hpt)
    _ = cA ^ 2 * cB ^ 2
          * ∫ z in pairS23 ℓ p, ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2 := by
        rw [integral_const_mul]
    _ = cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ := by
        rw [pairS23_integral_sq_eq_pinL2 hℓ hp hΘ₀c]

end Work.BoseBoxFock
