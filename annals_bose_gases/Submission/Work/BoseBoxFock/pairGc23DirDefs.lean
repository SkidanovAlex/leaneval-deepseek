import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGc23Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc23DirDefs` — the weight/kernel decomposition of the clean `pairGc23` fibre

The clean `pairGc23` fibre of `pairGCore` is the box integral

    ∫ z in K, star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
                 * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1) ,   K = pairS23 ℓ p.

Only the **first** factor depends on the two kernel parameters `w₀`, `w₁` (and it does so through
the single slot `p.1` for `w₀` and the single slot `p.2` for `w₁`); the remaining three factors are
a *fixed* function of the integration variable `z`.  This module names the two pieces:

* `pgW p Θ₀ A B` — the weight `z ↦ star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)`;
* `pgKer p Θ₀ w₁` — the parametric kernel `(w, z) ↦ star (Θ₀ (insertCoord2 p w w₁ z.1))`;

and records that the fibre is the parametric box integral of their product
(`pairGc23_eq_weight`).  This is the shape used by the dominated-differentiation lemma for
parametric integrals with a bounded measurable weight, and it is what makes the Cauchy–Schwarz
estimate of `pairGc23DirV2` work: the weight carries the two kernel-box factors `A`, `B` while the
`z.1`-only kernel factor carries the derivative of `Θ₀`.

`sorry`-free (definitions and one definitional identity).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- The **parametric kernel factor** of the clean `pairGc23` fibre at the fixed second kernel
parameter `w₁`: `(w, z) ↦ star (Θ₀ (insertCoord2 p w w₁ z.1))`. -/
def pgKer {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (w₁ : E3) :
    E3 → ((pairFib23 n p → E3) × (E3 × E3)) → ℂ :=
  fun w z => star (Θ₀ (insertCoord2 p w w₁ z.1))

/-- The **weight** of the clean `pairGc23` fibre: the three factors of the integrand that do not
depend on the kernel parameters. -/
def pgW {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ) :
    ((pairFib23 n p → E3) × (E3 × E3)) → ℂ :=
  fun z => star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)

/-- **The clean fibre is the parametric box integral of the weight times the kernel factor.** -/
theorem pairGc23_eq_weight {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ) (w w₁ : E3) :
    pairGc23 ℓ p hp Θ₀ A B w w₁
      = ∫ z in pairS23 ℓ p, pgW p Θ₀ A B z * pgKer p Θ₀ w₁ w z := by
  rw [pairGc23, pairS23]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [pgW, pgKer, insertCoord2_eq, if_true]
  ring

/-- The norm of the kernel factor only depends on `z.1`. -/
theorem pgKer_norm {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (w₁ w : E3) (z :
    (pairFib23 n p → E3) × (E3 × E3)) :
    ‖pgKer p Θ₀ w₁ w z‖ = ‖Θ₀ (insertCoord2 p w w₁ z.1)‖ := by
  simp [pgKer]

end Work.BoseBoxFock
