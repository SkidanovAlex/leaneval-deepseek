import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.block13_dict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux` — definitions for the `L¹` dictionary `dict13_L1`

The target `Work.BoseBoxFock.dict13_L1` is the block-`I` box ↔ word dictionary at a pair kernel
`k` that is only assumed **integrable** (and symmetric), whereas the proved bounded version
`Work.BoseBoxFock.block13_dict` needs `k` measurable **and bounded**.  The route taken here is:

* prove the statement for measurable, bounded symmetric kernels (that is `block13_dict`);
* show that both sides depend only on the a.e. class of `k`;
* show that both sides are continuous in the `L¹(Λ×Λ)`-norm of `k` (with a fixed constant), so
  that the value-truncations of a measurable representative converge.

The last point is the analytic heart: an explicit `ENNReal`-valued domination of the
`rowShape13`-integrand by the box `L¹`-norm of the kernel.  The definitions below fix the objects
used by the auxiliary lemmas (`rowInt`, `rowProd`, `rowDom`).

Everything here is `sorry`-free (definitions only).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- The `rowShape13` integrand `star (Θ x) * A (x p.1) * K (x p.2) y * star (B u) *
Θ (update (update x p.1 y) p.2 u)` as a function of the pair kernel `K`. -/
noncomputable def rowInt {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ)
    (p : Fin n × Fin n) : Xn n → E3 → E3 → ℂ :=
  fun x y u => star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
    * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- `rowShape13 Θ A B K p` is the triple integral of `rowInt Θ A B K p`. -/
theorem rowShape13_eq_integral {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ)
    (p : Fin n × Fin n) :
    rowShape13 Θ A B K p = ∫ x : Xn n, ∫ y : E3, ∫ u : E3, rowInt Θ A B K p x y u := rfl

/-- The same integrand, uncurried on `Xn n × (E3 × E3)` (for Tonelli/Fubini arguments). -/
noncomputable def rowProd {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ)
    (p : Fin n × Fin n) (z : Xn n × (E3 × E3)) : ℂ :=
  rowInt Θ A B K p z.1 z.2.1 z.2.2

/-- The universal `ENNReal`-valued dominator of the `rowInt` integrand at the `Q M Q` kernel of a
pair kernel `e`: the four rows of `qmqKernelR` bounded by the corresponding box integrals of the
absolute value of `e`. -/
noncomputable def rowDom {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) (A B : E3 → ℂ) (p : Fin n × Fin n)
    (e : E3 → E3 → ℝ) : Xn n × (E3 × E3) → ENNReal :=
  fun z => ‖Θ z.1‖ₑ * ‖A (z.1 p.1)‖ₑ * ‖B z.2.2‖ₑ
    * ‖Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)‖ₑ
    * (‖e (z.1 p.2) z.2.1‖ₑ
        + ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ∫⁻ y', ‖e (z.1 p.2) y'‖ₑ ∂(volume.restrict (acb ℓ))
        + ENNReal.ofReal ((ℓ ^ 3)⁻¹) * ∫⁻ w', ‖e w' z.2.1‖ₑ ∂(volume.restrict (acb ℓ))
        + ENNReal.ofReal ((ℓ ^ 3)⁻¹) ^ 2
            * ∫⁻ w', ∫⁻ y', ‖e w' y'‖ₑ ∂(volume.restrict (acb ℓ))
                ∂(volume.restrict (acb ℓ)))

end Work.BoseBoxFock
