import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.dict13Aux3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux5` — the general block-I functional and its standing hypotheses

`lhsGen ℓ Θ A B p e` is the `(ℓ³)⁻¹·re` of the block-I row `rowShape13 Θ A B (qmqKernel ℓ e) p`;
`lhsFun` (the left-hand side of `dict13_L1`) is its instance at `Θ = boxRestrictC ℓ Ψ` and
`A = B = c·θ_Λ`.

`RowData` bundles the hypotheses under which every analytic statement about `rowShape13` in this
chapter is made: positivity of the box side, the off-diagonal condition, the support of the state
factor in the box, measurability of the three functions, and finiteness of their `ℝ≥0∞` bounds.
Branding them as a structure keeps the statements of the `L¹` bounds readable.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox

set_option autoImplicit false

/-- The block-I row functional at an arbitrary state factor `Θ` and weights `A`, `B`. -/
noncomputable def lhsGen {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) (A B : E3 → ℂ) (p : Fin n × Fin n)
    (e : E3 → E3 → ℝ) : ℝ :=
  ((ℓ ^ 3)⁻¹ : ℝ) * (rowShape13 Θ A B (qmqKernel ℓ e) p).re

/-- The left-hand side of `dict13_L1` is the general one at the box restriction and the `θ`-weights. -/
theorem lhsFun_eq_lhsGen {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} {c : ℂ} {p : Fin n × Fin n}
    (e : E3 → E3 → ℝ) :
    lhsFun ℓ Ψ c p e = lhsGen ℓ (boxRestrictC ℓ Ψ)
      (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
      (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) p e := rfl

/-- **Standing hypotheses for the block-I row.**  `Θ` is the (complex) state factor, supported in
the `n`-particle box and bounded by `BΘ`; `A`, `B` are the two `θ`-weights, bounded by `BA`, `BB`;
`p` is off-diagonal and `ℓ > 0`. -/
structure RowData (n : ℕ) (ℓ : ℝ) (Θ : Xn n → ℂ) (A B : E3 → ℂ) (p : Fin n × Fin n) where
  hℓ : 0 < ℓ
  hp : p.1 ≠ p.2
  hΘs : Function.support Θ ⊆ abx n ℓ
  hΘm : Measurable Θ
  hAm : Measurable A
  hBm : Measurable B
  BΘ : ENNReal
  hΘb : ∀ x, ‖Θ x‖ₑ ≤ BΘ
  hΘf : BΘ ≠ ⊤
  BA : ENNReal
  hAb : ∀ y, ‖A y‖ₑ ≤ BA
  hAf : BA ≠ ⊤
  BB : ENNReal
  hBb : ∀ y, ‖B y‖ₑ ≤ BB
  hBf : BB ≠ ⊤

end Work.BoseBoxFock
