import Mathlib
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open WeierstrassCurve.Affine

-- `transX`/`transY` were defined using the `DecidableEq` instance on the function field that
-- `TranslationDefs` installs locally; we re-register exactly that instance so that the `slope`
-- terms we write are syntactically the ones produced by `transX_some`/`transY_some`.
attribute [local instance] Work.MotC2.instDecEqFunc

variable {L : Type*} [Field L]

/-- The negation `[-1]` of the function field commutes with the `addX` formula. -/
lemma negAlgEquiv_addX_formula (E : WeierstrassCurve L) (x₁ x₂ ℓ : Func E) :
    negAlgEquiv E (addX (baseE E) x₁ x₂ ℓ) =
      addX (baseE E) (negAlgEquiv E x₁) (negAlgEquiv E x₂) (negAlgEquiv E ℓ) := by
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    map_sub, map_add, map_mul, map_pow]
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

/-- The negation `[-1]` of the function field commutes with the `addY` formula. -/
lemma negAlgEquiv_addY_formula (E : WeierstrassCurve L) (x₁ x₂ y₁ ℓ : Func E) :
    negAlgEquiv E (addY (baseE E) x₁ x₂ y₁ ℓ) =
      addY (baseE E) (negAlgEquiv E x₁) (negAlgEquiv E x₂) (negAlgEquiv E y₁)
        (negAlgEquiv E ℓ) := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, map_sub, map_add, map_mul, map_pow, map_neg]
  rw [AlgEquiv.commutes, AlgEquiv.commutes, AlgEquiv.commutes]

/-- The negation `[-1]` acts on the `y`-coordinate of the translate by `Q` by the negation formula
in `Q`: `[-1](τ_Q y) = -τ_{-Q} y - a₁·τ_{-Q} x - a₃`.

As functions of the point `R`, `transX E Q` is `x(R + Q)` and `transY E Q` is `y(R + Q)`, so the
left-hand side is `R ↦ y(-R + Q) = y(Q - R) = y(-(R - Q)) = -y(R - Q) - a₁x(R - Q) - a₃`, which is
the right-hand side (`-transY E (-Q) - a₁·transX E (-Q) - a₃`).

Route.  Same reduction as `Work.MotC2.negAlgEquiv_transX`: the case `Q = Point.zero` is
`transY_zero`, `negAlgEquiv_genX`, `negAlgEquiv_genY`, `neg_zero`; for `Q = Point.some a b h` use
`transY_some` (with `Point.neg_some` for the coordinates of `-Q`) and the same slope computation:
with `u` the transformed slope and `v` the slope at `-Q` one has `a₁ = -(u+v)` and `addX(u) = addX(v)`,
and expanding `addY W x a y ℓ = -(ℓ(addX ℓ - x) + y) - a₁·addX ℓ - a₃` gives the identity.  Close with
`field_simp; ring` (the ring identity `transY_ring_id` of `Submission.Work.MotC2.TransYFormula` may be
reused). -/
theorem negAlgEquiv_transY (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) :
    Work.MotC2.negAlgEquiv E (Work.MotC2.transY E Q) =
      - Work.MotC2.transY E (-Q) -
          algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.transX E (-Q) -
        algebraMap L (Work.MotC2.Func E) E.a₃ := by
  cases Q with
  | zero =>
      rw [transY_zero, show (-Point.zero : E.toAffine.Point) = Point.zero from rfl, transY_zero,
        transX_zero, negAlgEquiv_genY]
  | some a b h =>
      have hne : genX E ≠ algebraMap L (Func E) a := genX_ne_algebraMap E a
      rw [transY_some E a b h, negAlgEquiv_addY_formula, negAlgEquiv_genX, negAlgEquiv_genY,
        (negAlgEquiv E).commutes a]
      rw [Point.neg_some h, transY_some, transX_some]
      -- the images of the two slopes under `[-1]` and at `-Q`
      have hu : (negAlgEquiv E) (slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
            (algebraMap L (Func E) b)) =
          ((-genY E - algebraMap L (Func E) E.a₁ * genX E - algebraMap L (Func E) E.a₃) -
            algebraMap L (Func E) b) / (genX E - algebraMap L (Func E) a) := by
        rw [slope_of_X_ne hne, map_div₀, map_sub, map_sub, negAlgEquiv_genX, negAlgEquiv_genY,
          (negAlgEquiv E).commutes a, (negAlgEquiv E).commutes b]
      have hv : slope (baseE E) (genX E) (algebraMap L (Func E) a) (genY E)
            (algebraMap L (Func E) (negY E a b)) =
          (genY E - algebraMap L (Func E) (negY E a b)) / (genX E - algebraMap L (Func E) a) :=
        slope_of_X_ne hne
      rw [hu, hv]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, map_sub, map_mul, map_neg]
      have hden : genX E - algebraMap L (Func E) a ≠ 0 := sub_ne_zero.mpr hne
      field_simp
      first | refl_ring1 | ring

end Work.MotC2
