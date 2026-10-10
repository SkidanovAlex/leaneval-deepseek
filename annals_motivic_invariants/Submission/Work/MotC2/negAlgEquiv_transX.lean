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

set_option linter.style.haveILetI false

namespace Work.MotC2

/-- The negation `[-1]` acts on the `x`-coordinate of the translate by `Q` by changing the sign of
`Q`: `[-1](τ_Q x) = τ_{-Q} x`.

Here `transX E Q = phi E Q (genX E)` is the `x`-coordinate of `genPoint + Q`, so as a function of the
point `R` it is `x(R + Q)`; `negAlgEquiv E = [-1]` acts by `f ↦ f ∘ [-1]`, so the left-hand side is
`R ↦ x(-R + Q) = x(Q - R)` while the right-hand side is `R ↦ x(R - Q)`, and these agree because the
`x`-coordinate is even (`x(-P) = x(P)`).

Route.  Reduce to `Q = Point.zero` (`transX_zero`, `negAlgEquiv_genX`, `neg_zero`) or
`Q = Point.some a b h`.  In the latter case use `transX_some`
(`transX E (some a b h) = addX (baseE E) (genX E) a ℓ`, `ℓ = slope (baseE E) (genX E) a (genY E) b =
(genY E - b)/(genX E - a)`, via `slope_of_X_ne` and `genX_ne_algebraMap`), rewrite `negAlgEquiv`
through `negAlgEquiv_genX`, `negAlgEquiv_genY`, `AlgEquiv.commutes` (the constants `a`, `b` are
fixed) and `map_div₀`, and identify the resulting slope with the slope occurring in
`transX_some` for `-Q` (`- Point.some a b h = Point.some a (-b - a₁a - a₃) _` by `Point.neg_some`):
if `u := ((-genY E - e) - b)/(genX E - a)` is the transformed slope and
`v := (genY E + b + a₁a + a₃)/(genX E - a)` the slope at `-Q`, then `u + v = -a₁`, and since
`addX W x a ℓ = ℓ^2 + a₁ℓ - a₂ - x - a` is invariant under `ℓ ↦ -a₁ - ℓ`
(`(a₁+ℓ)² - a₁(a₁+ℓ) = ℓ² + a₁ℓ`), the two sides agree.  Close with `field_simp; ring`. -/
theorem negAlgEquiv_transX (L : Type*) [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] (Q : E.toAffine.Point) :
    Work.MotC2.negAlgEquiv E (Work.MotC2.transX E Q) = Work.MotC2.transX E (-Q) := by
  cases Q with
  | zero =>
      rw [Work.MotC2.transX_zero, Work.MotC2.negAlgEquiv_genX]
      exact Work.MotC2.transX_zero E
  | some a b h =>
      -- use the same `DecidableEq` instance for the `slope` occurring in `transX`
      letI : DecidableEq (Work.MotC2.Func E) := Work.MotC2.instDecEqFunc E
      -- `[-1]` commutes with the `addX` formula: it fixes the curve `baseE E` (the constants
      -- `a₁`, `a₂`) and acts on the arguments.
      have haddX : ∀ x₁ x₂ ℓ : Work.MotC2.Func E,
          (Work.MotC2.negAlgEquiv E) (WeierstrassCurve.Affine.addX (Work.MotC2.baseE E) x₁ x₂ ℓ)
            = WeierstrassCurve.Affine.addX (Work.MotC2.baseE E) ((Work.MotC2.negAlgEquiv E) x₁)
                ((Work.MotC2.negAlgEquiv E) x₂) ((Work.MotC2.negAlgEquiv E) ℓ) := by
        intro x₁ x₂ ℓ
        simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
          map_sub, map_add, map_mul, map_pow]
        rw [AlgEquiv.commutes, AlgEquiv.commutes]
      have hxne : Work.MotC2.genX E ≠ algebraMap L (Work.MotC2.Func E) a :=
        Work.MotC2.genX_ne_algebraMap E a
      -- the image of the slope `(genY E - b)/(genX E - a)` under `[-1]`
      have hne_slope : (Work.MotC2.negAlgEquiv E)
          (WeierstrassCurve.Affine.slope (Work.MotC2.baseE E) (Work.MotC2.genX E)
            (algebraMap L (Work.MotC2.Func E) a) (Work.MotC2.genY E)
            (algebraMap L (Work.MotC2.Func E) b))
          = ((- Work.MotC2.genY E - algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E
                - algebraMap L (Work.MotC2.Func E) E.a₃) - algebraMap L (Work.MotC2.Func E) b)
              / (Work.MotC2.genX E - algebraMap L (Work.MotC2.Func E) a) := by
        rw [WeierstrassCurve.Affine.slope_of_X_ne hxne, map_div₀, map_sub, map_sub,
          Work.MotC2.negAlgEquiv_genY, Work.MotC2.negAlgEquiv_genX, AlgEquiv.commutes,
          AlgEquiv.commutes]
      rw [Work.MotC2.transX_some E a b h, haddX, Work.MotC2.negAlgEquiv_genX, AlgEquiv.commutes,
        hne_slope]
      -- the slope at `-Q = Point.some a (-b - a₁a - a₃) _`
      rw [WeierstrassCurve.Affine.Point.neg_some,
        Work.MotC2.transX_some E a (E.toAffine.negY a b) _,
        WeierstrassCurve.Affine.slope_of_X_ne hxne]
      simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.Affine.addX, map_sub, map_mul, map_neg]
      field_simp
      first | refl_ring1 | ring

end Work.MotC2
