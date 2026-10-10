import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV

/-- Norm computation (pure algebra; the heart of the support statement used by `degreeZero`).
For `a` in the affine coordinate ring of a Weierstrass curve over a field `N` and an `N`-algebra
map `φ : CoordinateRing E →ₐ[N] N` sending the coordinates `x ↦ c`, `y ↦ d` and killing `a`, the
norm `Algebra.norm N[X] a ∈ N[X]` vanishes at `c`.

Route. `CoordinateRing.exists_smul_basis_eq a` gives `p q : N[X]` with
`p • 1 + q • CoordinateRing.mk E X = a`. `CoordinateRing.norm_smul_basis` computes
`norm (p • 1 + q • mk X) = p^2 - p*q*(C a₁ * X + C a₃) - q^2*(X^3 + C a₂*X^2 + C a₄*X + C a₆)`.
The composite `N[X] --algebraMap--> CoordinateRing E --φ--> N` is an `N`-algebra map sending `X`
to `φ (Work.MotC2.coordX E) = c` (use `Work.MotC2.algebraMap_X_eq_coordX`); by uniqueness of
`N`-algebra maps out of `N[X]` (`Polynomial.algHom_ext'`) it is `Polynomial.aeval c`. Hence, using
`Algebra.algebraMap_eq_smul_one`, `φ (p • 1) = Polynomial.eval c p` and
`φ (q • coordY E) = Polynomial.eval c q * d` (from `hy`). So `ha` gives
`eval c p = -(eval c q) * d`. Finally evaluate the norm formula at `c` (statement `theorem`:
`Work.MotV.normEvalOfAlgHom`). -/
theorem normEvalOfAlgHom {N : Type*} [Field N] (E : WeierstrassCurve N)
    (a : WeierstrassCurve.Affine.CoordinateRing E) (c d : N)
    (φ : WeierstrassCurve.Affine.CoordinateRing E →ₐ[N] N)
    (hx : φ (Work.MotC2.coordX E) = c) (hy : φ (Work.MotC2.coordY E) = d)
    (ha : φ a = 0) (heq : WeierstrassCurve.Affine.Equation E c d) :
    Polynomial.eval c (Algebra.norm (Polynomial N) a) = 0 := by
  -- Write `a` in the `N[X]`-basis `{1, y}` of the coordinate ring.
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) a
  -- The composite `N[X] → CoordinateRing E --φ--> N` is the evaluation at `c`.
  have hφ : ∀ r : Polynomial N,
      φ (algebraMap (Polynomial N) (CoordinateRing E) r) = Polynomial.eval c r := by
    intro r
    have h1 : (φ.comp (IsScalarTower.toAlgHom N (Polynomial N) (CoordinateRing E)))
        = Polynomial.aeval c := by
      apply Polynomial.algHom_ext
      show φ (algebraMap (Polynomial N) (CoordinateRing E) Polynomial.X)
        = Polynomial.aeval c Polynomial.X
      rw [Work.MotC2.algebraMap_X_eq_coordX, hx, Polynomial.aeval_X]
    have h2 := AlgHom.congr_fun h1 r
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at h2
    rwa [Polynomial.coe_aeval_eq_eval] at h2
  have hp1 : φ (p • (1 : CoordinateRing E)) = Polynomial.eval c p := by
    rw [← Algebra.algebraMap_eq_smul_one]; exact hφ p
  have hqy : φ (q • CoordinateRing.mk E Polynomial.X) = Polynomial.eval c q * d := by
    rw [Algebra.smul_def, map_mul, hφ q, ← Work.MotC2.coordY_eq_mk, hy]
  -- `ha` becomes the relation `eval c p = -(eval c q) * d`.
  have h0 : Polynomial.eval c p + Polynomial.eval c q * d = 0 := by
    have h := ha
    rw [map_add, hp1, hqy] at h
    exact h
  -- The Weierstrass equation, expanded.
  have heq' : d ^ 2 + E.a₁ * c * d + E.a₃ * d
      = c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆ := by
    have h := (WeierstrassCurve.Affine.equation_iff' (W := E) c d).mp heq
    rwa [sub_eq_zero] at h
  -- Evaluate the norm formula at `c` and use the two relations.
  rw [CoordinateRing.norm_smul_basis]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination (norm := first | refl_ring1 | ring1) (Polynomial.eval c p - Polynomial.eval c q * d
      - Polynomial.eval c q * (E.a₁ * c + E.a₃)) * h0 + Polynomial.eval c q ^ 2 * heq'

end Work.MotV
