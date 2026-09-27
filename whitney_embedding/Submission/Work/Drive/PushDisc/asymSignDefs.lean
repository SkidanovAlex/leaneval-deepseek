import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# `Work.Drive.PushDisc.asymSignDefs`: the linear-algebra data of the sign derivation

The sign derivation of the one-sided normal form (`Work.Drive.PushDisc.AsymChartData`) compares the
signs of the two crossings in the *model* coordinates `ξ = (x, y, u, v) = Φ (f ·)` of
`Work.Drive.Whitney.Mdl k`.  `Work.Whitney.pairDet` computes the crossing sign as the determinant of

    (u₁, u₂) ↦ pairEquiv (A u₁ + B u₂),      A = fderiv (f ∘ c₁.symm) (c₁ p₁),
                                             B = fderiv (f ∘ c₂.symm) (c₂ p₂),

an endomorphism of `E^n × E^n`.  For the *model* charts

* `c₁` = the inverse of the first sheet's parametrisation, so that `Φ (f (c₁.symm u)) = incLM u`
  (the flattened first sheet is the plane `{y = 0, v = 0}`),
* `c₂` = the inverse of the second sheet's `(x,v)`-parametrisation, so that
  `Φ (f (c₂.symm v)) = graphLM (yx, ·) v` (the second sheet is a graph `(x,v) ↦ (x, y, u, v)`),

both jets factor through the *same* `dΘ` at the *same* ambient point (`f p₁ = f p₂`), so the
`pairDet`s are the determinants of `pairZ ∘ (incLM coprod graphLM ·)` up to one common nonzero
factor `det (pairEquiv ∘ dΘ)`.  This file provides the three linear maps involved.

* `pairZ` — the pairing `(x, y, u, v) ↦ ((x,u), (y,v))` of the model space with the two block
  coordinates that `pairEquiv` splits into;
* `incLM` — the inclusion of the first sheet's plane, `(x,u) ↦ (x, 0, u, 0)`;
* `graphLM` — the jet of a graph over `(x,v)`, `(x,v) ↦ (x, yx * x + b v, x • a + D v, v)`.

The identity `det (pairZ ∘ (incLM coprod graphLM yx b a D)) = c * yx` (with a constant `c ≠ 0`
independent of the data) is the *content* of the sign derivation: the determinant of a crossing is
proportional to `yx = ∂_x y`, the derivative of the *height of the core* of the second sheet in the
`x`-direction.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

/-- **The pairing of the model space** with the two blocks of `n = k + 1` coordinates that
`pairEquiv` splits into: `(x, y, u, v) ↦ ((x,u), (y,v))`. -/
noncomputable def pairZ (k : ℕ) : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ]
    ((ℝ × EuclideanSpace ℝ (Fin k)) × (ℝ × EuclideanSpace ℝ (Fin k))) where
  toFun ξ := ((ξ.1, ξ.2.2.1), (ξ.2.1, ξ.2.2.2))
  invFun p := (p.1.1, p.2.1, p.1.2, p.2.2)
  map_add' := by intro a b; ext <;> rfl
  map_smul' := by intro c a; ext <;> rfl
  left_inv := by rintro ⟨x, y, u, v⟩; rfl
  right_inv := by rintro ⟨⟨x, u⟩, ⟨y, v⟩⟩; rfl

/-- **The inclusion of the flattened first sheet's plane**: `(x,u) ↦ (x, 0, u, 0)`. -/
def incLM (k : ℕ) : (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] Work.Drive.Whitney.Mdl k :=
  (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).prod
    ((0 : (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] ℝ).prod
      ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).prod
        (0 : (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))))

@[simp] theorem incLM_apply (k : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    incLM k p = (p.1, 0, p.2, 0) := rfl

/-- **The jet of a graph `(x,v) ↦ (x, y, u, v)` over `(x,v)`**: the linear map
`(x,v) ↦ (x, yx * x + b v, x • a + D v, v)`, whose `y`-component along the `x`-direction is
`yx = ∂_x y` (the derivative of the height of the *core* in the `x`-direction). -/
def graphLM (k : ℕ) (yx : ℝ) (b : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ℝ)
    (a : EuclideanSpace ℝ (Fin k)) (D : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] Work.Drive.Whitney.Mdl k :=
  (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).prod
    (((yx • (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))))
        + (b.comp (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))))).prod
      ((((LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).smulRight a)
          + (D.comp (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))))).prod
        (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k)))))

@[simp] theorem graphLM_apply (k : ℕ) (yx : ℝ) (b : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ℝ)
    (a : EuclideanSpace ℝ (Fin k)) (D : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    graphLM k yx b a D p = (p.1, yx * p.1 + b p.2, p.1 • a + D p.2, p.2) := rfl

end Work.Drive.PushDisc
