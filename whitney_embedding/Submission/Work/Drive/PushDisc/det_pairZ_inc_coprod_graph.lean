import Mathlib
import Submission.Work.Drive.PushDisc.asymSignDefs

/-!
# The signed determinant of a crossing: `det (pairZ ∘ (incLM coprod graphLM)) = yx`

`Work.Drive.PushDisc.asymSignDefs` sets up the three linear maps of the model crossing:

* `pairZ k : Mdl k ≃ₗ (ℝ × E) × (ℝ × E)`, `(x,y,u,v) ↦ ((x,u),(y,v))` — the pairing of the model
  space with the two blocks that `Work.Projection.pairEquiv` splits into (`E = EuclideanSpace ℝ (Fin k)`);
* `incLM k : (ℝ × E) →ₗ Mdl k`, `(x,u) ↦ (x,0,u,0)` — the flattened first sheet;
* `graphLM k yx b a D : (ℝ × E) →ₗ Mdl k`, `(x,v) ↦ (x, yx*x + b v, x•a + D v, v)` — the jet of a
  graph over `(x,v)`, whose `y`-component along the `x`-direction is the number `yx = ∂_x y`.

Evaluating the two sheets on the two base variables `(p, q) ∈ (ℝ × E) × (ℝ × E)` gives

    pairZ (incLM p + graphLM q) = (p + g₁ q, g₂ q),

with `g₁ (x,v) = (x, x•a + D v)` (the base part of the graph jet) and `g₂ (x,v) = (yx*x + b v, v)`
(the height part).  The endomorphism of `(ℝ × E) × (ℝ × E)` so obtained is *block upper triangular*
with identity diagonal in its first block and `g₂` in its second, so its determinant is the
determinant of `g₂`; and `g₂` is itself block upper triangular with diagonal `x ↦ yx*x` and the
identity of `E`, hence has determinant `yx`.  The resulting identity

    LinearMap.det (pairZ ∘ (incLM coprod graphLM yx b a D)) = yx

is the *content* of the sign derivation: the signed determinant of a model crossing is proportional
to `∂_x y` of the second sheet, with a constant of proportionality independent of the data.

## Provenance of `yx ≠ 0`

Nothing here needs `yx ≠ 0`: the identity is polynomial in the data, so it also covers the
degenerate case in which the two sheets are tangent (`yx = 0`, determinant zero).

## Main results

* `det_prod_block` — the general brick: the determinant of the block-triangular endomorphism
  `(x, y) ↦ (f x + h y, g y)` of a product `X × Y` is `det f * det g` (the `f = id` case is the
  determinant of a "shear", which is `1`);
* `det_pairZ_inc_coprod_graph` — the target identity.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff

/-- **The determinant of a block-triangular endomorphism of a product.**

For finite free real modules `X`, `Y` and linear maps `f : X → X`, `h : Y → X`, `g : Y → Y`, the
endomorphism of `X × Y` given by `(x, y) ↦ (f x + h y, g y)` has determinant `det f * det g`.

(Proof: in the basis `bX.prod bY` — whose index type is the *sum* `ι ⊕ κ` — the matrix is the block
matrix `fromBlocks (toMatrix f) (toMatrix h) 0 (toMatrix g)`, so `Matrix.det_fromBlocks_zero₂₁`
applies.  This is the general form of the two shear computations
`Work.Whitney.CutPush.det_shear_lower` / `det_shear_upper`.) -/
theorem det_prod_block {X Y : Type*} [AddCommGroup X] [Module ℝ X] [Module.Finite ℝ X]
    [Module.Free ℝ X] [AddCommGroup Y] [Module ℝ Y] [Module.Finite ℝ Y] [Module.Free ℝ Y]
    (f : X →ₗ[ℝ] X) (h : Y →ₗ[ℝ] X) (g : Y →ₗ[ℝ] Y) :
    LinearMap.det (((f.comp (LinearMap.fst ℝ X Y)) + (h.comp (LinearMap.snd ℝ X Y))).prod
        (g.comp (LinearMap.snd ℝ X Y))) = LinearMap.det f * LinearMap.det g := by
  classical
  let bX := Module.Free.chooseBasis ℝ X
  let bY := Module.Free.chooseBasis ℝ Y
  have hmat : LinearMap.toMatrix (bX.prod bY) (bX.prod bY)
      (((f.comp (LinearMap.fst ℝ X Y)) + (h.comp (LinearMap.snd ℝ X Y))).prod
        (g.comp (LinearMap.snd ℝ X Y)))
      = Matrix.fromBlocks (LinearMap.toMatrix bX bX f) (LinearMap.toMatrix bY bX h) 0
          (LinearMap.toMatrix bY bY g) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, LinearMap.prod_apply]
  rw [← LinearMap.det_toMatrix (bX.prod bY), hmat, Matrix.det_fromBlocks_zero₂₁,
    ← LinearMap.det_toMatrix bX, ← LinearMap.det_toMatrix bY]

/-- **The signed determinant of a crossing `det (pairZ ∘ (incLM coprod graphLM yx b a D))` is the
`x`-derivative `yx` of the height of the core of the second sheet.**

With `E = EuclideanSpace ℝ (Fin k)` and `P = ℝ × E`, the composite is the endomorphism
`(p, q) ↦ (p + g₁ q, g₂ q)` of `P × P`, where `g₁ (x,v) = (x, x•a + D v)` and
`g₂ (x,v) = (yx*x + b v, v)`; it is block triangular with diagonal blocks `id` and `g₂`, and `g₂` is
block triangular with diagonal blocks `x ↦ yx*x` and `id_E`.  Hence the determinant is `yx`. -/
theorem det_pairZ_inc_coprod_graph {k : ℕ} (yx : ℝ)
    (b : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ℝ) (a : EuclideanSpace ℝ (Fin k))
    (D : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    LinearMap.det ((pairZ k).toLinearMap.comp
      ((incLM k).coprod (graphLM k yx b a D))) = yx := by
  let E := EuclideanSpace ℝ (Fin k)
  let P := ℝ × E
  -- the base part and the height part of the graph jet
  set g1 : P →ₗ[ℝ] P :=
    (LinearMap.fst ℝ ℝ E).prod
      (((LinearMap.fst ℝ ℝ E).smulRight a) + (D.comp (LinearMap.snd ℝ ℝ E))) with hg1def
  set g2 : P →ₗ[ℝ] P :=
    (((LinearMap.mulLeft ℝ yx).comp (LinearMap.fst ℝ ℝ E)) +
      (b.comp (LinearMap.snd ℝ ℝ E))).prod (LinearMap.snd ℝ ℝ E) with hg2def
  have hg1 : ∀ (x : ℝ) (v : E), g1 (x, v) = (x, x • a + D v) := by
    intro x v
    show ((LinearMap.fst ℝ ℝ E).prod
      (((LinearMap.fst ℝ ℝ E).smulRight a) + (D.comp (LinearMap.snd ℝ ℝ E)))) (x, v) = _
    simp [LinearMap.prod_apply]
  have hg2 : ∀ (x : ℝ) (v : E), g2 (x, v) = (yx * x + b v, v) := by
    intro x v
    show ((((LinearMap.mulLeft ℝ yx).comp (LinearMap.fst ℝ ℝ E)) +
      (b.comp (LinearMap.snd ℝ ℝ E))).prod (LinearMap.snd ℝ ℝ E)) (x, v) = _
    simp [LinearMap.prod_apply, LinearMap.mulLeft_apply]
  -- the composite, evaluated on the two base variables
  have hM : (pairZ k).toLinearMap.comp ((incLM k).coprod (graphLM k yx b a D))
      = ((LinearMap.id.comp (LinearMap.fst ℝ P P)) + (g1.comp (LinearMap.snd ℝ P P))).prod
          (g2.comp (LinearMap.snd ℝ P P)) := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨p, q⟩
    rcases p with ⟨x, u⟩
    rcases q with ⟨y, v⟩
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.id_apply]
    rw [hg1 y v, hg2 y v]
    simp only [pairZ, incLM_apply, graphLM_apply, Prod.mk_add_mk, zero_add]
    rfl
  -- the determinant of the block-triangular map is `det g₂`
  rw [hM, det_prod_block, LinearMap.det_id, one_mul]
  -- and `g₂` is again block triangular, with diagonal `x ↦ yx*x` and `id_E`
  have hg2eq : g2 = (((LinearMap.mulLeft ℝ yx).comp (LinearMap.fst ℝ ℝ E)) +
      (b.comp (LinearMap.snd ℝ ℝ E))).prod
        ((LinearMap.id : E →ₗ[ℝ] E).comp (LinearMap.snd ℝ ℝ E)) := by
    rw [hg2def]
    simp
  rw [hg2eq, det_prod_block, LinearMap.det_mulLeft, LinearMap.det_id, mul_one]

end Work.Drive.PushDisc
