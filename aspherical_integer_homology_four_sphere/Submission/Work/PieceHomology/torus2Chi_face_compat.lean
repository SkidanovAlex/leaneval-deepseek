/-
# Face compatibility of the characteristic maps of the `Δ`-structure of the `2`-torus

The characteristic maps `torus2ChiCls k σ : Δ^k → T²` of
`Submission/Work/PieceHomology/Torus2Chi.lean` (one vertex, the three loops `a, b, c` and the two
triangles `T₀ = [b,c,a]`, `T₁ = [a,c,b]`) are the geometric half of the realization of the
`Δ`-complex `torus2DeltaCx`.  This file proves that they are compatible with the face maps of
`torus2DeltaCx`, i.e. that the singular simplices `torus2Chi k σ` form a `DeltaSimplexMap`:

```
torus2Chi k (torus2Face σ i) = singFace i (torus2Chi (k+1) σ) .
```

The two non-vacuous degrees are `k = 0` (`k+1 = 1`) and `k = 1` (`k+1 = 2`); in every higher
degree there are no simplices at all.  Everything therefore reduces to the explicit weight
computations `chiV z = chiE σ (map i.succAbove z)` and
`chiE (torus2TriFace σ i) z = chiT σ (map i.succAbove z)` carried out below.
-/
import Mathlib
import Submission.Work.PieceHomology.Torus2Chi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits
open Convexity
open scoped Topology

open Work.DeltaHomology

namespace Work.PieceHomology

noncomputable section

/-! ## §1  Weights of the face inclusions `StdSimplex.map i.succAbove`

The face `i` of `Δ^{k+1}` is the image of the face inclusion `i.succAbove : Fin (k+1) → Fin (k+2)`,
and the barycentric coordinates of the image point are those of the source point at the vertices
that survive, `0` at the dropped vertex `i`. -/

/-- The weights of a simplex pushed forward along an injective map, read at a point in the
image. -/
theorem stdSimplex_weights_map_succAbove {k : ℕ} (i : Fin (k + 2))
    (z : StdSimplex ℝ (Fin (k + 1))) (a : Fin (k + 1)) :
    (StdSimplex.map i.succAbove z).weights (i.succAbove a) = z.weights a := by
  rw [StdSimplex.weights_map i.succAbove z,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]

/-- The weight at the dropped vertex `i` of a face inclusion is zero. -/
theorem stdSimplex_weights_map_succAbove_self {k : ℕ} (i : Fin (k + 2))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    (StdSimplex.map i.succAbove z).weights i = 0 := by
  rw [StdSimplex.weights_map i.succAbove z]
  exact Finsupp.mapDomain_of_notMem_range z.weights i (by simp [Set.mem_range, Fin.succAbove_ne])

/-! ## §2  The two non-vacuous degrees -/

/-- **Degree `0`.**  The unique vertex of `torus2DeltaCx` is compatible with the three edges: the
image of `Δ⁰` under `chiV` and under any edge (precomposed with the corresponding face inclusion)
is the base point `(0,0)`. -/
theorem chiV_eq_chiE_face (σ : Fin 3) (i : Fin 2) (z : StdSimplex ℝ (Fin 1)) :
    chiV z = chiE σ (StdSimplex.map i.succAbove z) := by
  fin_cases σ <;> fin_cases i <;>
    simp only [chiE, chiV, ContinuousMap.coe_mk, ContinuousMap.const_apply, chiA, chiB, chiC, tpt,
      Fin.reduceFinMk, Matrix.cons_val]
  · have h1 : (StdSimplex.map (0 : Fin 2).succAbove z).weights 1 = z.weights 0 := by
      rw [show (1 : Fin 2) = (0 : Fin 2).succAbove (0 : Fin 1) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 2) z 0]
    have h2 : z.weights 0 = 1 := StdSimplex.weights_apply_eq_one z 0
    rw [h1, h2, AddCircle.coe_period]
  · have h1 : (StdSimplex.map (1 : Fin 2).succAbove z).weights 1 = 0 :=
      stdSimplex_weights_map_succAbove_self (1 : Fin 2) z
    rw [h1, AddCircle.coe_zero]
  · have h1 : (StdSimplex.map (0 : Fin 2).succAbove z).weights 1 = z.weights 0 := by
      rw [show (1 : Fin 2) = (0 : Fin 2).succAbove (0 : Fin 1) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 2) z 0]
    have h2 : z.weights 0 = 1 := StdSimplex.weights_apply_eq_one z 0
    rw [h1, h2, AddCircle.coe_period]
  · have h1 : (StdSimplex.map (1 : Fin 2).succAbove z).weights 1 = 0 :=
      stdSimplex_weights_map_succAbove_self (1 : Fin 2) z
    rw [h1, AddCircle.coe_zero]
  · have h1 : (StdSimplex.map (0 : Fin 2).succAbove z).weights 1 = z.weights 0 := by
      rw [show (1 : Fin 2) = (0 : Fin 2).succAbove (0 : Fin 1) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 2) z 0]
    have h2 : z.weights 0 = 1 := StdSimplex.weights_apply_eq_one z 0
    rw [h1, h2, AddCircle.coe_period]
  · have h1 : (StdSimplex.map (1 : Fin 2).succAbove z).weights 1 = 0 :=
      stdSimplex_weights_map_succAbove_self (1 : Fin 2) z
    rw [h1, AddCircle.coe_zero]

/-- **Degree `1`.**  The faces of the two triangles are the three edges: on the face opposite to
the vertex `i` of `Δ²`, `chiT0` (resp. `chiT1`) restricts to the edge prescribed by `torus2TriFace`. -/
theorem chiE_triFace_eq_chiT (σ : Fin 2) (i : Fin 3) (z : StdSimplex ℝ (Fin 2)) :
    chiE (torus2TriFace σ i) z = chiT σ (StdSimplex.map i.succAbove z) := by
  fin_cases σ <;> fin_cases i <;>
    simp only [torus2TriFace, chiE, chiT, chiA, chiB, chiC, chiT0, chiT1, tpt,
      Fin.reduceFinMk, Matrix.cons_val, ContinuousMap.coe_mk]
  · have h1 : (StdSimplex.map (0 : Fin 3).succAbove z).weights 1 = z.weights 0 := by
      rw [show (1 : Fin 3) = (0 : Fin 3).succAbove (0 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 3) z 0]
    have h2 : (StdSimplex.map (0 : Fin 3).succAbove z).weights 2 = z.weights 1 := by
      rw [show (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 3) z 1]
    rw [h1, h2, StdSimplex.total_fin_two z, AddCircle.coe_period]
  · have h1 : (StdSimplex.map (1 : Fin 3).succAbove z).weights 1 = 0 :=
      stdSimplex_weights_map_succAbove_self (1 : Fin 3) z
    have h2 : (StdSimplex.map (1 : Fin 3).succAbove z).weights 2 = z.weights 1 := by
      rw [show (2 : Fin 3) = (1 : Fin 3).succAbove (1 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (1 : Fin 3) z 1]
    rw [h1, h2, zero_add]
  · have h1 : (StdSimplex.map (2 : Fin 3).succAbove z).weights 1 = z.weights 1 := by
      rw [show (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (2 : Fin 3) z 1]
    have h2 : (StdSimplex.map (2 : Fin 3).succAbove z).weights 2 = 0 :=
      stdSimplex_weights_map_succAbove_self (2 : Fin 3) z
    rw [h1, h2, add_zero, AddCircle.coe_zero]
  · have h1 : (StdSimplex.map (0 : Fin 3).succAbove z).weights 1 = z.weights 0 := by
      rw [show (1 : Fin 3) = (0 : Fin 3).succAbove (0 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 3) z 0]
    have h2 : (StdSimplex.map (0 : Fin 3).succAbove z).weights 2 = z.weights 1 := by
      rw [show (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (0 : Fin 3) z 1]
    rw [h1, h2, StdSimplex.total_fin_two z, AddCircle.coe_period]
  · have h1 : (StdSimplex.map (1 : Fin 3).succAbove z).weights 1 = 0 :=
      stdSimplex_weights_map_succAbove_self (1 : Fin 3) z
    have h2 : (StdSimplex.map (1 : Fin 3).succAbove z).weights 2 = z.weights 1 := by
      rw [show (2 : Fin 3) = (1 : Fin 3).succAbove (1 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (1 : Fin 3) z 1]
    rw [h1, h2, zero_add]
  · have h1 : (StdSimplex.map (2 : Fin 3).succAbove z).weights 1 = z.weights 1 := by
      rw [show (1 : Fin 3) = (2 : Fin 3).succAbove (1 : Fin 2) from rfl,
        stdSimplex_weights_map_succAbove (2 : Fin 3) z 1]
    have h2 : (StdSimplex.map (2 : Fin 3).succAbove z).weights 2 = 0 :=
      stdSimplex_weights_map_succAbove_self (2 : Fin 3) z
    rw [h1, h2, add_zero, AddCircle.coe_zero]

/-! ## §3  The characteristic maps, with the face compatibilities -/

/-- **Face compatibility of the characteristic maps at the level of points of the standard
simplex.**  For every degree `k`, simplex `σ`, face `i` and interior point `z` of `Δ^k`, the
characteristic map of the face is the restriction of the characteristic map of `σ`. -/
theorem torus2ChiCls_face_apply {k : ℕ} (σ : Fin (torus2Card (k + 1))) (i : Fin (k + 2))
    (z : StdSimplex ℝ (Fin (k + 1))) :
    torus2ChiCls k (torus2Face σ i) z
      = torus2ChiCls (k + 1) σ (StdSimplex.map i.succAbove z) := by
  match k with
  | 0 =>
    show chiV z = chiE σ (StdSimplex.map i.succAbove z)
    exact chiV_eq_chiE_face σ i z
  | 1 =>
    show chiE (torus2TriFace σ i) z = chiT σ (StdSimplex.map i.succAbove z)
    exact chiE_triFace_eq_chiT σ i z
  | (j + 2) => exact Fin.elim0 σ

/-- **Face compatibility of the singular simplices of the `2`-torus.**  The characteristic maps
`torus2Chi` of the minimal `Δ`-structure of `T²` commute with the face maps: the `i`-th face of
the singular simplex of `σ` is the singular simplex of the `i`-th face of `σ`. -/
theorem torus2Chi_face_compat {k : ℕ} (σ : Fin (Work.PieceHomology.torus2Card (k + 1)))
    (i : Fin (k + 2)) :
    Work.PieceHomology.torus2Chi k (Work.PieceHomology.torus2Face σ i) =
      Work.DeltaHomology.singFace i (Work.PieceHomology.torus2Chi (k + 1) σ) := by
  apply (TopCat.toSSetObjEquiv Torus2Space (Opposite.op (SimplexCategory.mk k))).injective
  ext z j
  erw [toSSetObjEquiv_torus2Chi, singFace, TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_torus2Chi]
  exact congrFun (torus2ChiCls_face_apply σ i z) j

end

end Work.PieceHomology
