import Mathlib
import Submission.Work.HomologyExtra.SimplexFaceSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The face map `Δⁿ → F` is a homeomorphism onto the last face of `∂Δⁿ⁺¹`

Let `F = simplexLastFace n ⊆ ∂Δⁿ⁺¹` be the face of the boundary of the `(n+1)`-simplex opposite
its last vertex, i.e. the set of points whose last barycentric coordinate vanishes.  The face map
`faceToLastFaceFun n : Δⁿ → F` (the restriction to `Δⁿ` of the last face inclusion
`∂Δⁿ⁺¹ ⊇ F`) is a bijection, and both spaces carry the subspace topology of a standard simplex;
the content of this file is that the two topologies match, so that `faceToLastFaceFun n` is a
homeomorphism.

The inverse is written out explicitly using `Fin.predAbove`, which removes the (unused) hole at
the last vertex: it is the map

`invLastFaceFun n x = StdSimplex.map (Fin.predAbove (Fin.last n)) x`,

where `x : F` is regarded as a point of `Δⁿ⁺¹` with `n + 2` barycentric coordinates.  Since the
last coordinate of `x` vanishes, this is exactly "forget the last coordinate", which is inverse to
the face map.  The two identities

* `Fin.predAbove (Fin.last n) ∘ Fin.castSucc = id` (`Fin.predAbove_last_castSucc`), and
* `Fin.castSucc ∘ Fin.predAbove (Fin.last n) = id` away from the last vertex
  (`castSucc_predAbove_last_of_ne`)

translate into the two round-trip identities for the simplices (`map_predAbove_map_castSucc`,
`map_castSucc_map_predAbove`), and `StdSimplex.map` is continuous
(`Convexity.StdSimplex.continuous_map`), which gives the homeomorphism.
-/

namespace Work.HomologyExtra

noncomputable section

/-! ## Two identities for `Fin.predAbove` at the last vertex -/

/-- `predAbove` at the last vertex is a left inverse of `castSucc`: removing the last coordinate
of the `j`-th vertex coordinate of `Fin (n+2)` returns `j`. -/
theorem predAbove_last_comp_castSucc (n : ℕ) :
    (Fin.predAbove (Fin.last n)) ∘ (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) = id :=
  funext (fun _ => Fin.predAbove_last_castSucc)

/-- `castSucc ∘ predAbove (last n)` fixes every index other than the last one: away from the last
vertex, removing the last coordinate and reinserting a coordinate is the identity. -/
theorem castSucc_predAbove_last_of_ne {n : ℕ} {a : Fin (n + 2)} (ha : a ≠ Fin.last (n + 1)) :
    (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) (Fin.predAbove (Fin.last n) a) = a := by
  rw [Fin.predAbove_last_of_ne_last ha, Fin.castSucc_castPred]

/-! ## The two round trips at the level of standard simplices -/

/-- Forgetting the last coordinate after reinserting it is the identity on `Δⁿ`. -/
theorem map_predAbove_map_castSucc (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Convexity.StdSimplex.map (Fin.predAbove (Fin.last n))
      (Convexity.StdSimplex.map (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) w) = w := by
  rw [← Convexity.StdSimplex.map_comp w (Fin.castSucc : Fin (n + 1) → Fin (n + 2))
    (Fin.predAbove (Fin.last n))]
  rw [predAbove_last_comp_castSucc, Convexity.StdSimplex.map_id]

/-- Reinserting the last coordinate after forgetting it is the identity on the points of
`Δⁿ⁺¹` whose last coordinate vanishes. -/
theorem map_castSucc_map_predAbove (n : ℕ) (y : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (hy : y.weights (Fin.last (n + 1)) = 0) :
    Convexity.StdSimplex.map (Fin.castSucc : Fin (n + 1) → Fin (n + 2))
      (Convexity.StdSimplex.map (Fin.predAbove (Fin.last n)) y) = y := by
  apply Convexity.StdSimplex.ext
  rw [Convexity.StdSimplex.weights_map, Convexity.StdSimplex.weights_map,
    ← Finsupp.mapDomain_comp]
  have hcongr : y.weights.mapDomain
        ((Fin.castSucc : Fin (n + 1) → Fin (n + 2)) ∘ Fin.predAbove (Fin.last n))
      = y.weights.mapDomain (id : Fin (n + 2) → Fin (n + 2)) :=
    Finsupp.mapDomain_congr (v := y.weights)
      (f := (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) ∘ Fin.predAbove (Fin.last n)) (g := id)
      (fun a ha => by
        have ha' : y.weights a ≠ 0 := Finsupp.mem_support_iff.mp ha
        exact castSucc_predAbove_last_of_ne (fun h => ha' (by rw [h, hy])))
  rw [hcongr, Finsupp.mapDomain_id]

/-! ## The inverse of the face map -/

/-- **The inverse of the face map**: a point of the last face `F`, i.e. a point of `∂Δⁿ⁺¹` whose
last barycentric coordinate vanishes, regarded as a point of `Δⁿ` by deleting the last
coordinate. -/
noncomputable def invLastFaceFun (n : ℕ) (x : ↥(simplexLastFace n)) : ↥(simplex n) :=
  Convexity.StdSimplex.map (Fin.predAbove (Fin.last n))
    ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))

/-- The underlying point of `faceToLastFaceFun n w` is the last face map applied to `w`. -/
theorem faceToLastFaceFun_coe_eq (n : ℕ) (w : ↥(simplex n)) :
    (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
        simplex (n + 1))
      = (simplexFace n (Fin.last (n + 1))) w := rfl

/-- `invLastFaceFun` is a left inverse of the face map. -/
theorem invLastFaceFun_faceToLastFaceFun (n : ℕ) (w : ↥(simplex n)) :
    invLastFaceFun n (faceToLastFaceFun n w) = w := by
  unfold invLastFaceFun
  rw [faceToLastFaceFun_coe_eq, simplexFace_last_apply]
  exact map_predAbove_map_castSucc n w

/-- `invLastFaceFun` is a right inverse of the face map. -/
theorem faceToLastFaceFun_invLastFaceFun (n : ℕ) (x : ↥(simplexLastFace n)) :
    faceToLastFaceFun n (invLastFaceFun n x) = x := by
  unfold invLastFaceFun
  apply Subtype.ext
  apply Subtype.ext
  rw [faceToLastFaceFun_coe_eq, simplexFace_last_apply]
  exact map_castSucc_map_predAbove n _ (mem_simplexLastFace.mp x.2)

/-- `invLastFaceFun` is continuous: it is induced by the continuous map `StdSimplex.map`. -/
theorem continuous_invLastFaceFun (n : ℕ) : Continuous (invLastFaceFun n) := by
  unfold invLastFaceFun
  exact (Convexity.StdSimplex.continuous_map ℝ (Fin.predAbove (Fin.last n))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- **The face map `Δⁿ → F` as a homeomorphism**, `F = simplexLastFace n` being the face of
`∂Δⁿ⁺¹` opposite its last vertex. -/
noncomputable def simplexFaceHomeo (n : ℕ) :
    (simplex n) ≃ₜ TopCat.of (simplexLastFace n) where
  toFun := faceToLastFaceFun n
  invFun := invLastFaceFun n
  left_inv := invLastFaceFun_faceToLastFaceFun n
  right_inv := faceToLastFaceFun_invLastFaceFun n
  continuous_toFun := continuous_faceToLastFaceFun n
  continuous_invFun := continuous_invLastFaceFun n

theorem simplexFaceHomeo_exists (n : ℕ) :
    ∃ e : Work.HomologyExtra.simplex n ≃ₜ TopCat.of (Work.HomologyExtra.simplexLastFace n),
      ∀ w : Work.HomologyExtra.simplex n, e w = Work.HomologyExtra.faceToLastFaceFun n w := by
  exact ⟨simplexFaceHomeo n, fun _ => rfl⟩

end

end Work.HomologyExtra
