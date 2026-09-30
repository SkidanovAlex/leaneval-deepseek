import Mathlib
import ChallengeDeps
import Submission.Work.Homology.All
import Submission.Work.HomologyExtra.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The standard simplex as a "corner", and its boundary as the boundary of the corner

The standard simplex `Δⁿ = Convexity.StdSimplex ℝ (Fin (n+1))` is homeomorphic to the
**corner**

`cornerSimplex n = {y : ℝⁿ | y ≥ 0, ∑ᵢ yᵢ ≤ 1}`

(delete the last barycentric coordinate).  Under this correspondence the boundary `∂Δⁿ` (the
points with a vanishing barycentric coordinate) corresponds to the *topological* boundary
`frontier (cornerSimplex n)` of the corner, which is the boundary of a compact convex body with
nonempty interior.  Since any two compact convex bodies with nonempty interior are homeomorphic
(Minkowski functional, Mathlib's `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`),
this reduces the simplex pair `(Δⁿ, ∂Δⁿ)` to the disc pair `(Dⁿ, Sⁿ⁻¹)`.

## Main definitions

* `Work.HomologyExtra.cornerSimplex n` — the corner model of `Δⁿ`;
* `Work.HomologyExtra.cornerWeights`, `cornerOfSimplex` — the two coordinate maps;
* `Work.HomologyExtra.simplexCornerHomeo n` — the homeomorphism `Δⁿ ≃ₜ cornerSimplex n`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The corner model of the standard `n`-simplex**: the set of vectors of `ℝⁿ` with
non-negative coordinates and coordinate sum at most `1`.  It is the image of `Δⁿ` under the map
which forgets the last barycentric coordinate; it is a compact convex body of `ℝⁿ` containing the
origin in its interior (for `n ≥ 1`), with boundary `{∑ yᵢ = 1} ∪ ⋃ᵢ {yᵢ = 0}`. -/
def cornerSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

@[simp]
theorem mem_cornerSimplex (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ cornerSimplex n ↔ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1 := Iff.rfl

/-- The barycentric coordinates of the point of `Δⁿ⁺¹` associated with a point of the corner: the
given coordinates, together with `1 - ∑ᵢ yᵢ` in the last coordinate. -/
def cornerWeights (n : ℕ) (y : ↥(cornerSimplex n)) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 - ∑ i, (y : EuclideanSpace ℝ (Fin n)) i) (fun i => (y : EuclideanSpace ℝ (Fin n)) i)

theorem cornerWeights_last (n : ℕ) (y : ↥(cornerSimplex n)) :
    cornerWeights n y (Fin.last n) = 1 - ∑ i, (y : EuclideanSpace ℝ (Fin n)) i := by
  simp [cornerWeights]

theorem cornerWeights_castSucc (n : ℕ) (y : ↥(cornerSimplex n)) (i : Fin n) :
    cornerWeights n y (Fin.castSucc i) = (y : EuclideanSpace ℝ (Fin n)) i := by
  simp [cornerWeights]

theorem cornerWeights_nonneg (n : ℕ) (y : ↥(cornerSimplex n)) (j : Fin (n + 1)) :
    0 ≤ cornerWeights n y j := by
  refine Fin.lastCases ?_ ?_ j
  · rw [cornerWeights_last]; linarith [y.2.2]
  · intro i; rw [cornerWeights_castSucc]; exact y.2.1 i

theorem cornerWeights_sum (n : ℕ) (y : ↥(cornerSimplex n)) :
    ∑ j, cornerWeights n y j = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [cornerWeights_last, cornerWeights_castSucc]
  ring

/-- The standard simplex element with prescribed coordinates. -/
def simplexOfWeights {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i) (h2 : ∑ i, g i = 1) :
    Convexity.StdSimplex ℝ (Fin N) :=
  ⟨Finsupp.equivFunOnFinite.symm g, fun i => by simpa using h1 i,
    by simpa [Finsupp.sum_fintype] using h2⟩

theorem simplexOfWeights_weights {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i)
    (h2 : ∑ i, g i = 1) (i : Fin N) :
    (simplexOfWeights g h1 h2).weights i = g i := by
  simp [simplexOfWeights]

/-- **The inverse coordinate map**: a point of the corner determines a point of `Δⁿ` whose first
`n` barycentric coordinates are its coordinates and whose last one is `1 - ∑ᵢ yᵢ`. -/
def simplexOfCorner (n : ℕ) (y : ↥(cornerSimplex n)) : Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  simplexOfWeights (cornerWeights n y) (cornerWeights_nonneg n y) (cornerWeights_sum n y)

theorem simplexOfCorner_weights (n : ℕ) (y : ↥(cornerSimplex n)) (j : Fin (n + 1)) :
    (simplexOfCorner n y).weights j = cornerWeights n y j :=
  simplexOfWeights_weights _ _ _ j

/-- The coordinate map `Δⁿ → cornerSimplex n`, forgetting the last barycentric coordinate. -/
def cornerOfSimplex (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => w.weights (Fin.castSucc i))

theorem cornerOfSimplex_apply (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin n) :
    cornerOfSimplex n w i = w.weights (Fin.castSucc i) := rfl

theorem cornerOfSimplex_mem (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    cornerOfSimplex n w ∈ cornerSimplex n := by
  constructor
  · intro i; rw [cornerOfSimplex_apply]; exact w.weights_nonneg _
  · have ht : ∑ j : Fin (n + 1), w.weights j = 1 := w.total_of_fintype
    have h := Fin.sum_univ_castSucc (fun j : Fin (n + 1) => w.weights j)
    have h2 : ∑ i : Fin n, w.weights (Fin.castSucc i) = 1 - w.weights (Fin.last n) := by linarith
    simp only [cornerOfSimplex_apply]
    linarith [w.weights_nonneg (Fin.last n)]

theorem cornerOfSimplex_simplexOfCorner (n : ℕ) (y : ↥(cornerSimplex n)) :
    cornerOfSimplex n (simplexOfCorner n y) = (y : EuclideanSpace ℝ (Fin n)) := by
  apply PiLp.ext
  intro i
  rw [cornerOfSimplex_apply, simplexOfCorner_weights, cornerWeights_castSucc]

theorem simplexOfCorner_cornerOfSimplex (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexOfCorner n ⟨cornerOfSimplex n w, cornerOfSimplex_mem n w⟩ = w := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  refine Fin.lastCases ?_ ?_ j
  · rw [simplexOfCorner_weights, cornerWeights_last]
    have ht : ∑ j : Fin (n + 1), w.weights j = 1 := w.total_of_fintype
    have h := Fin.sum_univ_castSucc (fun j : Fin (n + 1) => w.weights j)
    simp only [cornerOfSimplex_apply]
    linarith
  · intro i
    rw [simplexOfCorner_weights, cornerWeights_castSucc, cornerOfSimplex_apply]

theorem continuous_cornerOfSimplex (n : ℕ) : Continuous (cornerOfSimplex n) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp ?_
  exact continuous_pi (fun i => Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i))

theorem continuous_cornerOfSimplexPair (n : ℕ) :
    Continuous fun w => (⟨cornerOfSimplex n w, cornerOfSimplex_mem n w⟩ : ↥(cornerSimplex n)) :=
  Continuous.subtype_mk (continuous_cornerOfSimplex n) _

theorem continuous_simplexOfCorner (n : ℕ) : Continuous (simplexOfCorner n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun y : ↥(cornerSimplex n) => (simplexOfCorner n y).weights j)
  rw [show (fun y : ↥(cornerSimplex n) => (simplexOfCorner n y).weights j) =
      (fun y => cornerWeights n y j) from funext fun y => simplexOfCorner_weights n y j]
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun y : ↥(cornerSimplex n) => cornerWeights n y (Fin.last n)) =
        (fun y : ↥(cornerSimplex n) => 1 - ∑ i, (y : EuclideanSpace ℝ (Fin n)) i) from
      funext fun y => cornerWeights_last n y]
    exact continuous_const.sub (continuous_finsetSum _ fun i _ =>
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val)
  · intro i
    rw [show (fun y : ↥(cornerSimplex n) => cornerWeights n y (Fin.castSucc i)) =
        (fun y : ↥(cornerSimplex n) => (y : EuclideanSpace ℝ (Fin n)) i) from
      funext fun y => cornerWeights_castSucc n y i]
    exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val

/-- **The homeomorphism between the standard `n`-simplex and the corner**: the identity on the
first `n` barycentric coordinates. -/
noncomputable def simplexCornerHomeo (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ ↥(cornerSimplex n) where
  toFun := fun w => ⟨cornerOfSimplex n w, cornerOfSimplex_mem n w⟩
  invFun := simplexOfCorner n
  left_inv := fun w => simplexOfCorner_cornerOfSimplex n w
  right_inv := fun y => Subtype.ext (cornerOfSimplex_simplexOfCorner n y)
  continuous_toFun := continuous_cornerOfSimplexPair n
  continuous_invFun := continuous_simplexOfCorner n

@[simp]
theorem simplexCornerHomeo_apply_coe (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ((simplexCornerHomeo n w : ↥(cornerSimplex n)) : EuclideanSpace ℝ (Fin n)) =
      cornerOfSimplex n w := rfl

theorem simplexCornerHomeo_apply (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (i : Fin n) :
    ((simplexCornerHomeo n w : ↥(cornerSimplex n)) : EuclideanSpace ℝ (Fin n)) i =
      w.weights (Fin.castSucc i) :=
  cornerOfSimplex_apply n w i


/-- A homeomorphism of spaces which carries the subset `A` onto the subset `B`, as a map of
pairs. -/
def pairHomOfHomeomorph {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (he : ∀ x : X, x ∈ A ↔ e x ∈ B) : Work.Homology.PairHom X Y A B where
  hom := Work.Homology.homeomorphTopCatHom e
  mapsTo := fun x hx => (he x).mp hx

end

end Work.HomologyExtra
