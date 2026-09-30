import Mathlib
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.SimplexFaceSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The face of `∂Δⁿ⁺¹` opposite its last vertex is contractible

The face `A = simplexLastFace n = {x ∈ ∂Δⁿ⁺¹ | x_last = 0}` is the image of the standard
`n`-simplex `Δⁿ` under the last face map, which is a closed embedding with image exactly `A`.
The inverse `lastFaceToSimplexFun` reads off the non-last barycentric coordinates of a point of
`A`, and the two maps exhibit a homeomorphism `A ≅ Δⁿ` (`lastFaceHomeo`).  The weight vectors of
`Δⁿ` form the non-empty convex set `simplexWeightSet n ⊆ ℝ^{n+1}`, which is contractible; hence so
is `A`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

open Topology

/-! ## The weight set of the standard `n`-simplex -/

/-- The set of weight vectors of the standard `n`-simplex, as a subset of `ℝ^{n+1}`. -/
def simplexWeightSet (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

/-- The weight map of `Δⁿ` has range exactly `simplexWeightSet n`. -/
theorem range_weights_eq_simplexWeightSet (n : ℕ) :
    Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) => (⇑t.weights : Fin (n + 1) → ℝ))
      = simplexWeightSet n := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext f
  simp [simplexWeightSet, Set.mem_iInter]

/-- `simplexWeightSet n` is convex. -/
theorem convex_simplexWeightSet (n : ℕ) : Convex ℝ (simplexWeightSet n) := by
  intro f hf g hg a b ha hb hab
  simp only [simplexWeightSet, Set.mem_ofPred_eq] at hf hg ⊢
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hf.1 i
    have h2 := hg.1 i
    positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2, hg.2]
    rw [mul_one, mul_one, hab]

/-- `simplexWeightSet n` is non-empty. -/
theorem simplexWeightSet_nonempty (n : ℕ) : (simplexWeightSet n).Nonempty := by
  obtain ⟨t⟩ := (inferInstance : Nonempty (Convexity.StdSimplex ℝ (Fin (n + 1))))
  exact ⟨fun i => t.weights i, by
    rw [← range_weights_eq_simplexWeightSet]
    exact ⟨t, rfl⟩⟩

/-! ## The homeomorphism `Δⁿ ≅ simplexLastFace n` -/

/-- The weight function of a point of the last face, reindexed to `Fin (n+1)`. -/
def lastFaceToSimplexWeights (n : ℕ) (x : ↥(simplexLastFace n)) : Fin (n + 1) → ℝ :=
  fun j => ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.castSucc j)

theorem lastFaceToSimplexWeights_nonneg (n : ℕ) (x : ↥(simplexLastFace n)) :
    ∀ j, 0 ≤ lastFaceToSimplexWeights n x j :=
  fun j => Convexity.StdSimplex.weights_nonneg
    (w := ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))) (Fin.castSucc j)

theorem lastFaceToSimplexWeights_sum (n : ℕ) (x : ↥(simplexLastFace n)) :
    ∑ j, lastFaceToSimplexWeights n x j = 1 := by
  have htot := Convexity.StdSimplex.total_of_fintype
    (((x : ↥(boundarySpace (n + 1)))) : simplex (n + 1))
  rw [Fin.sum_univ_castSucc] at htot
  have hlast :
      (((x : ↥(boundarySpace (n + 1)))) : simplex (n + 1)).weights (Fin.last (n + 1)) = 0 :=
    mem_simplexLastFace.mp x.2
  have : ∑ j : Fin (n + 1),
      (((x : ↥(boundarySpace (n + 1)))) : simplex (n + 1)).weights (Fin.castSucc j) = 1 := by
    linarith
  simpa only [lastFaceToSimplexWeights] using this

/-- The inverse of the last-face homeomorphism: a point of the last face, as a point of `Δⁿ`. -/
def lastFaceToSimplexFun (n : ℕ) (x : ↥(simplexLastFace n)) : ↥(simplex n) :=
  mkSimplex (lastFaceToSimplexWeights n x)
    (lastFaceToSimplexWeights_nonneg n x) (lastFaceToSimplexWeights_sum n x)

theorem lastFaceToSimplexFun_weights (n : ℕ) (x : ↥(simplexLastFace n)) (j : Fin (n + 1)) :
    ((lastFaceToSimplexFun n x : ↥(simplex n)) : Convexity.StdSimplex ℝ (Fin (n + 1))).weights j
      = lastFaceToSimplexWeights n x j := by
  rw [lastFaceToSimplexFun, mkSimplex_weights]

/-- `simplexFace n (last)` applied to the coordinates of a point of `Δⁿ` is the corresponding
point of the last face. -/
theorem coe_faceToLastFaceFun (n : ℕ) (w : ↥(simplex n)) :
    (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
        simplex (n + 1))
      = (simplexFace n (Fin.last (n + 1))) w := rfl

theorem lastFaceToSimplexFun_faceToLastFaceFun (n : ℕ) (w : ↥(simplex n)) :
    lastFaceToSimplexFun n (faceToLastFaceFun n w) = w := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  rw [lastFaceToSimplexFun_weights]
  rw [show lastFaceToSimplexWeights n (faceToLastFaceFun n w) j
      = ((simplexFace n (Fin.last (n + 1))) w).weights (Fin.castSucc j) from by
    rw [lastFaceToSimplexWeights, coe_faceToLastFaceFun]]
  exact weights_simplexFace_last n w j

theorem faceToLastFaceFun_lastFaceToSimplexFun (n : ℕ) (x : ↥(simplexLastFace n)) :
    faceToLastFaceFun n (lastFaceToSimplexFun n x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [coe_faceToLastFaceFun]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [weights_simplexFace_last, lastFaceToSimplexFun_weights, lastFaceToSimplexWeights]
  · rw [weights_simplexFace_self, mem_simplexLastFace.mp x.2]

/-- **The last face of `∂Δⁿ⁺¹` is homeomorphic to the standard `n`-simplex** via the last face
map. -/
noncomputable def lastFaceHomeo (n : ℕ) : ↥(simplexLastFace n) ≃ₜ ↥(simplex n) where
  toFun := lastFaceToSimplexFun n
  invFun := faceToLastFaceFun n
  left_inv := faceToLastFaceFun_lastFaceToSimplexFun n
  right_inv := lastFaceToSimplexFun_faceToLastFaceFun n
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
    rw [continuous_pi_iff]
    intro j
    simp only [Function.comp_apply]
    have key : (fun x : ↥(simplexLastFace n) =>
        (((lastFaceToSimplexFun n x : ↥(simplex n)) : Convexity.StdSimplex ℝ (Fin (n + 1))).weights
          j)) = fun x => lastFaceToSimplexWeights n x j := by
      funext x
      rw [lastFaceToSimplexFun_weights]
    rw [key]
    simp only [lastFaceToSimplexWeights]
    fun_prop
  continuous_invFun := continuous_faceToLastFaceFun n

/-! ## Contractibility -/

theorem simplexLastFace_contractible (n : ℕ) :
    ContractibleSpace (TopCat.of (Work.HomologyExtra.simplexLastFace n)) := by
  have hc : ContractibleSpace ↥(simplexWeightSet n) :=
    (convex_simplexWeightSet n).contractibleSpace (simplexWeightSet_nonempty n)
  have h : ↥(simplexLastFace n) ≃ₜ ↥(simplexWeightSet n) :=
    (lastFaceHomeo n).trans
      (((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph).trans
        (Homeomorph.setCongr (range_weights_eq_simplexWeightSet n)))
  show ContractibleSpace ↥(simplexLastFace n)
  exact (Homeomorph.contractibleSpace_iff h).mpr hc

end

end Work.HomologyExtra
