import Mathlib
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.simplexNorthCap_contractible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The closed star of the last vertex of `∂Δⁿ⁺¹` is contractible

The open star of the last vertex `v` of `∂Δⁿ⁺¹` (the "north cap") is contractible.  In this file
we prove the same for its **closed star**

`simplexStar n = {x ∈ ∂Δⁿ⁺¹ | ∃ i : Fin (n+1), x_weights (castSucc i) = 0}`,

the union of the facets of `∂Δⁿ⁺¹` opposite the vertices other than `v`.  This is the closed
neighbourhood of `v` in `∂Δⁿ⁺¹`; it is the cone with apex `v` over its link `∂F_v`, hence a closed
`n`-disk and in particular contractible.

As for the north cap, the argument is carried out on the barycentric coordinate vectors of the
points of `∂Δⁿ⁺¹`, where the contraction is the straight line homotopy to the apex `v`: the closed
star is *star shaped* with respect to `v`, because `v` has all coordinates other than the last
equal to `0`, and any convex combination `t • v + (1 - t) • w` therefore keeps vanishing the
coordinate that was zero for `w`.

## Main result

* `Work.HomologyExtra.simplexStar_contractible`
-/

namespace Work.HomologyExtra

open Topology

noncomputable section

/-- The closed star of the last vertex of `∂Δⁿ⁺¹`, described in barycentric coordinates: the
coordinates are non-negative, sum to `1`, and some coordinate other than the last vanishes.

This is the set of barycentric coordinate vectors of the points of `simplexStar n`. -/
def starWeightSet (n : ℕ) : Set (Fin (n + 2) → ℝ) :=
  {f | (∀ i, 0 ≤ f i) ∧ (∑ i, f i = 1) ∧ ∃ i : Fin (n + 1), f (Fin.castSucc i) = 0}

/-- The barycentric coordinate vector of the last vertex of `Δⁿ⁺¹`: a `1` at the last coordinate
and `0` elsewhere.  It is the apex of the cone that the closed star is. -/
abbrev starApex (n : ℕ) : Fin (n + 2) → ℝ :=
  fun j => if j = Fin.last (n + 1) then 1 else 0

/-- The barycentric coordinates of a point of `∂Δⁿ⁺¹` lie in `starWeightSet n` exactly when the
point lies in the closed star. -/
theorem starWeights_preimage (n : ℕ) :
    northCapWeights n ⁻¹' starWeightSet n = simplexStar n := by
  ext x
  simp only [Set.mem_preimage, starWeightSet, simplexStar, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, -, i, hi⟩
    exact ⟨i, hi⟩
  · intro h
    exact ⟨fun i => Convexity.StdSimplex.weights_nonneg (w := (x : simplex (n + 1))) i,
      Convexity.StdSimplex.total_of_fintype (x : simplex (n + 1)), h⟩

/-- Every element of `starWeightSet n` is the barycentric coordinate vector of a point of
`∂Δⁿ⁺¹`. -/
theorem starWeightSet_subset_range (n : ℕ) :
    starWeightSet n ⊆ Set.range (northCapWeights n) := by
  rintro f ⟨hfnn, hfsum, i, hi⟩
  have hmem : f ∈ Set.range
      (fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => fun i => t.weights i) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨hfnn, hfsum⟩
  obtain ⟨w, hw⟩ := hmem
  refine ⟨⟨w, ?_⟩, ?_⟩
  · exact ⟨Fin.castSucc i, by rw [show w.weights (Fin.castSucc i) = f (Fin.castSucc i) from
      congrFun hw (Fin.castSucc i), hi]⟩
  · exact hw

/-- The barycentric coordinate vector of the last vertex belongs to the closed star. -/
theorem starApex_mem (n : ℕ) : starApex n ∈ starWeightSet n := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp only [starApex]
    split <;> norm_num
  · simp [starApex]
  · refine ⟨0, ?_⟩
    have hne : (Fin.castSucc 0 : Fin (n + 2)) ≠ Fin.last (n + 1) :=
      (Fin.castSucc_lt_last (0 : Fin (n + 1))).ne
    simp [starApex, hne]

/-- The closed star of `∂Δⁿ⁺¹` is non-empty. -/
theorem starWeightSet_nonempty (n : ℕ) : (starWeightSet n).Nonempty :=
  ⟨starApex n, starApex_mem n⟩

/-- The set `starWeightSet n` is star shaped with respect to the barycentric coordinate vector of
the last vertex: the segment from any point of the closed star to that vertex stays in the closed
star. -/
theorem starConvex_starWeightSet (n : ℕ) :
    StarConvex ℝ (starApex n) (starWeightSet n) := by
  intro f hf a b ha hb hab
  obtain ⟨hfnn, hfsum, i, hi⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hvj : 0 ≤ starApex n j := by
      simp only [starApex]
      split <;> norm_num
    have := hfnn j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · have hvsum : ∑ j : Fin (n + 2), starApex n j = 1 := by simp [starApex]
    have hsplit : ∑ j : Fin (n + 2), (a * starApex n j + b * f j)
        = a * (∑ j : Fin (n + 2), starApex n j) + b * (∑ j : Fin (n + 2), f j) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsplit, hvsum, hfsum, mul_one, mul_one, hab]
  · refine ⟨i, ?_⟩
    have hv0 : starApex n (Fin.castSucc i) = 0 := by
      have hne : (Fin.castSucc i : Fin (n + 2)) ≠ Fin.last (n + 1) :=
        (Fin.castSucc_lt_last i).ne
      simp [starApex, hne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv0, hi, mul_zero, zero_add]

/-- **The closed star of the last vertex of `∂Δⁿ⁺¹` is contractible.** -/
theorem simplexStar_contractible (n : ℕ) :
    ContractibleSpace (TopCat.of (Work.HomologyExtra.simplexStar n)) := by
  have hc : ContractibleSpace ↥(starWeightSet n) :=
    (starConvex_starWeightSet n).contractibleSpace (starWeightSet_nonempty n)
  have h : ↥(simplexStar n) ≃ₜ ↥(starWeightSet n) :=
    (Homeomorph.setCongr (starWeights_preimage n)).symm.trans
      ((isEmbedding_northCapWeights n).homeomorphOfSubsetRange
        (starWeightSet_subset_range n))
  show ContractibleSpace ↥(simplexStar n)
  exact (Homeomorph.contractibleSpace_iff h).mpr hc

end

end Work.HomologyExtra
