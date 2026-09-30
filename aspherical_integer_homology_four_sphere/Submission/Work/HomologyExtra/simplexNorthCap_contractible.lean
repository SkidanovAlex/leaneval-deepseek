import Mathlib
import Submission.Work.HomologyExtra.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The north cap of `∂Δⁿ⁺¹` is contractible

The boundary `∂Δⁿ⁺¹` of the standard `(n+1)`-simplex is covered by the two caps
`simplexNorthCap n = {x | 0 < x.weights (Fin.last n)}` and
`simplexSouthCap n = {x | x.weights (Fin.last n) < 1}`.  In this file we prove that the north cap
-- the open star of the last vertex -- is contractible, which is the geometric input of the
Mayer–Vietoris computation of `H_*(∂Δⁿ⁺¹)`.

Geometrically, the north cap is the union of the (relatively open) faces of `∂Δⁿ⁺¹` containing the
last vertex `v`: it is star shaped with respect to `v`, because for `x` in the cap the whole segment
from `x` to `v` lies in the minimal face of `∂Δⁿ⁺¹` containing `x`, which is a face through `v`
contained in the cap.  We transport this star shapedness along the embedding that sends a point of
`∂Δⁿ⁺¹` to its barycentric coordinates, viewed as a vector of `ℝ^{n+2}`; on that side the argument
is the standard one for star shaped subsets of a real topological vector space.

## Main result

* `Work.HomologyExtra.simplexNorthCap_contractible`
-/

namespace Work.HomologyExtra

open Topology

noncomputable section

/-- The north cap of `∂Δⁿ⁺¹`, described in terms of barycentric coordinates: the coordinates are
non-negative, sum to `1`, the coordinate at the last vertex is positive, and (because the point lies
on the boundary of the simplex) some coordinate vanishes.

This is the set of barycentric coordinate vectors of the points of `simplexNorthCap n`. -/
def northCapWeightSet (n : ℕ) : Set (Fin (n + 2) → ℝ) :=
  {f | (∀ i, 0 ≤ f i) ∧ (∑ i, f i = 1) ∧ 0 < f (Fin.last (n + 1)) ∧ ∃ i, f i = 0}

/-- The barycentric coordinates of a point of `∂Δⁿ⁺¹`, as a vector of `ℝ^{n+2}`. -/
abbrev northCapWeights (n : ℕ) : ↥(simplexBoundary (n + 1)) → (Fin (n + 2) → ℝ) :=
  fun x => fun i => (x : simplex (n + 1)).weights i

/-- The barycentric coordinates of the last vertex of `Δⁿ⁺¹`: the vector with a `1` at the last
coordinate and `0` elsewhere. -/
abbrev northCapApex (n : ℕ) : Fin (n + 2) → ℝ :=
  fun j => if j = Fin.last (n + 1) then 1 else 0

/-- The barycentric coordinate map is an embedding. -/
theorem isEmbedding_northCapWeights (n : ℕ) : IsEmbedding (northCapWeights n) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).comp
    IsEmbedding.subtypeVal

/-- The barycentric coordinates of a point of `∂Δⁿ⁺¹` lie in `northCapWeightSet n` exactly when
the point lies in the north cap. -/
theorem northCapWeights_preimage (n : ℕ) :
    northCapWeights n ⁻¹' northCapWeightSet n = simplexNorthCap n := by
  ext x
  simp only [Set.mem_preimage, northCapWeightSet, Set.mem_ofPred_eq, simplexNorthCap]
  constructor
  · rintro ⟨-, -, h, -⟩
    exact h
  · intro h
    exact ⟨fun i => Convexity.StdSimplex.weights_nonneg (w := (x : simplex (n + 1))) i,
      Convexity.StdSimplex.total_of_fintype (x : simplex (n + 1)), h, x.2⟩

/-- Every element of `northCapWeightSet n` is the barycentric coordinate vector of a point of
`∂Δⁿ⁺¹`. -/
theorem northCapWeightSet_subset_range (n : ℕ) :
    northCapWeightSet n ⊆ Set.range (northCapWeights n) := by
  rintro f ⟨hfnn, hfsum, hfpos, i, hi⟩
  have hmem : f ∈ Set.range
      (fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => fun i => t.weights i) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨hfnn, hfsum⟩
  obtain ⟨w, hw⟩ := hmem
  refine ⟨⟨w, ?_⟩, ?_⟩
  · exact ⟨i, by rw [show w.weights i = f i from congrFun hw i, hi]⟩
  · exact hw

/-- The barycentric coordinate vector of the last vertex belongs to the north cap. -/
theorem northCapApex_mem (n : ℕ) : northCapApex n ∈ northCapWeightSet n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simp only [northCapApex]
    split <;> norm_num
  · simp [northCapApex]
  · simp only [northCapApex]
    norm_num
  · refine ⟨(0 : Fin (n + 2)), ?_⟩
    simp [northCapApex, Fin.ext_iff]

/-- The north cap of `∂Δⁿ⁺¹` is non-empty. -/
theorem northCapWeightSet_nonempty (n : ℕ) : (northCapWeightSet n).Nonempty :=
  ⟨northCapApex n, northCapApex_mem n⟩

/-- The set `northCapWeightSet n` is star shaped with respect to the barycentric coordinate vector
of the last vertex: the segment from any point of the cap to that vertex stays in the cap. -/
theorem starConvex_northCapWeightSet (n : ℕ) :
    StarConvex ℝ (northCapApex n) (northCapWeightSet n) := by
  intro f hf a b ha hb hab
  obtain ⟨hfnn, hfsum, hfpos, i, hi⟩ := hf
  have hi_ne : i ≠ Fin.last (n + 1) := by
    intro h
    rw [← h, hi] at hfpos
    exact lt_irrefl 0 hfpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hvj : 0 ≤ northCapApex n j := by
      simp only [northCapApex]
      split <;> norm_num
    have := hfnn j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · have hvsum : ∑ j : Fin (n + 2), northCapApex n j = 1 := by simp [northCapApex]
    have hsplit : ∑ j : Fin (n + 2), (a * northCapApex n j + b * f j)
        = a * (∑ j : Fin (n + 2), northCapApex n j) + b * (∑ j : Fin (n + 2), f j) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsplit, hvsum, hfsum, mul_one, mul_one, hab]
  · have hlast : northCapApex n (Fin.last (n + 1)) = 1 := by simp [northCapApex]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlast]
    rcases lt_or_eq_of_le ha with ha0 | ha0
    · have hb' : 0 ≤ b * f (Fin.last (n + 1)) := mul_nonneg hb (le_of_lt hfpos)
      linarith
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]
      linarith
  · refine ⟨i, ?_⟩
    have hv0 : northCapApex n i = 0 := by simp [northCapApex, hi_ne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv0, hi, mul_zero, zero_add]

/-- **The north cap of `∂Δⁿ⁺¹` is contractible.** -/
theorem simplexNorthCap_contractible (n : ℕ) :
    ContractibleSpace (TopCat.of (Work.HomologyExtra.simplexNorthCap n)) := by
  have hc : ContractibleSpace ↥(northCapWeightSet n) :=
    (starConvex_northCapWeightSet n).contractibleSpace (northCapWeightSet_nonempty n)
  have h : ↥(simplexNorthCap n) ≃ₜ ↥(northCapWeightSet n) :=
    (Homeomorph.setCongr (northCapWeights_preimage n)).symm.trans
      ((isEmbedding_northCapWeights n).homeomorphOfSubsetRange
        (northCapWeightSet_subset_range n))
  show ContractibleSpace ↥(simplexNorthCap n)
  exact (Homeomorph.contractibleSpace_iff h).mpr hc

end

end Work.HomologyExtra
