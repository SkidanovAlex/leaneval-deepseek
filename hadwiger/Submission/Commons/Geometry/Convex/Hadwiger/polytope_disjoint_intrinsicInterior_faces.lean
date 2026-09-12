import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.CompletePartialOrder

namespace Commons.Geometry.Convex.Hadwiger

/-!
# Disjoint intrinsic interiors of distinct exposed faces of a polytope

Two distinct nonempty exposed faces of a polytope have disjoint (relative)
interiors.  The proof is the classical one:

1. (`mem_openSegment_smul_sub`) If `δ > 0` then `x` lies in the open segment
   joining `y` to `x + δ • (x - y)` (the point obtained by walking past `x`
   in the direction from `y` through `x`).
2. (`exists_add_smul_sub_mem_of_mem_intrinsicInterior`) A point of the
   intrinsic (relative) interior of a set is a relative interior point of its
   affine span, so walking any small distance in a direction lying in that
   affine span keeps one inside the set.  Hence from `x ∈ intrinsicInterior s`
   and `y ∈ s` we can walk past `x` toward any point of `s`.
3. (`exists_openSegment_mem_of_mem_intrinsicInterior`) Combining the previous
   two: if `x ∈ intrinsicInterior s` and `y ∈ s`, then `x` lies in the open
   segment between `y` and some point `z ∈ s`.
4. (`subset_of_mem_intrinsicInterior_of_isExtreme`) If `F` is an extreme
   subset of `C`, `G ⊆ C`, `x ∈ F ∩ intrinsicInterior G`, then `G ⊆ F`:
   each `y ∈ G` is an endpoint of an open segment through `x` whose other
   endpoint lies in `G ⊆ C`, and extremality of `F` forces `y ∈ F`.
5. The theorem: two distinct faces cannot have a common point in their
   intrinsic interiors, for such a point would force each face to contain
   the other.
-/

open Set Filter
open scoped BigOperators Pointwise Convex Topology

/-- If `δ > 0`, then `x` lies in the open segment joining `y` to the point
`x + δ • (x - y)` obtained by walking past `x` in the direction from `y`
through `x`. -/
lemma mem_openSegment_smul_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : V) {δ : ℝ} (hδ : 0 < δ) :
    x ∈ openSegment ℝ y (x + δ • (x - y)) := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨(1 + δ)⁻¹, ?_, ?_⟩
  · constructor
    · positivity
    · have h1 : 1 < 1 + δ := by linarith
      exact inv_lt_one_of_one_lt₀ h1
  · rw [AffineMap.lineMap_apply_module']
    have hz : (x + δ • (x - y)) - y = (1 + δ) • (x - y) := by module
    rw [hz, smul_smul]
    have ht0 : (1 + δ) ≠ 0 := by positivity
    have hsc : (1 + δ)⁻¹ * (1 + δ) = 1 := inv_mul_cancel₀ ht0
    rw [hsc, one_smul]
    abel

/-- A point `x` of the intrinsic interior of `s` is an interior point of `s`
within its affine span, so one may walk a little past `x` towards any point
`y ∈ s` and remain in `s`. -/
lemma exists_add_smul_sub_mem_of_mem_intrinsicInterior {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {s : Set V} {x y : V}
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ δ : ℝ, 0 < δ ∧ x + δ • (x - y) ∈ s := by
  classical
  by_cases hxy : x = y
  · subst y
    refine ⟨1, zero_lt_one, ?_⟩
    simpa using (intrinsicInterior_subset hx)
  have hxs : x ∈ s := intrinsicInterior_subset hx
  have hxA : x ∈ (affineSpan ℝ s : AffineSubspace ℝ V) := subset_affineSpan ℝ s hxs
  have hyA : y ∈ (affineSpan ℝ s : AffineSubspace ℝ V) := subset_affineSpan ℝ s hy
  have hdir : x - y ∈ (affineSpan ℝ s).direction :=
    AffineSubspace.vsub_mem_direction hxA hyA
  rcases mem_intrinsicInterior.mp hx with ⟨x', hx'int, hx'eq⟩
  haveI : Nonempty (affineSpan ℝ s) := ⟨x'⟩
  let sA : Set (affineSpan ℝ s) := ((↑) : affineSpan ℝ s → V) ⁻¹' s
  have hx'int' : x' ∈ interior sA := by simpa [sA] using hx'int
  have hball : sA ∈ 𝓝 x' := mem_interior_iff_mem_nhds.mp hx'int'
  rcases Metric.mem_nhds_iff.mp hball with ⟨ε, hε, hballε⟩
  let δ : ℝ := ε / (2 * ‖x - y‖)
  have hd0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact div_pos hε (mul_pos (by norm_num) hd0)
  refine ⟨δ, hδ0, ?_⟩
  let z : V := x + δ • (x - y)
  have hzA : z ∈ (affineSpan ℝ s : Set V) := by
    have hzm : δ • (x - y) +ᵥ x ∈ (affineSpan ℝ s : Set V) :=
      AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ s) δ hxA hyA hxA
    simpa [z, add_comm] using hzm
  have hzin : ⟨z, hzA⟩ ∈ Metric.ball x' ε := by
    rw [Metric.mem_ball]
    rw [Subtype.dist_eq]
    rw [dist_eq_norm]
    have hnorm : ‖(x + δ • (x - y)) - (x' : V)‖ < ε := by
      rw [hx'eq]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδ0]
      have hδn : δ * ‖x - y‖ = ε / 2 := by
        dsimp [δ]
        field_simp [hd0.ne']
      rw [hδn]
      linarith
    simpa [z] using hnorm
  have hzinsA : ⟨z, hzA⟩ ∈ sA := hballε hzin
  change z ∈ s
  simpa [sA] using hzinsA

/-- From a point of the intrinsic interior of `s`, every other point of `s`
is the endpoint of an open segment through the interior point whose other
endpoint also lies in `s`. -/
lemma exists_openSegment_mem_of_mem_intrinsicInterior {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {s : Set V} {x y : V}
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ z ∈ s, x ∈ openSegment ℝ y z := by
  rcases exists_add_smul_sub_mem_of_mem_intrinsicInterior hx hy with ⟨δ, hδ, hzmem⟩
  refine ⟨x + δ • (x - y), hzmem, ?_⟩
  exact mem_openSegment_smul_sub x y hδ

/-- If `F` is an extreme subset of `C`, `G ⊆ C` and a point of the intrinsic
interior of `G` lies in `F`, then `G ⊆ F`. -/
lemma subset_of_mem_intrinsicInterior_of_isExtreme {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {C F G : Set V}
    (hGC : G ⊆ C) (hFext : IsExtreme ℝ C F)
    {x : V} (hxF : x ∈ F) (hxG : x ∈ intrinsicInterior ℝ G) : G ⊆ F := by
  intro y hy
  by_cases hyx : y = x
  · simpa [hyx] using hxF
  · rcases exists_openSegment_mem_of_mem_intrinsicInterior (s := G) hxG hy with ⟨z, hzG, hxz⟩
    exact hFext.left_mem_of_mem_openSegment (hGC hy) (hGC hzG) hxF hxz

/-- Distinct nonempty exposed faces of a polytope have disjoint intrinsic
(relative) interiors: a common point of the two relative interiors would make
each face contain the other. -/
theorem polytope_disjoint_intrinsicInterior_faces (m : ℕ)
    (u : Finset (EuclideanSpace ℝ (Fin m)))
    (P : Set (EuclideanSpace ℝ (Fin m)))
    (hP : P = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m))))
    {F G : Set (EuclideanSpace ℝ (Fin m))}
    (hF : IsExposed ℝ P F) (hG : IsExposed ℝ P G)
    (hFne : F.Nonempty) (hGne : G.Nonempty) (hFG : F ≠ G) :
    Disjoint (intrinsicInterior ℝ F) (intrinsicInterior ℝ G) := by
  classical
  rw [Set.disjoint_left]
  intro x hxF hxG
  have hxFmem : x ∈ F := intrinsicInterior_subset hxF
  have hxGmem : x ∈ G := intrinsicInterior_subset hxG
  have hG_le_F : G ⊆ F :=
    subset_of_mem_intrinsicInterior_of_isExtreme (C := P) (F := F) (G := G)
      hG.subset hF.isExtreme hxFmem hxG
  have hF_le_G : F ⊆ G :=
    subset_of_mem_intrinsicInterior_of_isExtreme (C := P) (F := G) (G := F)
      hF.subset hG.isExtreme hxGmem hxF
  have hFG' : F = G := Set.Subset.antisymm hF_le_G hG_le_F
  exact hFG hFG'

end Commons.Geometry.Convex.Hadwiger