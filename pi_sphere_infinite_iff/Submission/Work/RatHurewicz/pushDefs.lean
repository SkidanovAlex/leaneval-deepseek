import Mathlib
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.skeletonCompress
import Submission.Work.RatHurewicz.cellPushRadialFalse
import Submission.Work.RatHurewicz.cellFacts

/-!
# The cell-wise push of the model `Model D` off its `k`-cells: vocabulary

This file fixes the vocabulary of the "push the `k`-cells off" step of
`Work.RatHurewicz.skelStep`: the *centroid points* of the faces (the points at which the push of a
cell is discontinuous), the *bad points* of the model in dimension `k` (the images of those
centroids), the barycentric push `pushPt` (of arbitrary arity, so that it is compatible with the
face identifications), and its elementary properties.

For a point `x` of a standard simplex whose support `S` has `k+1` elements and which is not the
centroid of `S`, the push `pushPt k u x` is the straight-line interpolation between `x` and the
*collapse* of `x` (the point of the face `S` obtained by bringing the smallest coordinate of the
support down to `0` and renormalising).  At `u = 0` it is the identity; at `u = 1` it is the
collapse, which lies in the boundary of `S` (the weight drops); for `u < 1` the weight is
preserved.  It is compatible with the face maps `facept`, and continuous away from the centroid of
`S`.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The support of a point of a standard simplex (any arity) -/

/-- The support of a point of a standard simplex is nonempty (the coordinates sum to `1`). -/
theorem supp_nonempty {m : ℕ} (x : stdSimplex ℝ (Fin m)) : (supp x).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hsum : ∑ i, (x : Fin m → ℝ) i = 1 := x.2.2
  have hzero : ∑ i, (x : Fin m → ℝ) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hx
    have hmem : i ∈ (∅ : Finset (Fin m)) := h ▸ mem_supp.mpr hx
    simp at hmem
  rw [hzero] at hsum
  norm_num at hsum

/-- The support of a point of `Δ^{n+1}` is its `ptSupport`. -/
theorem supp_eq_ptSupport (x : stdSimplex ℝ (Fin (n + 2))) : supp x = ptSupport x := rfl

/-- The **smallest barycentric coordinate** of a point of a standard simplex. -/
def suppMin {m : ℕ} (x : stdSimplex ℝ (Fin m)) : ℝ :=
  (supp x).inf' (supp_nonempty x) (fun i => (x : Fin m → ℝ) i)

theorem suppMin_le {m : ℕ} (x : stdSimplex ℝ (Fin m)) {i : Fin m} (hi : i ∈ supp x) :
    suppMin x ≤ (x : Fin m → ℝ) i :=
  (Finset.inf'_le_iff (supp_nonempty x)).mpr ⟨i, hi, le_refl _⟩

theorem suppMin_eq_of_min {m : ℕ} {x : stdSimplex ℝ (Fin m)} {i : Fin m} (hi : i ∈ supp x)
    (hmin : ∀ j ∈ supp x, (x : Fin m → ℝ) i ≤ (x : Fin m → ℝ) j) :
    suppMin x = (x : Fin m → ℝ) i :=
  le_antisymm (suppMin_le x hi)
    ((Finset.le_inf'_iff (supp_nonempty x) (fun j => (x : Fin m → ℝ) j)).mpr hmin)

/-- The sum of the coordinates over the support is `1`. -/
theorem sum_supp {m : ℕ} (x : stdSimplex ℝ (Fin m)) :
    ∑ i ∈ supp x, (x : Fin m → ℝ) i = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · exact x.2.2
  · intro i _ hi
    by_contra hx
    exact hi (mem_supp.mpr hx)

/-- `suppMin` is at most `1/(k+1)` when the support has `k+1` elements. -/
theorem suppMin_le_inv {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) : suppMin x ≤ ((k : ℝ) + 1)⁻¹ := by
  have hcard' : ((supp x).card : ℝ) = (k : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hcast : ((supp x).card : ℝ) * suppMin x = ∑ _i ∈ supp x, suppMin x := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hle : ((supp x).card : ℝ) * suppMin x ≤ ∑ i ∈ supp x, (x : Fin m → ℝ) i := by
    rw [hcast]
    exact Finset.sum_le_sum (fun j hj => suppMin_le x hj)
  rw [sum_supp] at hle
  have hpos : (0:ℝ) < ((supp x).card : ℝ) := by rw [hcard]; positivity
  have h1 : suppMin x * ((supp x).card : ℝ) ≤ 1 := by linarith
  have h2 : suppMin x ≤ 1 / ((supp x).card : ℝ) := (le_div_iff₀ hpos).mpr h1
  calc suppMin x ≤ 1 / ((supp x).card : ℝ) := h2
    _ = ((k : ℝ) + 1)⁻¹ := by rw [hcard', one_div]

/-- The denominator of the collapse is nonnegative when the support has `k+1` elements. -/
theorem one_sub_suppMin_nonneg {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) : 0 ≤ 1 - ((k : ℝ) + 1) * suppMin x := by
  have h := suppMin_le_inv k x hcard
  have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt hk), inv_mul_cancel₀ (ne_of_gt hk)]

/-- **A centroid point of dimension `k`**: a point of a standard simplex with `k+1` support
coordinates, all equal.  These are the points at which the push of a `(k+1)`-cell is
discontinuous. -/
def IsCentralPt {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m)) : Prop :=
  (supp x).card = k + 1 ∧ ∀ i ∈ supp x, (x : Fin m → ℝ) i = ((k : ℝ) + 1)⁻¹

/-- In a centroid point the smallest coordinate is `1/(k+1)`. -/
theorem IsCentralPt.suppMin {m : ℕ} {k : ℕ} {x : stdSimplex ℝ (Fin m)} (h : IsCentralPt k x) :
    suppMin x = ((k : ℝ) + 1)⁻¹ := by
  obtain ⟨i, hi⟩ := supp_nonempty x
  have hmin : ∀ j ∈ supp x, (x : Fin m → ℝ) i ≤ (x : Fin m → ℝ) j := by
    intro j hj; rw [h.2 i hi, h.2 j hj]
  rw [suppMin_eq_of_min hi hmin, h.2 i hi]

/-! ## The bad points of the model -/

/-- **A bad point of the model in dimension `k`**: the image of a centroid point of dimension `k`
in one of the copies of `Δ^{n+1}`. -/
def IsBadPt (D : MData X n x₀) (k : ℕ) (z : Model D) : Prop :=
  ∃ (i : D.Idx) (x : stdSimplex ℝ (Fin (n + 2))), IsCentralPt k x ∧
    (Quotient.mk'' (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) : Model D) = z

/-- The points of the `1`-skeleton of the model are never bad in dimension `k ≥ 2`. -/
theorem not_isBadPt_of_mem_skeleton {D : MData X n x₀} {k : ℕ} (hk : 2 ≤ k) {z : Model D}
    (hz : z ∈ skeleton D) : ¬ IsBadPt D k z := by
  rintro ⟨i, x, hx, hxz⟩
  have hz1 : z ∈ skel D 1 := hz
  obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp hz1
  have hrel : Relation.EqvGen (modelRel D) a (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx,
      stdSimplex ℝ (Fin (n + 2)))) := Quotient.exact (ha.trans hxz.symm)
  have hw' : rawWeight D a = rawWeight D (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx,
      stdSimplex ℝ (Fin (n + 2)))) := rawWeight_eqvGen D hrel
  rw [rawWeight_inl] at hw'
  rw [← supp_eq_ptSupport] at hw'
  rw [hx.1] at hw'
  omega

end

end Work.RatHurewicz
