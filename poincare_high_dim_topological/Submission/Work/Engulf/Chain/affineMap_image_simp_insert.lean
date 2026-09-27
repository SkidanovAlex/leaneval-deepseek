import Mathlib
import Submission.Work.PL.Defs

open Set Metric PL

namespace Work.Engulf.Chain

/-- If an affine self-map `A` of `PL.E N` fixes a finite vertex set `σ` pointwise and sends the
apex `a` into the simplex `PL.simp σ`, then it maps the cone `PL.simp (insert a σ)` into
`PL.simp σ` (`A '' convexHull ℝ (σ ∪ {a}) = convexHull ℝ (A '' (σ ∪ {a})) ⊆ convexHull ℝ σ`, as
`PL.simp σ` is convex). -/
theorem affineMap_image_simp_insert {N : ℕ} (A : PL.E N →ᵃ[ℝ] PL.E N) {σ : Finset (PL.E N)}
    {a : PL.E N} (h : ∀ v ∈ σ, A v = v) (ha : A a ∈ PL.simp σ) :
    A '' PL.simp (insert a σ) ⊆ PL.simp σ := by
  intro x hx
  rw [PL.simp] at hx ⊢
  rw [AffineMap.image_convexHull] at hx
  refine convexHull_min ?_ (convex_convexHull ℝ (σ : Set (PL.E N))) hx
  rintro y ⟨v, hv, rfl⟩
  rw [Finset.mem_coe, Finset.mem_insert] at hv
  rcases hv with rfl | hv
  · simpa [PL.simp] using ha
  · rw [h v hv]
    exact subset_convexHull ℝ (σ : Set (PL.E N)) (by simpa using hv)

end Work.Engulf.Chain
