import Mathlib
import Submission.Work.Whitney.exists_sheet_model

/-!
# Infrastructure for the cut form of the local Whitney push (transverse case)

Three self-contained facts about the sheet model `Work.Whitney.exists_sheet_model`:

* the image of *every* ball `ball 0 ρ` (`ρ ≤ R₀`) under a sheet parametrisation is open;
* the frontier of `σ '' closedBall 0 ρ` is contained in `σ '' sphere 0 ρ`;
* the model's `A` (a continuous linear map with `α‖u‖ ≤ ‖A u‖`) can be turned into a continuous
  linear *equivalence*, with the expected bound on its inverse.
-/

open scoped Manifold ContDiff
open Topology Metric Set

namespace Work.Whitney

/-- **The image of a ball under a right section of `φ` is open.**
If `σ` is a right section of `φ` on the ball of radius `R₀` (`φ (σ u) = u` there) and `σ` is
injective on that ball, then `σ '' ball 0 ρ` is open for every `ρ ≤ R₀` (given openness for `R₀`).
The proof is the identity `σ '' ball 0 ρ = (σ '' ball 0 R₀) ∩ φ ⁻¹' ball 0 ρ`. -/
theorem isOpen_image_ball_of_section {n : ℕ} {M : Type*} [TopologicalSpace M]
    (σ : EuclideanSpace ℝ (Fin n) → M) (φ : M → EuclideanSpace ℝ (Fin n)) (R₀ : ℝ)
    (hφ : Continuous φ) (hsec : ∀ u, ‖u‖ ≤ R₀ → φ (σ u) = u)
    (hinj : Set.InjOn σ (Metric.closedBall 0 R₀))
    (hopen : IsOpen (σ '' Metric.ball 0 R₀))
    (ρ : ℝ) (hρR : ρ ≤ R₀) :
    IsOpen (σ '' Metric.ball 0 ρ) := by
  have hset : σ '' Metric.ball 0 ρ = (σ '' Metric.ball 0 R₀) ∩ φ ⁻¹' Metric.ball 0 ρ := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      have huR : ‖u‖ ≤ R₀ := le_of_lt (lt_of_lt_of_le (mem_ball_zero_iff.mp hu) hρR)
      exact ⟨⟨u, mem_ball_zero_iff.mpr (lt_of_lt_of_le (mem_ball_zero_iff.mp hu) hρR), rfl⟩,
        by rw [Set.mem_preimage, mem_ball_zero_iff, hsec u huR]; exact mem_ball_zero_iff.mp hu⟩
    · rintro z ⟨⟨u, hu, rfl⟩, hz⟩
      have huR : ‖u‖ ≤ R₀ := le_of_lt (mem_ball_zero_iff.mp hu)
      rw [Set.mem_preimage, mem_ball_zero_iff] at hz
      rw [hsec u huR] at hz
      exact ⟨u, mem_ball_zero_iff.mpr hz, rfl⟩
  rw [hset]
  exact hopen.inter (Metric.isOpen_ball.preimage hφ)

/-- **The frontier of the image of a closed ball.**  If the image of the *open* ball is open and
the image of the closed ball is closed, the frontier consists of images of sphere points. -/
theorem frontier_image_closedBall_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (σ : EuclideanSpace ℝ (Fin n) → M)
    (ρ : ℝ) (hopen : IsOpen (σ '' Metric.ball 0 ρ))
    (hclosed : IsClosed (σ '' Metric.closedBall 0 ρ))
    (hinj : Set.InjOn σ (Metric.closedBall 0 ρ)) :
    frontier (σ '' Metric.closedBall 0 ρ) ⊆ σ '' Metric.sphere 0 ρ := by
  intro z hz
  have hzS : z ∈ σ '' Metric.closedBall 0 ρ := by
    rw [← hclosed.closure_eq]; exact hz.1
  obtain ⟨u, hu, rfl⟩ := hzS
  have hu' : ‖u‖ ≤ ρ := mem_closedBall_zero_iff.mp hu
  refine ⟨u, ?_, rfl⟩
  rw [Metric.mem_sphere, dist_zero_right]
  by_contra hne
  have hlt : ‖u‖ < ρ := lt_of_le_of_ne hu' hne
  have hmem : σ u ∈ σ '' Metric.ball 0 ρ := ⟨u, mem_ball_zero_iff.mpr hlt, rfl⟩
  have hint : σ u ∈ interior (σ '' Metric.closedBall 0 ρ) :=
    interior_maximal (Set.image_mono Metric.ball_subset_closedBall) hopen hmem
  exact hz.2 hint

/-- **A continuous linear map bounded below is a continuous linear equivalence.**
The inverse satisfies `‖A.symm v‖ ≤ α⁻¹ ‖v‖`. -/
theorem clm_equiv_of_lower_bound {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (α : ℝ) (hα : 0 < α) (hA : ∀ u, α * ‖u‖ ≤ ‖A u‖) :
    ∃ A' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (A' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = A ∧
      ∀ v, ‖A'.symm v‖ ≤ α⁻¹ * ‖v‖ := by
  have hinj : Function.Injective A := by
    intro u v huv
    have h0 : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 := hA (u - v)
    rw [h0, norm_zero] at h1
    have h2 : ‖u - v‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (u - v)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : A.range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinj)
  let A' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofBijective A hker hrange
  have hcoe : (A' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = A :=
    ContinuousLinearEquiv.coe_ofBijective A hker hrange
  refine ⟨A', hcoe, ?_⟩
  intro v
  have h1 : A (A'.symm v) = v := by
    rw [← hcoe]
    exact A'.apply_symm_apply v
  have h2 := hA (A'.symm v)
  rw [h1] at h2
  rw [inv_mul_eq_div, le_div_iff₀ hα]
  linarith

end Work.Whitney
