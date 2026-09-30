import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## A linear-algebra fact about the row space of a rational matrix

If `u` is not in the `ℚ`-span of the rows of `A`, then there is a vector `w` in the
right kernel of `A` whose dot product with `u` is nonzero.  Equivalently, the row space
of `A` is exactly the orthogonal complement of the kernel of `A` (with respect to the
standard dot product), a fact we obtain from the double-orthogonal theorem for
nondegenerate reflexive bilinear forms (`LinearMap.BilinForm.orthogonal_orthogonal`).
-/

/-- The standard dot-product bilinear form on `Fin N → ℚ`. -/
private def dotB (N : ℕ) : LinearMap.BilinForm ℚ (Fin N → ℚ) := dotProductBilin ℚ ℚ

private lemma dotB_apply {N : ℕ} (x y : Fin N → ℚ) : dotB N x y = ∑ i, x i * y i := rfl

/-- The dot-product form is reflexive. -/
private lemma dotB_refl (N : ℕ) : (dotB N).IsRefl := by
  intro x y h
  simpa [dotB_apply, dotProduct, mul_comm] using h

/-- The dot-product form is nondegenerate. -/
private lemma dotB_nondegenerate (N : ℕ) : (dotB N).Nondegenerate := by
  constructor
  · intro x h
    exact dotProduct_eq_zero_iff.mp (fun y => by simpa [dotB_apply, dotProduct] using h y)
  · intro y h
    exact dotProduct_eq_zero_iff.mp (fun x => by simpa [dotB_apply, dotProduct, mul_comm] using h x)

lemma ker_orth {N ρ : ℕ} (A : Fin ρ → Fin N → ℚ) (u : Fin N → ℚ)
    (hu : u ∉ Submodule.span ℚ (Set.range A)) :
    ∃ w : Fin N → ℚ, (∀ j, ∑ i, A j i * w i = 0) ∧ ∑ i, u i * w i ≠ 0 := by
  classical
  -- `u` is not in `V⊥⊥`, where `V` is the row space and `⊥` is w.r.t. the dot product.
  have hu' : u ∉ (dotB N).orthogonal ((dotB N).orthogonal (Submodule.span ℚ (Set.range A))) := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal (dotB_nondegenerate N) (dotB_refl N)]
    exact hu
  -- Hence some `w` orthogonal to the row space has nonzero dot product with `u`.
  obtain ⟨w, hw, huw⟩ :
      ∃ w ∈ (dotB N).orthogonal (Submodule.span ℚ (Set.range A)), (dotB N) u w ≠ 0 := by
    by_contra hcon
    refine hu' ?_
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    by_contra hne
    exact hcon ⟨v, hv, fun h0 => hne ((dotB_refl N).eq_iff.mp h0)⟩
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hAj : A j ∈ Submodule.span ℚ (Set.range A) := Submodule.subset_span (Set.mem_range_self j)
    have h0 : (dotB N) (A j) w = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) (A j) hAj
    rw [dotB_apply] at h0
    exact h0
  · intro h0
    apply huw
    rw [dotB_apply]
    exact h0

end Work.BW
