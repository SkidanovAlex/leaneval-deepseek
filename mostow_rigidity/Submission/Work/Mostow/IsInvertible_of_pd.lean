import Mathlib
import Submission.Work.Mostow.BCGDefs

namespace Work.Mostow

/-- If the symmetric (quadratic) form of `id - H` is strictly positive definite, then `id - H` is
invertible.  The space `E n` is finite-dimensional, so injectivity suffices. -/
theorem IsInvertible_of_pd (n : ℕ) (H : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
    (h : ∀ v : Submission.Mostow.E n, v ≠ 0 →
      0 < inner ℝ v v - inner ℝ (H v) v) :
    (ContinuousLinearMap.id ℝ (Submission.Mostow.E n) - H).IsInvertible := by
  set f : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n :=
    ContinuousLinearMap.id ℝ (Submission.Mostow.E n) - H with hf
  have hker : ∀ v, f v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    have hh := h v hv0
    have hinner : inner ℝ (f v) v = inner ℝ v v - inner ℝ (H v) v := by
      simp only [hf, sub_apply, ContinuousLinearMap.id_apply, inner_sub_left]
    rw [hv, inner_zero_left] at hinner
    linarith
  have hinj : Function.Injective f := fun v w hvw => by
    have : f (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker (v - w) this)
  have hinj' : Function.Injective f.toLinearMap := hinj
  let e : Submission.Mostow.E n ≃ₗ[ℝ] Submission.Mostow.E n :=
    LinearEquiv.ofBijective f.toLinearMap
      ⟨hinj', LinearMap.injective_iff_surjective.mp hinj'⟩
  exact ⟨e.toContinuousLinearEquiv, by ext v; simp [e, hf]⟩

end Work.Mostow
