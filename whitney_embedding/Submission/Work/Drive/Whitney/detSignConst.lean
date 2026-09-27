import Mathlib

namespace Work.Drive.Whitney

/-- **The determinant of a smooth family of invertible operators has constant sign.**

Let `Z : ℝ × ℝ → (EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))` be smooth (as a family
of continuous linear maps).  Then for any two points `p, q` the determinants `det (Z p)` and
`det (Z q)` have the same sign, i.e. `0 < det (Z p) * det (Z q)`.

This uses only the continuity of `det ∘ Z` on the connected space `ℝ × ℝ` together with the fact
that `det (Z ·) ≠ 0` everywhere.  Suggested route: `det` is a polynomial function of the entries of
the matrix of the operator, hence continuous, and a continuous nowhere-zero real function on a
connected space has constant sign (`isPreconnected_iff` / the intermediate value theorem). -/
theorem detSignConst {n : ℕ}
    (Z : ℝ × ℝ → (EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hZ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (Z p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))))
    (p q : ℝ × ℝ) :
    0 < (LinearMap.det ((Z p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) *
      (LinearMap.det ((Z q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) := by
  -- `det ∘ Z` is continuous, being the composite of `Z` with the continuous determinant.
  have hcont : Continuous fun x : ℝ × ℝ =>
      LinearMap.det ((Z x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearMap.continuous_det.comp hZ.continuous
  -- and it never vanishes, because each `Z x` is an invertible linear map.
  have hne : ∀ x : ℝ × ℝ,
      LinearMap.det ((Z x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro x
    have h1 : IsUnit (LinearMap.det ((Z x).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) :=
      LinearEquiv.isUnit_det' _
    rw [show LinearMap.det ((Z x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
        LinearMap.det ((Z x).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) from rfl]
    exact h1.ne_zero
  -- A continuous nowhere-zero function on `ℝ × ℝ` (preconnected) cannot change sign:
  -- if the values at `p` and `q` had opposite signs, the intermediate value theorem
  -- would produce a zero.
  rcases lt_or_gt_of_ne (hne p) with hp | hp
  · rcases lt_or_gt_of_ne (hne q) with hq | hq
    · exact mul_pos_of_neg_of_neg hp hq
    · exfalso
      obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge hcont
        (show ∃ a : ℝ × ℝ, _ ≤ (0:ℝ) from ⟨p, le_of_lt hp⟩)
        (show ∃ b : ℝ × ℝ, (0:ℝ) ≤ _ from ⟨q, le_of_lt hq⟩)
      exact hne x hx
  · rcases lt_or_gt_of_ne (hne q) with hq | hq
    · exfalso
      obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge hcont
        (show ∃ a : ℝ × ℝ, _ ≤ (0:ℝ) from ⟨q, le_of_lt hq⟩)
        (show ∃ b : ℝ × ℝ, (0:ℝ) ≤ _ from ⟨p, le_of_lt hp⟩)
      exact hne x hx
    · exact mul_pos hp hq

end Work.Drive.Whitney
