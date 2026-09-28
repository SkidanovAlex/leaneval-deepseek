import Mathlib

namespace Work.Analysis.BilinOperator

open scoped ContDiff in
/-- Given a symmetric, non-degenerate continuous bilinear form `Q` on a finite-dimensional real
inner product space `E` and a nonzero real `c`, the operator `P₀ = ♯(c • Q)` is an invertible,
self-adjoint continuous linear operator, and its inverse `Pin` is again self-adjoint. -/
theorem bilin_operator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] (E →L[ℝ] ℝ)) (c : ℝ) (hc : c ≠ 0)
    (hQsymm : ∀ v w, Q v w = Q w v)
    (hQ : ∀ v, (∀ w, Q v w = 0) → v = 0) :
    ∃ (P₀ : E →L[ℝ] E) (Pin : E ≃L[ℝ] E),
      P₀ = InnerProductSpace.continuousLinearMapOfBilin (c • Q) ∧
      (Pin : E →L[ℝ] E) * P₀ = 1 ∧
      P₀ * (Pin : E →L[ℝ] E) = 1 ∧
      ContinuousLinearMap.adjoint (Pin : E →L[ℝ] E) = Pin ∧
      ContinuousLinearMap.adjoint P₀ = P₀ := by
  obtain ⟨P₀, hP₀eq⟩ : ∃ P : E →L[ℝ] E,
      P = InnerProductSpace.continuousLinearMapOfBilin (c • Q) := ⟨_, rfl⟩
  -- The defining property of `P₀` against the inner product.
  have hP₀apply : ∀ v w : E, inner ℝ (P₀ v) w = c * Q v w := by
    intro v w
    rw [hP₀eq, InnerProductSpace.continuousLinearMapOfBilin_apply]
    simp [smul_eq_mul]
  -- `P₀` is self-adjoint, because `Q` is symmetric.
  have hsymm : ∀ x y : E, inner ℝ (P₀ x) y = inner ℝ x (P₀ y) := by
    intro x y
    rw [hP₀apply x y, ← real_inner_comm x (P₀ y), hP₀apply y x, hQsymm x y]
  have hP₀adj : ContinuousLinearMap.adjoint P₀ = P₀ := by
    rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    exact hsymm
  -- Non-degeneracy of `Q` (and `c ≠ 0`) makes `P₀` injective.
  have hker0 : ∀ v : E, P₀ v = 0 → v = 0 := by
    intro v hv
    apply hQ v
    intro w
    have h1 : inner ℝ (P₀ v) w = 0 := by rw [hv, inner_zero_left]
    rw [hP₀apply v w] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  have hinj : Function.Injective ⇑(P₀ : E →ₗ[ℝ] E) := by
    intro x y hxy
    have hxy' : P₀ x = P₀ y := hxy
    have hsub : P₀ (x - y) = 0 := by rw [map_sub, hxy', sub_self]
    exact sub_eq_zero.mp (hker0 _ hsub)
  have hker : (P₀ : E →ₗ[ℝ] E).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsurj : Function.Surjective ⇑(P₀ : E →ₗ[ℝ] E) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hrange : (P₀ : E →ₗ[ℝ] E).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  -- `Pin` is the inverse of `P₀`, as a continuous linear equivalence.
  set e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective P₀ hker hrange with he
  set Pin : E ≃L[ℝ] E := e.symm with hPin
  have hPin_left : (Pin : E →L[ℝ] E) * P₀ = 1 := by
    ext x
    have h1 : (Pin : E →L[ℝ] E) (P₀ x) = x := by
      rw [hPin]
      show e.symm (e x) = x
      exact ContinuousLinearEquiv.symm_apply_apply e x
    simpa using h1
  have hPin_right : P₀ * (Pin : E →L[ℝ] E) = 1 := by
    ext x
    have h1 : P₀ ((Pin : E →L[ℝ] E) x) = x := by
      rw [hPin]
      show e (e.symm x) = x
      exact ContinuousLinearEquiv.apply_symm_apply e x
    simpa using h1
  -- `Pin`, the inverse of a self-adjoint operator, is self-adjoint.
  have hPinadj : ContinuousLinearMap.adjoint (Pin : E →L[ℝ] E) = Pin := by
    have hstar1 : P₀ * star (Pin : E →L[ℝ] E) = 1 := by
      have h := congrArg star hPin_left
      rw [star_mul, star_one] at h
      rwa [ContinuousLinearMap.star_eq_adjoint P₀, hP₀adj] at h
    have hEq : P₀ * star (Pin : E →L[ℝ] E) = P₀ * (Pin : E →L[ℝ] E) := by
      rw [hstar1, hPin_right]
    have hstar2 : star (Pin : E →L[ℝ] E) = (Pin : E →L[ℝ] E) := by
      apply ContinuousLinearMap.ext
      intro z
      apply hinj
      have h2 := congrArg (fun f : E →L[ℝ] E => f z) hEq
      simpa [mul_apply_eq_comp] using h2
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hstar2
  exact ⟨P₀, Pin, hP₀eq, hPin_left, hPin_right, hPinadj, hP₀adj⟩

end Work.Analysis.BilinOperator
