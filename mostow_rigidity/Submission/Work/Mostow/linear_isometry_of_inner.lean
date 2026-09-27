import Mathlib
import Submission.Work.Mostow.cosh_hdist_fermi

namespace Work.Mostow

/-! A self-map of a Euclidean space which preserves the inner product and is surjective is the
underlying map of a linear isometry equivalence.

The argument uses the inner product as the only "test functional": if `v` is orthogonal to the
image of `R`, then `v = 0` because `v` is the image of something (`hsurj`).  This gives additivity
and `ℝ`-homogeneity of `R`, and `‖R x‖ = ‖x‖` follows from `⟪R x, R x⟫ = ⟪x, x⟫`. -/
theorem linear_isometry_of_inner (m : ℕ) (R : Submission.Mostow.E m → Submission.Mostow.E m)
    (hinner : ∀ x y : Submission.Mostow.E m, inner ℝ (R x) (R y) = inner ℝ x y)
    (hsurj : Function.Surjective R) :
    ∃ R' : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m,
      ∀ x : Submission.Mostow.E m, R' x = R x := by
  have hnorm : ∀ x : Submission.Mostow.E m, ‖R x‖ = ‖x‖ := by
    intro x
    have h : ‖R x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (R x), ← real_inner_self_eq_norm_sq x, hinner]
    have h1 : ‖R x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg (R x), norm_nonneg x]
    have h2 : ‖x‖ ≤ ‖R x‖ := by nlinarith [norm_nonneg (R x), norm_nonneg x]
    linarith
  have hadd : ∀ x y : Submission.Mostow.E m, R (x + y) = R x + R y := by
    intro x y
    have key : ∀ z : Submission.Mostow.E m, inner ℝ (R (x + y) - R x - R y) (R z) = 0 := by
      intro z
      rw [inner_sub_left, inner_sub_left, hinner, hinner, hinner]
      rw [inner_add_left]
      ring
    obtain ⟨z, hz⟩ := hsurj (R (x + y) - R x - R y)
    have h := key z
    rw [hz] at h
    have hzero : R (x + y) - R x - R y = 0 := inner_self_eq_zero.mp h
    have hsub : R (x + y) - R x = R y := sub_eq_zero.mp hzero
    rw [← hsub]
    abel
  have hsmul : ∀ (c : ℝ) (x : Submission.Mostow.E m), R (c • x) = c • R x := by
    intro c x
    have key : ∀ z : Submission.Mostow.E m, inner ℝ (R (c • x) - c • R x) (R z) = 0 := by
      intro z
      have h1 : inner ℝ (R (c • x)) (R z) = c * inner ℝ x z := by
        rw [hinner, inner_smul_left]
        simp
      have h2 : inner ℝ (c • R x) (R z) = c * inner ℝ x z := by
        rw [inner_smul_left, hinner]
        simp
      rw [inner_sub_left, h1, h2, sub_self]
    obtain ⟨z, hz⟩ := hsurj (R (c • x) - c • R x)
    have h := key z
    rw [hz] at h
    have hzero : R (c • x) - c • R x = 0 := inner_self_eq_zero.mp h
    rw [sub_eq_zero] at hzero
    exact hzero
  let L : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m :=
    { toFun := R, map_add' := hadd, map_smul' := hsmul }
  have hinjL : Function.Injective L := by
    intro x y hxy
    have hd : R (x - y) = 0 := by
      have : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      exact this
    have hinner0 : inner ℝ (x - y) (x - y) = 0 := by
      rw [← hinner (x - y) (x - y), hd]
      simp
    have := inner_self_eq_zero.mp hinner0
    rwa [sub_eq_zero] at this
  have hsurjL : Function.Surjective L := fun y => by
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨z, hz⟩
  let e : Submission.Mostow.E m ≃ₗ[ℝ] Submission.Mostow.E m :=
    LinearEquiv.ofBijective L ⟨hinjL, hsurjL⟩
  exact ⟨{ toLinearEquiv := e, norm_map' := fun x => hnorm x }, fun x => rfl⟩

end Work.Mostow
