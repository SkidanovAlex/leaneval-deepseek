import Mathlib.Analysis.InnerProductSpace.PiL2

open WithLp

namespace Commons.Analysis.InnerProductSpace

/-- Elementary scalar identity underlying the Schur-complement energy computation
for a self-adjoint block operator `[[A, b],[bᵀ, c]]`. -/
lemma schur_arith (X Y Z c t : ℝ) (hZ : c - Z ≠ 0) :
    (X + t * Y) + t * (Y + c * t)
      = (X + 2 * t * Y + t^2 * Z) + ((Y + c * t) - (Y + t * Z))^2 / (c - Z) := by
  field_simp
  ring

set_option linter.unusedVariables false in
theorem schur_block_energy3 {n : ℕ}
    (T : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))
    (A Ainv : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hAL : ∀ u, Ainv (A u) = u) (hAR : ∀ u, A (Ainv u) = u)
    (hAsym : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hAisym : ∀ u v, inner ℝ (Ainv u) v = inner ℝ u (Ainv v))
    (b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hblock : ∀ (u : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      T (WithLp.toLp 2 (u, t)) = WithLp.toLp 2 (A u + t • b, inner ℝ u b + c * t))
    (hs : c - inner ℝ (Ainv b) b ≠ 0)
    (v₁ w₁ : EuclideanSpace ℝ (Fin n)) (v₂ w₂ : ℝ)
    (hv : T (WithLp.toLp 2 (v₁, v₂)) = WithLp.toLp 2 (w₁, w₂)) :
    inner ℝ v₁ w₁ + v₂ * w₂ = inner ℝ (Ainv w₁) w₁
      + (w₂ - inner ℝ (Ainv b) w₁) ^ 2 / (c - inner ℝ (Ainv b) b) := by
  -- Read off the coordinates of the equation `T (v₁, v₂) = (w₁, w₂)`.
  have hkey := congrArg WithLp.ofLp hv
  rw [hblock] at hkey
  have hw1 : w₁ = A v₁ + v₂ • b := (congrArg Prod.fst hkey).symm
  have hw2 : w₂ = inner ℝ v₁ b + c * v₂ := (congrArg Prod.snd hkey).symm
  rw [hw1, hw2]
  -- Compute the three inner products appearing in the identity.
  have e1 : inner ℝ v₁ (A v₁ + v₂ • b) = inner ℝ v₁ (A v₁) + v₂ * inner ℝ v₁ b := by
    rw [inner_add_right, inner_smul_right]
  have e2 : inner ℝ (Ainv (A v₁ + v₂ • b)) (A v₁ + v₂ • b)
      = inner ℝ v₁ (A v₁) + 2 * v₂ * inner ℝ v₁ b + v₂^2 * inner ℝ (Ainv b) b := by
    rw [map_add, map_smul, hAL]
    rw [inner_add_left, inner_add_right, inner_add_right]
    rw [inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_left]
    rw [← hAsym (Ainv b) v₁, hAR b]
    rw [real_inner_comm b v₁]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have e3 : inner ℝ (Ainv b) (A v₁ + v₂ • b) = inner ℝ v₁ b + v₂ * inner ℝ (Ainv b) b := by
    rw [inner_add_right, inner_smul_right]
    rw [← hAsym (Ainv b) v₁, hAR b]
    rw [real_inner_comm b v₁]
  rw [e1, e2, e3]
  exact schur_arith _ _ _ _ _ hs

end Commons.Analysis.InnerProductSpace