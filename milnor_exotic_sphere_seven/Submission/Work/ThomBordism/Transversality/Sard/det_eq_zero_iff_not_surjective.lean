import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism.Transversality.Sard

/-- For a continuous linear endomorphism of `ℝⁿ`, the determinant vanishes exactly when the map
fails to be surjective. -/
theorem det_eq_zero_iff_not_surjective {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    A.det = 0 ↔ ¬ Function.Surjective A := by
  constructor
  · intro h hsurj
    have hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 0 := by
      simpa using h
    have hlt := LinearMap.range_lt_top_of_det_eq_zero hdet
    have htop : LinearMap.range (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    exact absurd htop hlt.ne
  · intro h
    have hker : (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).ker ≠ ⊥ := by
      intro hbot
      apply h
      have hinj : Function.Injective (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
        LinearMap.ker_eq_bot.mp hbot
      have hsurj : Function.Surjective (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
        LinearMap.injective_iff_surjective.mp hinj
      exact fun y => hsurj y
    have hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 0 :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
    simpa using hdet

end Work.ThomBordism.Transversality.Sard
