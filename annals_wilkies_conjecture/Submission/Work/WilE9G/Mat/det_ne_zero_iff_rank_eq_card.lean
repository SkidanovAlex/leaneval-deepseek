import Mathlib

namespace Work.WilE9G.Mat

theorem det_ne_zero_iff_rank_eq_card {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    A.det ≠ 0 ↔ A.rank = m := by
  constructor
  · intro h
    simpa using (Matrix.rank_of_det_ne_zero (A := A) h)
  · intro h
    have hrank : Module.finrank ℝ (LinearMap.range A.mulVecLin) = Module.finrank ℝ (Fin m → ℝ) := by
      rw [Module.finrank_pi, Fintype.card_fin]
      exact h
    have htop : LinearMap.range A.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq hrank
    have hsurj : Function.Surjective A.mulVec := by
      have h1 := LinearMap.range_eq_top.mp htop
      simpa [Matrix.coe_mulVecLin] using h1
    have hunit : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    have hdetunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
    exact isUnit_iff_ne_zero.mp hdetunit

end Work.WilE9G.Mat
