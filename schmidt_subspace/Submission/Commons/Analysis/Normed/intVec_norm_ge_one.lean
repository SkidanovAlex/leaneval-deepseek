import Mathlib.Analysis.Normed.Ring.Lemmas

namespace Commons.Analysis.Normed

theorem intVec_norm_ge_one {σ : Type*} [Fintype σ] (x : σ → ℤ) (hx : x ≠ 0) :
    (1 : ℝ) ≤ ‖x‖ := by
  classical
  have hnon : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hnon with ⟨i, hi⟩
  have hzi : (1 : ℝ) ≤ ‖x i‖ := by
    have hnorm : ‖x i‖ = ((x i).natAbs : ℝ) := by
      rw [Int.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]
      simp
    rw [hnorm]
    exact_mod_cast (show 1 ≤ (x i).natAbs from by
      have hpos : 0 < (x i).natAbs := Int.natAbs_pos.mpr hi
      omega)
  exact le_trans hzi (norm_le_pi_norm x i)

end Commons.Analysis.Normed