import Mathlib.Analysis.RCLike.Lemmas

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.LinearAlgebra

/-- In a real vector space of dimension at least two, for a positive definite bilinear form `B`
(bilinear, `B v v ≥ 0`, and `B v v = 0 → v = 0`) and any vector `v` with `B v v = 1`, there is a
vector `w` with `B w w = 1` and `B w v = 0`. -/
theorem exists_ne_zero_orthogonal_of_finrank_two_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h : 2 ≤ Module.finrank ℝ E) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hpos : ∀ v, 0 ≤ B v v) (hdef : ∀ v, B v v = 0 → v = 0) (v : E) (hv : B v v = 1) :
    ∃ w : E, B w w = 1 ∧ B w v = 0 := by
  -- The linear functional `φ w = B w v` has kernel of dimension at least `finrank E - 1 ≥ 1`.
  have hfr : Module.finrank ℝ ℝ < Module.finrank ℝ E := by
    rw [Module.finrank_self]; omega
  have hker : LinearMap.ker (B.flip v) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := B.flip v) hfr
  obtain ⟨w₀, hw₀mem, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw₀v : B w₀ v = 0 := by
    have := (LinearMap.mem_ker.mp hw₀mem)
    simpa [LinearMap.flip_apply] using this
  -- `w₀ ≠ 0` and positive-definiteness give `B w₀ w₀ > 0`.
  have hx : (0 : ℝ) < B w₀ w₀ := by
    rcases lt_or_eq_of_le (hpos w₀) with hlt | heq
    · exact hlt
    · exact absurd (hdef w₀ heq.symm) hw₀ne
  set c : ℝ := (Real.sqrt (B w₀ w₀))⁻¹ with hc
  have hc2 : c * c * (B w₀ w₀) = 1 := by
    have hs : Real.sqrt (B w₀ w₀) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
    rw [hc, ← mul_inv, Real.mul_self_sqrt (le_of_lt hx), inv_mul_cancel₀ (ne_of_gt hx)]
  -- Use `hv` to record that `v` is not "null": `B v v ≠ 0`.
  have _hv : B v v ≠ 0 := by rw [hv]; norm_num
  refine ⟨c • w₀, ?_, ?_⟩
  · have hmul : B (c • w₀) (c • w₀) = c * c * (B w₀ w₀) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hmul, hc2]
  · have hmul : B (c • w₀) v = c * (B w₀ v) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hmul, hw₀v, mul_zero]

end Commons.LinearAlgebra