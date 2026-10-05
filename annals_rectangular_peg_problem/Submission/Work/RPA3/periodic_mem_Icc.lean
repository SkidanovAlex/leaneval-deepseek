import Mathlib

namespace Work.RPA3

/-- Every value of a `T`-periodic function with `T > 0` is attained at a point of `[0,T]`. -/
theorem periodic_mem_Icc {V : Type*} {T : ℝ} (hT : 0 < T) (g : ℝ → V)
    (hg : Function.Periodic g T) (t : ℝ) :
    ∃ t0 ∈ Set.Icc (0:ℝ) T, g t = g t0 := by
  refine ⟨t - ⌊t / T⌋ * T, ⟨?_, ?_⟩, (hg.sub_int_mul_eq ⌊t / T⌋).symm⟩
  · have h1 : ((⌊t / T⌋ : ℤ) : ℝ) ≤ t / T := Int.floor_le _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hT)
    rw [div_mul_cancel₀ t hT.ne'] at h2
    linarith
  · have h1 : t / T < ((⌊t / T⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 := mul_lt_mul_of_pos_right h1 hT
    rw [div_mul_cancel₀ t hT.ne'] at h2
    have h3 : (((⌊t / T⌋ : ℤ) : ℝ) + 1) * T = ((⌊t / T⌋ : ℤ) : ℝ) * T + T := by ring
    rw [h3] at h2
    linarith

end Work.RPA3
