import Mathlib
import Submission.Work.HP.LatRecurseDefs

namespace Work.HP.Sig2

/-- The elementary facts about the orthogonal projection `Work.HP.projPerp x` onto `(ℝ x)^⊥`
used by the Schmidt recursion: closed form, vanishing on `x`, orthogonality, norm decrease,
kernel description and the orthogonal decomposition. -/
theorem projPerpFacts {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    Work.HP.projPerp x y = y - (‖x‖ ^ 2)⁻¹ • (inner ℝ x y • x) ∧
    Work.HP.projPerp x x = 0 ∧
    inner ℝ x (Work.HP.projPerp x y) = 0 ∧
    ‖Work.HP.projPerp x y‖ ≤ ‖y‖ ∧
    (Work.HP.projPerp x y = 0 ↔ ∃ c : ℝ, y = c • x) ∧
    y = ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) • x + Work.HP.projPerp x y := by
  -- Closed form with the scalar pulled out to the front.
  have happ : ∀ z : E, Work.HP.projPerp x z = z - ((‖x‖ ^ 2)⁻¹ * inner ℝ x z) • x := by
    intro z; simp [Work.HP.projPerp, smul_smul]
  -- `(‖x‖²)⁻¹ * ‖x‖²` acts as `1` on `x` (true also when `x = 0`).
  have hA : ((‖x‖ ^ 2)⁻¹ * ‖x‖ ^ 2) • x = x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)), one_smul]
  have hzero : Work.HP.projPerp x x = 0 := by
    rw [happ x, real_inner_self_eq_norm_sq, hA, sub_self]
  -- The scalar cancels against `‖x‖²`.
  have hkey : ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) * ‖x‖ ^ 2 = inner ℝ x y := by
    by_cases hx : x = 0
    · simp [hx]
    · have hne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
      calc ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) * ‖x‖ ^ 2
          = inner ℝ x y * ((‖x‖ ^ 2)⁻¹ * ‖x‖ ^ 2) := by ring
        _ = inner ℝ x y * 1 := by rw [inv_mul_cancel₀ hne]
        _ = inner ℝ x y := by rw [mul_one]
  have horth : inner ℝ x (Work.HP.projPerp x y) = 0 := by
    rw [happ y, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hkey, sub_self]
  have hpx : inner ℝ (Work.HP.projPerp x y) x = 0 := by
    rw [real_inner_comm]; exact horth
  -- Pythagoras: `⟪p, p⟫ = ⟪p, y⟫` since `⟪p, x⟫ = 0`.
  have hpp : inner ℝ (Work.HP.projPerp x y) (Work.HP.projPerp x y) =
      inner ℝ (Work.HP.projPerp x y) y := by
    calc inner ℝ (Work.HP.projPerp x y) (Work.HP.projPerp x y)
        = inner ℝ (Work.HP.projPerp x y)
            (y - ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) • x) := by rw [happ y]
      _ = inner ℝ (Work.HP.projPerp x y) y -
            inner ℝ (Work.HP.projPerp x y)
              (((‖x‖ ^ 2)⁻¹ * inner ℝ x y) • x) := inner_sub_right _ _ _
      _ = inner ℝ (Work.HP.projPerp x y) y -
            ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) *
              inner ℝ (Work.HP.projPerp x y) x := by rw [real_inner_smul_right]
      _ = inner ℝ (Work.HP.projPerp x y) y := by rw [hpx, mul_zero, sub_zero]
  have hnorm2 : ‖Work.HP.projPerp x y‖ ^ 2 ≤ ‖Work.HP.projPerp x y‖ * ‖y‖ := by
    calc ‖Work.HP.projPerp x y‖ ^ 2
        = inner ℝ (Work.HP.projPerp x y) (Work.HP.projPerp x y) :=
          (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (Work.HP.projPerp x y) y := hpp
      _ ≤ ‖Work.HP.projPerp x y‖ * ‖y‖ := real_inner_le_norm _ _
  have hnorm : ‖Work.HP.projPerp x y‖ ≤ ‖y‖ := by
    by_cases h0 : ‖Work.HP.projPerp x y‖ = 0
    · rw [h0]; exact norm_nonneg y
    · have hpos : 0 < ‖Work.HP.projPerp x y‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h2 : ‖Work.HP.projPerp x y‖ * ‖Work.HP.projPerp x y‖ ≤
          ‖Work.HP.projPerp x y‖ * ‖y‖ := by
        rwa [pow_two] at hnorm2
      exact (mul_le_mul_iff_of_pos_left hpos).mp h2
  have hker : Work.HP.projPerp x y = 0 ↔ ∃ c : ℝ, y = c • x := by
    constructor
    · intro h
      have h' : y - ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) • x = 0 := by rw [← happ y]; exact h
      exact ⟨_, sub_eq_zero.mp h'⟩
    · rintro ⟨c, rfl⟩
      rw [LinearMap.map_smul, hzero, smul_zero]
  have hdecomp : y = ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) • x + Work.HP.projPerp x y := by
    rw [happ y]; abel
  have h1 : Work.HP.projPerp x y = y - (‖x‖ ^ 2)⁻¹ • (inner ℝ x y • x) := by
    simp [Work.HP.projPerp]
  exact ⟨h1, hzero, horth, hnorm, hker, hdecomp⟩

end Work.HP.Sig2
