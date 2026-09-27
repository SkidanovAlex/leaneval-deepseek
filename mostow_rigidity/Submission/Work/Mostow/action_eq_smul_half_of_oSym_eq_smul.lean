import Mathlib
import Submission.Work.Mostow.abelianBlockDefs
import Submission.Work.Mostow.isometryEqOfSymPartEq

namespace Work.Mostow

/-- If the symmetric part `oSym T = T + T⁻¹` is the scalar `a` on a nonzero subspace `W`, and
`a ^ 2` is not `< 4`, then `a / 2 = ±1` and `T` acts on `W` by the scalar `a / 2`. -/
theorem action_eq_smul_half_of_oSym_eq_smul {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (T : V ≃ₗᵢ[ℝ] V) (W : Submodule ℝ V) (hWne : W ≠ ⊥)
    (hTW : ∀ x ∈ W, T x ∈ W) (a : ℝ) (ha : ∀ x ∈ W, oSym T x = a • x)
    (h4 : ¬ a ^ 2 < 4) :
    (∀ x ∈ W, T x = (a / 2) • x) ∧ (a / 2 = 1 ∨ a / 2 = -1) := by
  -- Quadratic relation on `W`: applying the scalar hypothesis to `T x` (which stays in `W`)
  -- gives `T (T x) + x = a • T x`.
  have hquad : ∀ x ∈ W, T (T x) = a • T x - x := by
    intro x hx
    have h : T (T x) + T.symm (T x) = a • T x := by
      simpa only [oSym_apply, LinearIsometryEquiv.coe_inv] using ha (T x) (hTW x hx)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    rw [eq_sub_iff_add_eq]
    exact h
  -- The scalar `a` satisfies `|a| ≤ 2` (Cauchy–Schwarz).
  have hbound : a ^ 2 ≤ 4 := by
    obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hWne
    have hr : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have hb0 : |inner ℝ x (T x)| ≤ ‖x‖ ^ 2 := by
      have h := abs_real_inner_le_norm x (T x)
      rw [LinearIsometryEquiv.norm_map T x] at h
      simpa [pow_two] using h
    have hb1 : |inner ℝ (T x) (T (T x))| ≤ ‖x‖ ^ 2 := by
      have h := abs_real_inner_le_norm (T x) (T (T x))
      rw [LinearIsometryEquiv.norm_map T x, LinearIsometryEquiv.norm_map T (T x),
          LinearIsometryEquiv.norm_map T x] at h
      simpa [pow_two] using h
    have hq := hquad x hxW
    have hb1' : inner ℝ (T x) (T (T x)) = a * ‖x‖ ^ 2 - inner ℝ x (T x) := by
      rw [hq, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        ← real_inner_comm x (T x), LinearIsometryEquiv.norm_map T x]
    have hsum : a * ‖x‖ ^ 2 = inner ℝ x (T x) + inner ℝ (T x) (T (T x)) := by
      rw [hb1']; ring
    have hfin : |a| * ‖x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
      calc |a| * ‖x‖ ^ 2
          = |a * ‖x‖ ^ 2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
        _ = |inner ℝ x (T x) + inner ℝ (T x) (T (T x))| := by rw [hsum]
        _ ≤ |inner ℝ x (T x)| + |inner ℝ (T x) (T (T x))| := abs_add_le _ _
        _ ≤ ‖x‖ ^ 2 + ‖x‖ ^ 2 := add_le_add hb0 hb1
        _ = 2 * ‖x‖ ^ 2 := by ring
    have habs : |a| ≤ 2 := le_of_mul_le_mul_right hfin hr
    have h := abs_le.mp habs
    nlinarith [h.1, h.2]
  -- With `a ^ 2 ≥ 4` from the hypothesis, `a ^ 2 = 4`, so `a = ±2`.
  have ha2 : a = 2 ∨ a = -2 := by
    have h : a ^ 2 = 4 := le_antisymm hbound (not_lt.mp h4)
    have hfac : (a - 2) * (a + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · left; linarith
    · right; linarith
  have hc : a / 2 = 1 ∨ a / 2 = -1 := by
    rcases ha2 with rfl | rfl
    · left; norm_num
    · right; norm_num
  refine ⟨?_, hc⟩
  refine isometryEqOfSymPartEq T W hTW (a / 2) hc ?_
  intro x hx
  have h' : T x + T.symm x = a • x := by
    simpa only [oSym_apply, LinearIsometryEquiv.coe_inv] using ha x hx
  rw [h', smul_smul]
  rw [show (2:ℝ)⁻¹ * a = a / 2 by ring]

end Work.Mostow
