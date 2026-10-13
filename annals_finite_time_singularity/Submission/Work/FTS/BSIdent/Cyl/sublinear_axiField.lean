import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl

/-- **The no-swirl field `axiField a b` is sublinear whenever its profiles decay like
`(1 + √(w + z²))⁻¹` on the half plane `w ≥ 0`.**

Indeed, at a point `x` with `w = r² = x₀² + x₁²` and `z = x₃`, the field is
`a(r²,x₃) • (x₀,x₁,0) + b(r²,x₃) • e₃`, so

  `‖axiField a b x‖ ≤ ‖a(r²,x₃)‖ ‖(x₀,x₁,0)‖ + ‖b(r²,x₃)‖
     ≤ (C/(1+‖x‖))·r + C/(1+‖x‖) = (C/(1+‖x‖))·(1 + r) ≤ (C/(1+‖x‖))·(1+‖x‖) = C`,

because `√(r² + x₃²) = ‖x‖` and `r ≤ ‖x‖`.  So the uniform constant `C` (which is `C·(1+‖x‖)^0`)
already witnesses sublinearity. -/
theorem sublinear_axiField (a b : ℝ → ℝ → ℝ)
    (hbd : ∃ C : ℝ, 0 < C ∧ ∀ w z, 0 ≤ w →
      ‖a w z‖ ≤ C / (1 + Real.sqrt (w + z ^ 2)) ∧ ‖b w z‖ ≤ C / (1 + Real.sqrt (w + z ^ 2))) :
    Work.FTS.Physical.Sublinear (Work.Cyl.axiField a b) := by
  obtain ⟨C, hCpos, hCbd⟩ := hbd
  refine ⟨C, 0, le_of_lt hCpos, by norm_num, ?_⟩
  intro x
  rw [Real.rpow_zero, mul_one]
  -- The hypotheses at the point `x`
  have hw : 0 ≤ Work.Cyl.radSq x := Work.Cyl.radSq_nonneg x
  obtain ⟨ha, hb⟩ := hCbd (Work.Cyl.radSq x) (Work.Cyl.axial x) hw
  have hs : Real.sqrt (Work.Cyl.radSq x + Work.Cyl.axial x ^ 2) = ‖x‖ := by
    rw [← Work.Cyl.rho_eq_norm x]; rfl
  have ha' : ‖a (Work.Cyl.radSq x) (Work.Cyl.axial x)‖ ≤ C / (1 + ‖x‖) := by
    simpa only [hs] using ha
  have hb' : ‖b (Work.Cyl.radSq x) (Work.Cyl.axial x)‖ ≤ C / (1 + ‖x‖) := by
    simpa only [hs] using hb
  -- the two structural facts about the frame
  have hrv : ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := by
    have h : ‖Work.Cyl.radialVec x‖ ^ 2 = Work.Cyl.radSq x := by
      rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_radialVec_self]
    have h2 : Work.Cyl.radial x ^ 2 = Work.Cyl.radSq x := Work.Cyl.radial_sq x
    nlinarith [norm_nonneg (Work.Cyl.radialVec x), Work.Cyl.radial_nonneg x]
  have hrvle : ‖Work.Cyl.radialVec x‖ ≤ ‖x‖ := by
    rw [hrv, ← Work.Cyl.rho_eq_norm x]
    exact Work.Cyl.radial_le_rho x
  have heZ : ‖Work.Cyl.eZ‖ = 1 := by
    simp [Work.Cyl.eZ, FiniteTimeSingularity.e]
  have hden : 0 < 1 + ‖x‖ := by positivity
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hpnn : 0 ≤ C / (1 + ‖x‖) := div_nonneg hCnn hden.le
  have hstep : ‖Work.Cyl.axiField a b x‖
      ≤ C / (1 + ‖x‖) * ‖Work.Cyl.radialVec x‖ + C / (1 + ‖x‖) := by
    have h1 : ‖Work.Cyl.axiField a b x‖
        ≤ ‖a (Work.Cyl.radSq x) (Work.Cyl.axial x) • Work.Cyl.radialVec x‖
          + ‖b (Work.Cyl.radSq x) (Work.Cyl.axial x) • Work.Cyl.eZ‖ := by
      show ‖a (Work.Cyl.radSq x) (Work.Cyl.axial x) • Work.Cyl.radialVec x
            + b (Work.Cyl.radSq x) (Work.Cyl.axial x) • Work.Cyl.eZ‖ ≤ _ 
      exact norm_add_le _ _
    have h2 : ‖a (Work.Cyl.radSq x) (Work.Cyl.axial x) • Work.Cyl.radialVec x‖
          + ‖b (Work.Cyl.radSq x) (Work.Cyl.axial x) • Work.Cyl.eZ‖
        = ‖a (Work.Cyl.radSq x) (Work.Cyl.axial x)‖ * ‖Work.Cyl.radialVec x‖
          + ‖b (Work.Cyl.radSq x) (Work.Cyl.axial x)‖ * ‖Work.Cyl.eZ‖ := by
      rw [norm_smul, norm_smul]
    have h3 : ‖a (Work.Cyl.radSq x) (Work.Cyl.axial x)‖ * ‖Work.Cyl.radialVec x‖
          + ‖b (Work.Cyl.radSq x) (Work.Cyl.axial x)‖ * ‖Work.Cyl.eZ‖
        ≤ C / (1 + ‖x‖) * ‖Work.Cyl.radialVec x‖ + C / (1 + ‖x‖) := by
      have key := add_le_add
        (mul_le_mul_of_nonneg_right ha' (norm_nonneg (Work.Cyl.radialVec x)))
        (mul_le_mul_of_nonneg_right hb' (norm_nonneg (Work.Cyl.eZ)))
      simpa only [heZ, mul_one] using key
    exact h1.trans (h2.trans_le h3)
  refine hstep.trans ?_
  have hfac : C / (1 + ‖x‖) * ‖Work.Cyl.radialVec x‖ + C / (1 + ‖x‖)
      = C / (1 + ‖x‖) * (‖Work.Cyl.radialVec x‖ + 1) := by ring
  rw [hfac]
  calc C / (1 + ‖x‖) * (‖Work.Cyl.radialVec x‖ + 1)
      ≤ C / (1 + ‖x‖) * (‖x‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hpnn
    _ = C := by
        rw [add_comm (‖x‖) 1]
        exact div_mul_cancel₀ C (ne_of_gt hden)

end Work.FTS.BSIdent.Cyl
