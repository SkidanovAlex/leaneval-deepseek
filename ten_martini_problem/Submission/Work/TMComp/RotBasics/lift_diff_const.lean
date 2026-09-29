import Mathlib
import Submission.Work.TMComp.RotBasics.Defs
import Submission.Work.TMC13.Basic

namespace Work.TMComp.RotBasics

/-- Two positive lifts `G, H` of the same invertible matrix `A` which are both continuous
differ by a constant even integer. -/
theorem lift_diff_const (A : Matrix (Fin 2) (Fin 2) ℝ) (G H : ℝ → ℝ) (hA : A.det ≠ 0)
    (hG : IsPosLift A G) (hH : IsPosLift A H) (hcG : Continuous G) (hcH : Continuous H) :
    ∃ m : ℤ, ∀ t : ℝ, H t = G t + 2 * (m : ℝ) := by
  -- An invertible matrix cannot kill the circle point `vc t`.
  have hker : ∀ t, smul A (vc t) ≠ 0 := by
    intro t h
    have e1 : A 0 0 * (vc t).re + A 0 1 * (vc t).im = 0 := by
      have := congrArg Complex.re h
      simpa [smul] using this
    have e2 : A 1 0 * (vc t).re + A 1 1 * (vc t).im = 0 := by
      have := congrArg Complex.im h
      simpa [smul] using this
    have hdetval : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    have hc0 : (vc t).re = 0 := by
      have h0 : A.det * (vc t).re = 0 := by
        rw [hdetval]; linear_combination A 1 1 * e1 - A 0 1 * e2
      exact (mul_eq_zero.mp h0).resolve_left hA
    have hs0 : (vc t).im = 0 := by
      have h0 : A.det * (vc t).im = 0 := by
        rw [hdetval]; linear_combination A 0 0 * e2 - A 1 0 * e1
      exact (mul_eq_zero.mp h0).resolve_left hA
    exact vc_ne_zero t (Complex.ext hc0 hs0)
  -- Hence both lifts present the same direction.
  have hvc : ∀ t, vc (H t) = vc (G t) := by
    intro t
    have h1 := hH t
    have h2 := hG t
    have heq : (‖smul A (vc t)‖ : ℝ) • vc (H t) = (‖smul A (vc t)‖ : ℝ) • vc (G t) :=
      h1.symm.trans h2
    have hn : (‖smul A (vc t)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr (hker t)
    exact smul_right_injective ℂ hn heq
  -- So `(H - G)/2` is integer-valued; continuity forces it to be constant.
  have hint : ∀ t, ∃ k : ℤ, (H t - G t) / 2 = (k : ℝ) := by
    intro t
    obtain ⟨m, hm⟩ := vc_eq_iff (hvc t)
    refine ⟨m, ?_⟩
    rw [hm]; ring
  obtain ⟨k, hk⟩ := Work.TMC13.exists_int_eq_const ((hcH.sub hcG).div_const 2) hint
  refine ⟨k, fun t => ?_⟩
  have h := hk t
  have h2 : H t - G t = 2 * (k : ℝ) := by
    have := congrArg (fun x : ℝ => 2 * x) h
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at this
    exact this
  linarith [h2]

end Work.TMComp.RotBasics
