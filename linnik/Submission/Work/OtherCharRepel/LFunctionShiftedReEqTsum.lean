import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.LFunctionLogDerivReEqTsum
import Submission.Work.LinnikAreas.repelOtherAux.twistedNonneg

namespace Work.OtherCharRepel

theorem LFunctionShiftedReEqTsum {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (t : ℝ)
    {σ : ℝ} (hσ : 1 < σ) :
    (-(logDeriv (DirichletCharacter.LFunction ψ) ((σ : ℂ) + Complex.I * (t : ℂ)))).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
          * (ψ (n : ZMod N) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))).re
          * (n : ℝ) ^ (-σ) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hs_def
  have hsr : s.re = σ := by rw [hs_def]; simp
  have hs : 1 < s.re := by rw [hsr]; exact hσ
  have h1 := Work.LinnikAreas.OtherCharAux.LFunctionLogDerivReEqTsum_complex ψ (s := s) hs
  rw [Complex.neg_re, h1, neg_neg]
  refine tsum_congr (fun n => ?_)
  have hsplit : (n : ℂ) ^ (-s)
      = Complex.ofReal ((n : ℝ) ^ (-σ)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
    rcases eq_or_ne n 0 with rfl | hn0
    · have hz0 : -s ≠ 0 := by
        intro h
        have h2 := congrArg Complex.re h
        rw [Complex.neg_re] at h2
        simp at h2
        rw [hsr] at h2
        linarith
      have hz1 : ((-σ : ℝ)) ≠ 0 := by linarith
      simp only [Nat.cast_zero, Complex.zero_cpow hz0, Real.zero_rpow hz1,
        Complex.ofReal_zero, zero_mul]
    · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have hne : (n : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_natCast]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      have hexp : -s = (-(σ : ℂ)) + (-(Complex.I * (t : ℂ))) := by rw [hs_def]; ring
      rw [hexp, Complex.cpow_add _ _ hne]
      congr 1
      rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by simp]
      exact (Complex.ofReal_cpow (le_of_lt hpos) (-σ)).symm
  rw [hsplit]
  rw [show ψ (n : ZMod N) * (Complex.ofReal ((n : ℝ) ^ (-σ)) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))))
      = Complex.ofReal ((n : ℝ) ^ (-σ))
          * (ψ (n : ZMod N) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) by ring]
  rw [Complex.re_ofReal_mul]
  ring

end Work.OtherCharRepel
