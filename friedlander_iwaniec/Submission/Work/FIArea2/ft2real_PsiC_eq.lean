import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs
import Submission.Work.FIArea2.sec6_change_of_variables

namespace Work.FIArea2

/-- The algebraic identity behind the scaling comparison of (6.9): for `D, n > 0`,
`√(D/√n) = D/√(D√n)`.  Both sides are the `√(|Δ|/|z|)` of §6 rewritten through the frequency
denominator `√(|Δz|)` of (6.9). -/
private lemma sqrt_div_sqrt_eq (D n : ℝ) (hD : 0 < D) (hn : 0 < n) :
    Real.sqrt (D / Real.sqrt n) = D / Real.sqrt (D * Real.sqrt n) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hB : 0 < Real.sqrt (D * Real.sqrt n) := Real.sqrt_pos.2 (mul_pos hD hs)
  have hsq : (D / Real.sqrt (D * Real.sqrt n)) ^ 2 = D / Real.sqrt n := by
    rw [div_pow, Real.sq_sqrt (le_of_lt (mul_pos hD hs))]
    field_simp
  have h1 := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (le_of_lt (div_pos hD hB))] at h1
  exact h1.symm

theorem ft2real_PsiC_eq (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hm : Work.FIPlan.absDelta z1 z2 ≠ 0) (u₁ u₂ : ℝ) :
    Work.FIArea2.ft2real (Work.FIArea2.PsiC F z1 z2)
        (u₁ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
        (u₂ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
      = (Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2)
          * Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2)
              (-u₁ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
              (-u₂ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))) := by
  have hD : (0:ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hz1 : z1 ≠ 0 := by
    intro h; exact hm (by simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h])
  have hz2 : z2 ≠ 0 := by
    intro h; exact hm (by simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h])
  have hn1 : (0:ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero hz1
  have hn2 : (0:ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero hz2
  -- the two scalings rewritten through the frequency denominators of (6.9)
  have hS1 : Work.FIArea2.secScale₁ z1 z2
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
    rw [Work.FIArea2.secScale₁]
    exact sqrt_div_sqrt_eq _ _ hD hn2
  have hS2 : Work.FIArea2.secScale₂ z1 z2
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) := by
    rw [Work.FIArea2.secScale₂]
    exact sqrt_div_sqrt_eq _ _ hD hn1
  -- consequently `s_j · (u_j/|Δ|) = u_j/√(|Δz_{3−j}|)`
  have harg1 : Work.FIArea2.secScale₁ z1 z2
        * (u₁ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
      = u₁ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
    rw [hS1]
    field_simp
  have harg2 : Work.FIArea2.secScale₂ z1 z2
        * (u₂ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
      = u₂ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) := by
    rw [hS2]
    field_simp
  -- identify the paper's `F(·,·)` of (6.8) with `ft2real` at the underlying frequency
  have hFint : Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2)
        (-u₁ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
        (-u₂ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
      = Work.FIArea2.ft2real
          (fun t => ((F (Work.FIArea2.gQuartic (Work.FIArea2.gamOf z1 z2) t) : ℝ) : ℂ))
          (u₁ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
          (u₂ / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))) := by
    rw [neg_div, neg_div]
    exact Work.FIArea2.Fint_eq_ft2real F (Work.FIArea2.gamOf z1 z2) _ _
  -- the §6 change of variables, then the substitution of the frequencies
  rw [show (Work.FIArea2.PsiC F z1 z2)
        = fun t : ℝ × ℝ => ((Work.FIArea2.phiOf F z1 z2 t : ℝ) : ℂ) from rfl]
  rw [Work.FIArea2.sec6_change_of_variables F z1 z2 hm
        (u₁ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
        (u₂ / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))]
  rw [hFint, harg1, harg2]

end Work.FIArea2
