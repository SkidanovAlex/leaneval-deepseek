import Mathlib
import Submission.Work.A14.defs

namespace Work.A14D

/-- `DyIter (k+1) f = Dy (DyIter k f)`. -/
lemma DyIter_succ_local (k : ℕ) (f : ℂ → ℂ) :
    DyIter (k + 1) f = Dy (DyIter k f) := by
  have := Function.iterate_succ_apply' Dy k f
  simp only [DyIter] at this ⊢
  exact this

/-- The factor `(z-1)²/(z²-2z)` of `Dy` is holomorphic on any set avoiding `0` and `2`. -/
lemma dy_factor_diffOn_of_isOpen {S : Set ℂ} (h0 : (0 : ℂ) ∉ S) (h2 : (2 : ℂ) ∉ S) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2 / (z ^ 2 - 2 * z)) S := by
  refine DifferentiableOn.div ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    ((differentiableOn_id.pow 2).sub ((differentiableOn_const 2).mul differentiableOn_id))
    ?_
  intro z hz
  rw [show z ^ 2 - 2 * z = z * (z - 2) by ring]
  exact mul_ne_zero (fun h => h0 (h ▸ hz)) (sub_ne_zero.mpr (fun h => h2 (h ▸ hz)))

theorem DyIter_diffOn_of_isOpen {S : Set ℂ} (hSo : IsOpen S) (h0 : (0 : ℂ) ∉ S) (h2 : (2 : ℂ) ∉ S)
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A S) :
    ∀ k : ℕ, DifferentiableOn ℂ (Work.A14D.DyIter k A) S := by
  have hg := dy_factor_diffOn_of_isOpen h0 h2
  intro k
  induction k with
  | zero =>
      rw [DyIter, Function.iterate_zero]
      simpa using hA
  | succ k ih =>
      rw [DyIter_succ_local]
      have hfun : Dy (DyIter k A)
          = fun z : ℂ => deriv (DyIter k A) z * ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) := by
        funext z
        simp only [Dy]
        rw [mul_div_assoc]
      rw [hfun]
      exact (ih.deriv hSo).mul hg

end Work.A14D
