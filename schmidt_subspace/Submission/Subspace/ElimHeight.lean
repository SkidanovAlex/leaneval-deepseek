import Mathlib
import Submission.Subspace.ElimIter
import Submission.Subspace.ProjRoth

/-!
# Heights and the elimination iteration

Dividing out the lowest power of a variable does not increase the height (in the `gP`
normalisation used throughout): the coefficients of `lowestCoeff y F` are coefficients of `F`.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

open Commons.NumberTheory.Height.MvPolynomial (gP mulHeight_gP_eq)

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Dividing out the lowest power of a variable does not increase the height. -/
lemma logHeight_gP_lowestCoeff_le (y : σ) (F : MvPolynomial σ ℚ) :
    Height.logHeight (gP (lowestCoeff y F)) ≤ Height.logHeight (gP F) := by
  simp only [Height.logHeight_eq_log_mulHeight]
  refine Real.log_le_log ?_ ?_
  · rw [mulHeight_gP_eq]
    exact Height.mulHeight_pos _
  · apply mulHeight_gP_le_of_coeff_map _ _ (fun t => t + Finsupp.single y (lowestDeg y F))
    intro t ht
    obtain ⟨w, hw, hwy, hwt⟩ := mem_support_lowestCoeff ht
    have h2 : (w - Finsupp.single y (lowestDeg y F)) + Finsupp.single y (lowestDeg y F) = w := by
      ext z
      rcases eq_or_ne z y with rfl | hz
      · simp [hwy]
      · simp [Finsupp.single_eq_of_ne hz]
    rw [hwt, h2]
    exact coeff_lowestCoeff_of_mem hw hwy

/-- The elimination iteration does not increase the height. -/
lemma logHeight_gP_elimF_le :
    ∀ (ys : List σ) (F : MvPolynomial σ ℚ),
      Height.logHeight (gP (elimF ys F)) ≤ Height.logHeight (gP F) := by
  intro ys
  induction ys with
  | nil => intro F; simp [elimF]
  | cons y ys ih =>
      intro F
      exact le_trans (ih (lowestCoeff y F)) (logHeight_gP_lowestCoeff_le y F)

end Submission.Subspace
