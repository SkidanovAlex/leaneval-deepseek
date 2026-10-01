/-
# ZeroFreeTables/P9/NearSummandDefs — the summand of `nearP3sum` as a named function

The definition `nearP3sum` of `P9/Defs.lean` is a `tsum` of the function defined below
(definitionally).  Naming it makes the pointwise lemmas about the summand
(non-negativity, finite support, comparison with a single `P₃`-term) statable and usable.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3Pos

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

/-- The summand of `nearP3sum`: multiplicity times the `δ`-window indicator times `Re P₃` of
the argument, written through the three terms of `P₃`. -/
def nearP3summand (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ δ : ℝ) (u : ℂ) : ℝ :=
  (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
    ( ((a + lam₁) / L) * ((1 / (s - u))).re
      + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
      + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re)

/-- `nearP3sum` is the `tsum` of its summand (definitional). -/
lemma nearP3sum_eq_tsum (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ δ : ℝ) :
    nearP3sum N L χ s a lam₁ δ = ∑' u : ℂ, nearP3summand N L χ s a lam₁ δ u := rfl

/-- The summand rewritten with `Re P₃` in place of the three-term expansion. -/
lemma nearP3summand_eq_P3 (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ δ : ℝ) (u : ℂ) :
    nearP3summand N L χ s a lam₁ δ u
      = (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
          (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by
  unfold nearP3summand
  rw [P3_re_div_eq]

end Work.ZeroFreeTables.P9
