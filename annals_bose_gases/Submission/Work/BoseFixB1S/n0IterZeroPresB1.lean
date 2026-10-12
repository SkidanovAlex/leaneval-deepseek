import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.n0SpectralDefs
import Submission.Work.BoseFixB1S.n0ZeroOffPIndPresB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **The slot iteration preserves vanishing off the box in slot `i`.**  If `Ψ` vanishes at every
configuration whose `i`-th coordinate lies outside `A`, then so does `n0Iter volA A b l Ψ`: the slot
operator at any slot `j` is a combination of `P_{B,j}` and `1 − P_{B,j}`, and both the box
projection `P_{B,j}` (`BoseFixB1S.n0ZeroOffPIndPresB1`) and the pointwise difference preserve this
vanishing, whence the induction over the slot list. -/
theorem n0IterZeroPresB1 {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N}
    (b : Fin N → Bool) (l : List (Fin N))
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x : Submission.BoseGases.X N, x i ∉ A → Ψ x = 0) :
    ∀ x : Submission.BoseGases.X N, x i ∉ A →
      Work.BoseFixB1S.n0Iter volA A b l Ψ x = 0 := by
  induction l generalizing Ψ with
  | nil => intro x hx; exact hΨ x hx
  | cons j l ih =>
      intro x hx
      rw [Work.BoseFixB1S.n0Iter]
      by_cases hb : b j
      · rw [if_pos hb]
        exact ih (fun y hy => Work.BoseFixB1S.n0ZeroOffPIndPresB1 hΨ j y hy) x hx
      · rw [if_neg hb]
        refine ih (fun y hy => ?_) x hx
        rw [hΨ y hy, Work.BoseFixB1S.n0ZeroOffPIndPresB1 hΨ j y hy, sub_zero]

end Work.BoseFixB1S
