import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.abs_exp_freeze_sub_le
import Submission.Work.Deep.Reed.Prob.freeze_exp
import Submission.Work.Deep.Reed.Prob.FunDepends

/-!
# Freezing a coordinate the function does not depend on

If `Z` depends only on the coordinates in `S` and `g ∉ S`, then replacing the `g`-marginal of a
product measure by the point mass at `c` leaves `E[Z]` unchanged.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

/-- Freezing a coordinate that `Z` does not depend on does not change the expectation of `Z`. -/
theorem freeze_exp_of_depends {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, FinProb (Ω i)) {g : ι} {S : Finset ι}
    (hg : g ∉ S) {Z : (∀ i, Ω i) → ℝ} (hZ : FunDepends S Z) (c : Ω g) :
    (FinProb.pi (FinProb.freeze ν g c)).exp Z = (FinProb.pi ν).exp Z := by
  classical
  have hupd : ∀ (f : ∀ i, Ω i) (y : Ω g), Z (Function.update f g y) = Z f := by
    intro f y
    refine hZ (Function.update f g y) f ?_
    intro i hi
    have hne : i ≠ g := by
      rintro rfl
      exact hg hi
    exact Function.update_of_ne hne y f
  have hall : ∀ x : Ω g, (FinProb.pi (FinProb.freeze ν g x)).exp Z
      = (FinProb.pi (FinProb.freeze ν g c)).exp Z := by
    intro x
    have h := abs_exp_freeze_sub_le ν g Z (D := 0) le_rfl
      (fun f y => by rw [hupd f y, sub_self, abs_zero]) x c
    have h0 : |(FinProb.pi (FinProb.freeze ν g x)).exp Z
        - (FinProb.pi (FinProb.freeze ν g c)).exp Z| = 0 := le_antisymm h (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h0)
  refine (calc (FinProb.pi ν).exp Z
      = ∑ x : Ω g, (ν g).wt x * (FinProb.pi (FinProb.freeze ν g x)).exp Z :=
        freeze_exp ν g Z
    _ = ∑ x : Ω g, (ν g).wt x * (FinProb.pi (FinProb.freeze ν g c)).exp Z := by
        refine Finset.sum_congr rfl fun x _ => by rw [hall x]
    _ = (∑ x : Ω g, (ν g).wt x) * (FinProb.pi (FinProb.freeze ν g c)).exp Z := by
        rw [Finset.sum_mul]
    _ = (FinProb.pi (FinProb.freeze ν g c)).exp Z := by rw [(ν g).wt_sum, one_mul]).symm

end Work.Deep.Reed.Prob
