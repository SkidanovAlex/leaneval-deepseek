/-
# Auxiliary definitions for `Work.HP.DN.realSolCone_facts_alt`

The real-soluble cone is `realSolCone d n = {t | ∃ x ≠ 0, formEvalR d n t x = 0}`.  The proof of
`realSolCone_facts_alt` splits the coefficient space of forms into

* `posCone d n` : the forms that are strictly positive on the *punctured* space `x ≠ 0`;
* `negCone d n` : the forms that are strictly negative on it.

For `d` even, these two are convex cones whose union is the complement of `realSolCone d n`, so
the frontier of the cone is contained in the union of the frontiers of two convex sets, which is
null by `Convex.addHaar_frontier`; the frontier of the Euclidean unit ball is null for the same
reason, and `frontier (s ∩ t) ⊆ frontier s ∪ frontier t` finishes the argument.
-/
import Mathlib
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.evaldefs

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory Pointwise

namespace Work.HP.DN

open Work.HP

/-- The set of forms that are strictly positive on the punctured space `ℝ^{n+1} \ {0}`. -/
def posCone (d n : ℕ) : Set (Mon d n → ℝ) :=
  {t | ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → 0 < formEvalR d n t x}

/-- The set of forms that are strictly negative on the punctured space `ℝ^{n+1} \ {0}`. -/
def negCone (d n : ℕ) : Set (Mon d n → ℝ) :=
  {t | ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → formEvalR d n t x < 0}

/-- `formEvalR` is additive in the coefficient vector. -/
lemma formEvalR_add_coeff (d n : ℕ) (a b : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) :
    formEvalR d n (a + b) x = formEvalR d n a x + formEvalR d n b x := by
  simp only [formEvalR, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `formEvalR d n t`, as a function of `x`, is continuous. -/
lemma continuous_formEvalR_vec (d n : ℕ) (t : Mon d n → ℝ) :
    Continuous fun x : Fin (n + 1) → ℝ => formEvalR d n t x := by
  simp only [formEvalR, veronese]
  exact continuous_finsetSum _ fun m _ =>
    continuous_const.mul (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)

/-- A nonzero vector of `Fin (n+1) → ℝ` exists. -/
lemma exists_ne_zero_vec (n : ℕ) : ∃ x : Fin (n + 1) → ℝ, x ≠ 0 := by
  refine ⟨Pi.single (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) (1 : ℝ), ?_⟩
  intro h
  have h0 := congrFun h (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))
  rw [Pi.single_eq_same] at h0
  exact one_ne_zero h0

end Work.HP.DN
