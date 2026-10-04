import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `continuous_pdVec`: iterated partial derivatives of a `Cᵏ` function are continuous

`pdVec k l f = pdList (List.ofFn l) f` is the iterated partial derivative
`∂_{l 0} ⋯ ∂_{l (k-1)} f` (see `Torus.lean`).  Each `pd i` lowers the order of
differentiability by one (`contDiff_pd_of_contDiff`, proved in `fourierCoeff_pdVec`), so a
list of `k` directions applied to a `Cᵏ` function lands in `C⁰`, i.e. it is continuous.

The auxiliary lemma `contDiff_pdList_of_contDiff` is the iteration: for a list `t` of length
`m`, a `C^{m+n}` function has `pdList t f` of class `Cⁿ`.  It is stated with `t.length + n`
(rather than `n + t.length`) so that the induction step on `List.foldr` (which peels the head,
`pdList (i :: t) f = pd i (pdList t f)`) is a direct application of the two ingredients.
-/

noncomputable section

namespace Work.Diff.STE

/-- **Iterated partial derivatives lower regularity.**  If `f` is `C^{t.length + n)}` then the
iterated derivative `pdList t f` is `Cⁿ`. -/
lemma contDiff_pdList_of_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι] (t : List ι) :
    ∀ (n : ℕ) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ ((t.length + n : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (n : WithTop ℕ∞) (pdList t f) := by
  induction t with
  | nil => intro n f hf; simpa [pdList] using hf
  | cons i t ih =>
      intro n f hf
      have h1 : (t.length + (n + 1) : ℕ) = ((i :: t).length + n : ℕ) := by
        simp [List.length_cons]; omega
      rw [← h1] at hf
      have hrec : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (pdList t f) := ih (n + 1) f hf
      have hstep : ContDiff ℝ (n : WithTop ℕ∞) (pd i (pdList t f)) :=
        contDiff_pd_of_contDiff i (n := n + 1) (m := n) hrec (le_refl _)
      simpa [pdList] using hstep

theorem continuous_pdVec {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (l : Fin k → ι)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ k f) : Continuous (Work.Diff.STE.pdVec k l f) := by
  have h := contDiff_pdList_of_contDiff (List.ofFn l) 0 f (by
    simpa [List.length_ofFn] using hf)
  simpa [pdVec] using h.continuous

end Work.Diff.STE
