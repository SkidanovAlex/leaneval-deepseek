import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Polynomial Finset Real Complex

/-- Conjugation of the additive character: `star (e(t)) = e(-t)`. -/
lemma star_exp (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) := by
  have h := Complex.exp_conj z
  simp only [starRingEnd_apply] at h
  exact h.symm

/-- `star (e(t)) = e(-t)`. -/
lemma star_eC (t : ℝ) : star (Work.BMF.eC t) = Work.BMF.eC (-t) := by
  rw [Work.BMF.eC, Work.BMF.eC, star_exp]
  congr 1
  simp

/-- The additive character is a character: `e(a) * e(b) = e(a + b)`. -/
lemma eC_add (a b : ℝ) : Work.BMF.eC a * Work.BMF.eC b = Work.BMF.eC (a + b) := by
  rw [Work.BMF.eC, Work.BMF.eC, Work.BMF.eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For a finite set `s` of naturals and two real polynomials `P`, `Q`, the sum of the
pointwise Gram entries `eC(-P(n)) * conj(eC(-Q(n)))` equals the conjugate of the sum of
the difference phases `eC(P(n) - Q(n))`. -/
theorem eC_conj_sum (s : Finset ℕ) (P Q : Polynomial ℝ) :
    (∑ n ∈ s, Work.BMF.eC (-(P.eval (n : ℝ))) * star (Work.BMF.eC (-(Q.eval (n : ℝ)))))
      = star (∑ n ∈ s, Work.BMF.eC (P.eval (n : ℝ) - Q.eval (n : ℝ))) := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [star_eC, star_eC, eC_add]
  congr 1
  ring

end Work.BMF.SD
