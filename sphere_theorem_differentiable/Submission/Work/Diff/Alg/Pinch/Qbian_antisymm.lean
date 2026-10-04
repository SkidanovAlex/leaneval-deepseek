import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Antisymmetry of the Bianchi integrand of Hamilton's `Q`

Under the hypothesis pattern that the components of `R` encountered here are read off from a
single `2`-tensor `A` (`R a b p q = A a b - A b a`, `R a p b q = A a b`, and the two counterparts
with `q`), the `(p,q)`-integrand `Qbian` of the first Bianchi identity of `Q R` is antisymmetric
in `p, q`: `Qbian R i j k l p q + Qbian R i j k l q p = 0`.

This is a pure polynomial identity in the entries of `A`: after unfolding `Qbian` and `Qterm` and
rewriting the twelve components of `R` that occur, both sides become explicit polynomials.
-/

namespace Work.Diff.Alg.Pinch

/-- Antisymmetry of the Bianchi integrand of `Q` in the last two indices, for a tensor `R` whose
components are given by a `2`-tensor `A` through the four hypotheses. -/
theorem Qbian_antisymm (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (A : Fin n → Fin n → ℝ)
    (i j k l p q : Fin n)
    (h1 : ∀ a b : Fin n, R a b p q = A a b - A b a)
    (h2 : ∀ a b : Fin n, R a b q p = A b a - A a b)
    (h3 : ∀ a b : Fin n, R a p b q = A a b)
    (h4 : ∀ a b : Fin n, R a q b p = A b a) :
    Work.Diff.Alg.Pinch.Qbian R i j k l p q + Work.Diff.Alg.Pinch.Qbian R i j k l q p = 0 := by
  simp only [Work.Diff.Alg.Pinch.Qbian, Work.Diff.Alg.Pinch.Qterm, h1, h2, h3, h4]
  ring

end Work.Diff.Alg.Pinch
