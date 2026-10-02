import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces
import Submission.Work.Deep.Prob.LLL.lovaszLocalLemma_lopsided

namespace Work.Deep.Prob.LLL

/-- **Asymmetric Lovász local lemma.**

Let `A : ι → Set Ω` be a finite family of bad events in a finite probability space, `D i` a
finite set of "neighbours" of `i`, and `x i ∈ [0,1)` numbers with
`ℙ[A i] ≤ x i * ∏ j ∈ D i, (1 - x j)`.  If every `A i` is independent of the conjunction of
the complements of the events far from it, then `∏ i, (1 - x i) ≤ ℙ[⋂ i, (A i)ᶜ]`.

The statement is an immediate corollary of the lopsided local lemma
`lovaszLocalLemma_lopsided` proved in this directory: the independence hypothesis
`FinProbSpace.indepOfCompls` (an *equality* between `ℙ[A i ∩ ⋂_{j ∈ T} A jᶜ]` and
`ℙ[A i] * ℙ[⋂_{j ∈ T} A jᶜ]`) is strictly stronger than the lopsided hypothesis
`FinProbSpace.LopsidedIndep` (the corresponding *inequality*), so it can be fed to the
lopsided lemma via `FinProbSpace.indepOfCompls.lopsided`.  This is the same reduction by
which `lovaszLocalLemma_symmetric` is derived from the lopsided lemma. -/
theorem lovaszLocalLemma_asymmetric {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*}
    [Fintype ι] (A : ι → Set Ω) (D : ι → Finset ι) (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) (hbound : ∀ i, P.prob (A i) ≤ x i * ∏ j ∈ D i, (1 - x j))
    (hindep : ∀ i (T : Finset ι), (∀ j ∈ T, j ∉ D i ∧ j ≠ i) →
      FinProbSpace.indepOfCompls P (A i) A T) :
    ∏ i, (1 - x i) ≤ P.prob (⋂ i, (A i)ᶜ) :=
  lovaszLocalLemma_lopsided P A D x hx0 hx1 hbound
    (fun i T hT => FinProbSpace.indepOfCompls.lopsided P (hindep i T hT))

end Work.Deep.Prob.LLL
