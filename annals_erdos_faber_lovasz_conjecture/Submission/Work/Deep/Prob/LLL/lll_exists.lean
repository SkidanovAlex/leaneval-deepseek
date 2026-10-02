/-
# Existence form of the symmetric Lovász local lemma

`Work.Deep.Prob.LLL.lll_exists` : under the hypotheses of the symmetric local lemma
(each bad event has probability at most `p`, each event is independent of the family of
events indexed outside `D i ∪ {i}` with `|D i| ≤ d`, and `e · p · (d+1) ≤ 1`), some sample
point avoids every bad event.

This is the existence statement obtained from the positive-probability conclusion of
`Work.Deep.Prob.LLL.lovaszLocalLemma_symmetric` by `FinProbSpace.exists_of_prob_pos`.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces
import Submission.Work.Deep.Prob.LLL.lovaszLocalLemma_symmetric

namespace Work.Deep.Prob.LLL

theorem lll_exists {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (D : ι → Finset ι) {p : ℝ} (hp : ∀ i, P.prob (A i) ≤ p) {d : ℕ}
    (hd : ∀ i, (D i).card ≤ d)
    (hindep : ∀ i (T : Finset ι), (∀ j ∈ T, j ∉ D i ∧ j ≠ i) →
      FinProbSpace.indepOfCompls P (A i) A T)
    (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ ω, ∀ i, ω ∉ A i := by
  obtain ⟨ω, hω⟩ := P.exists_of_prob_pos (lovaszLocalLemma_symmetric P A D hp hd hindep hpd)
  exact ⟨ω, fun i => Set.mem_iInter.mp hω i⟩

end Work.Deep.Prob.LLL
