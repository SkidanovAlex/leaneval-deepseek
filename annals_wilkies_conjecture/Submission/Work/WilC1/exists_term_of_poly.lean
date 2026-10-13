import Mathlib
import Submission.Work.WilC1.Defs

namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG

/-- Every polynomial in the coordinates and their `rexp`s is the value of an `LRc`-term. -/
theorem exists_term_of_poly {τ : Type*} (P : MvPolynomial (τ ⊕ τ) ℝ) :
    ∃ t : WilkiesDesign.CG.LRc.Term τ,
      ∀ v : τ → ℝ, FirstOrder.Language.Term.realize v t = rexpEval v P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨tConst a, fun v => by simp⟩
  | add p q hp hq =>
      obtain ⟨tp, htp⟩ := hp
      obtain ⟨tq, htq⟩ := hq
      exact ⟨tAdd tp tq, fun v => by simp [htp v, htq v]⟩
  | mul_X p n hp =>
      obtain ⟨tp, htp⟩ := hp
      rcases n with j | j
      · exact ⟨tMul tp (tVar j), fun v => by simp [htp v]⟩
      · exact ⟨tMul tp (tRexp (tVar j)), fun v => by simp [htp v]⟩

end Work.WilC1
