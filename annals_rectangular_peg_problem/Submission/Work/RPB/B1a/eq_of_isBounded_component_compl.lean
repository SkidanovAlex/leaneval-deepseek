import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths
import Submission.Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs
import Submission.Work.RPB1a.Caratheodory.Brouwer.eq_of_isBounded_component_compl_aux
import Submission.Work.RPB.B1a.maehara_normalize
import Submission.Work.RPB.B1a.maehara_broken_line

namespace Work.RPB.B1a

open Work.RPB1a.Caratheodory.Brouwer

/-- **Uniqueness of the bounded connected component of the complement of a Jordan curve.**

If the complement of the plane curve `γ` has a bounded connected component, then it has only one:
any two points whose complementary component is bounded lie in the same component.

The proof (Maehara's second half) normalises the curve by a similarity
(`maehara_normalize`) so that the two diametral points become `(-1,0)` and `(1,0)`, the curve lies
in `rect = [-1,1] × [-2,2]` and meets `rectB = {x = ±1} ∪ {y = ±2}` only in those two points.
`maehara_broken_line` then produces the broken line `β` from `c = (0,2)` to `d = (0,-2)` together
with the point `x` on it, such that every off-curve point of `β` lies either in the component of `x`
or in an unbounded component.  `eq_of_isBounded_component_compl_aux` runs Maehara's crossing
argument with this broken line, and `eq_of_isBounded_component_compl_of_image` transports the
conclusion back along the normalising homeomorphism. -/
theorem eq_of_isBounded_component_compl (γ : Circle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ)
    (h₀ : ∃ x : ℝ × ℝ, x ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x)) :
    ∀ y z : ℝ × ℝ, y ∉ Set.range γ → z ∉ Set.range γ →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) y) →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) →
      connectedComponentIn ((Set.range γ)ᶜ) y = connectedComponentIn ((Set.range γ)ᶜ) z := by
  obtain ⟨e, hbe, _, hsub, ha, hb, hbdry⟩ := maehara_normalize γ hγ hinj
  refine eq_of_isBounded_component_compl_of_image e hbe γ hγ hinj ?_ h₀
  intro h₀'
  have hcont : Continuous fun c : Circle => e (γ c) := e.continuous.comp hγ
  have hinj' : Function.Injective fun c : Circle => e (γ c) := e.injective.comp hinj
  obtain ⟨β, x, hβc, hβ0, hβ1, hβrect, hβa, hβb, hx, hβcomp⟩ :=
    maehara_broken_line (fun c : Circle => e (γ c)) hcont hinj' ha hb hsub hbdry
  exact eq_of_isBounded_component_compl_aux (fun c : Circle => e (γ c)) hcont hinj' hsub ha hb
    h₀' hβc hβrect hβ0 hβ1 hβa hβb hx hβcomp

end Work.RPB.B1a
