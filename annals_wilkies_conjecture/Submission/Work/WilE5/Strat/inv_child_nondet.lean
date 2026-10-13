/-
  WilE5 / Strat — the non-deterministic part of the child invariant.

  Given `Inv X σ` (the four bookkeeping invariants plus the pivot-minor hypothesis), the child
  `childSt X.c M NΦ σ t s` inherits the four *bookkeeping* invariants: the witnessing disjunct,
  `Φ = Ξ`, and the cube bookkeeping of the face pattern.  All of these are pure list bookkeeping:
  a child appends its new conditions (`childB`, `childΞ`, `childν`) and its flatness family
  (`σ.Φ ++ childΞ`) to the parent's, so every membership of the parent persists, and the child's
  `Φ` and `Ξ` are related by `Φ = σ.Φ ++ Ξ`.
-/
import Mathlib
import Submission.Work.WilE5.Strat.InvariantDef
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Strat.child_subset_parent

namespace Work.WilE5.Strat

theorem inv_child_nondet {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) (t : Work.WilE5.Test q) (s : Bool)
    (ht : t ∈ Work.WilE5.testL q M NΦ) (hσ : Work.WilE5.Strat.Inv X σ) :
    (∃ A ∈ X.basics,
        (∀ f ∈ A.eqs, f ∈ (Work.WilE5.stCond (Work.WilE5.childSt X.c M NΦ σ t s)).eqs) ∧
        (∀ g ∈ A.pos, g ∈ (Work.WilE5.stCond (Work.WilE5.childSt X.c M NΦ σ t s)).pos) ∧
        (∀ f ∈ A.eqs, f ∈ (Work.WilE5.childSt X.c M NΦ σ t s).Φ)) ∧
      (∀ ψ ∈ (Work.WilE5.childSt X.c M NΦ σ t s).Φ,
        ψ ∈ (Work.WilE5.childSt X.c M NΦ σ t s).Ξ) ∧
      (∀ ψ ∈ (Work.WilE5.childSt X.c M NΦ σ t s).Ξ,
        ψ ∈ (Work.WilE5.childSt X.c M NΦ σ t s).Φ) ∧
      (∀ l : Fin q,
          Work.WilE5.intPoly (p := p) (r := X.r) l ∈ (Work.WilE5.childSt X.c M NΦ σ t s).ν ∨
            ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
              Work.WilE5.facePoly (p := p) (r := X.r) l c ∈
                (Work.WilE5.childSt X.c M NΦ σ t s).B.map Prod.fst) := by
  have _ : t ∈ Work.WilE5.testL q M NΦ := ht
  obtain ⟨A, hA, hAe, hAp, hAΦ⟩ := hσ.1
  obtain ⟨hΦΞ, _, hcube, _⟩ := hσ.2
  refine ⟨⟨A, hA, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the disjunct's equations remain among the child's conditions
    intro f hf
    exact stCond_eqs_subset_child X M NΦ σ t s f (hAe f hf)
  · -- the disjunct's strict positivity conditions remain among the child's conditions
    intro g hg
    exact stCond_pos_subset_child X M NΦ σ t s g (hAp g hg)
  · -- the disjunct's equations remain among the child's flatness sources
    intro f hf
    simp only [Work.WilE5.childSt]
    exact List.mem_append_left _ (hAΦ f hf)
  · -- `Φ ⊆ Ξ` for the child: `child.Φ = σ.Φ ++ child.Ξ`
    intro ψ hψ
    simp only [Work.WilE5.childSt, List.mem_append] at hψ ⊢
    rcases hψ with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (hΦΞ ψ h))
    · exact h
  · -- `Ξ ⊆ Φ` for the child
    intro ψ hψ
    simp only [Work.WilE5.childSt, List.mem_append] at hψ ⊢
    exact Or.inr hψ
  · -- the cube bookkeeping, inherited from the parent
    intro l
    rcases hcube l with h | h
    · left
      simp only [Work.WilE5.childSt, Work.WilE5.childν, List.mem_append]
      exact Or.inl h
    · right
      obtain ⟨c, hc, hface⟩ := h
      refine ⟨c, hc, ?_⟩
      show Work.WilE5.facePoly (p := p) (r := X.r) l c ∈
        (Work.WilE5.childB X.c σ t).map Prod.fst
      rw [Work.WilE5.childB, List.map_append]
      exact List.mem_append_left _ hface

end Work.WilE5.Strat
