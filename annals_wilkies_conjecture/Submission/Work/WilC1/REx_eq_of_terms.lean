import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage
import Submission.Work.WilC1.REx_inter
import Submission.Work.WilC1.REx_proj
import Submission.Work.WilC1.REx_union

namespace Work.WilC1

/-- Membership in the graph of a term, with the last coordinate read off a `Sum.elim` tuple:
`Sum.elim x u` lies in `GraphSet t` exactly when the last coordinate `u 0` is the value of `t`
at `x`. -/
theorem mem_graphSet_iff {ι : Type*} (t : WilkiesDesign.CG.LRc.Term ι) (x : ι → ℝ)
    (u : Fin 1 → ℝ) :
    Sum.elim x u ∈ GraphSet t ↔ u 0 = FirstOrder.Language.Term.realize x t := by
  rw [GraphSet, Set.mem_ofPred_eq]
  constructor <;> intro h
  · simpa using h
  · simpa using h

/-- The set on which two terms of `LRc` agree is `REx`, given that every term has an `REx`
graph.  Both graphs sit inside `ℝ^{ι ⊕ Fin 1}`, where the last coordinate is the value; their
intersection is non-empty exactly over the points where the two term functions agree, so the
required set is the projection of an `REx` set along `Sum.inl`. -/
theorem REx_eq_of_terms {ι : Type*} (t₁ t₂ : WilkiesDesign.CG.LRc.Term ι)
    (hgraph : ∀ (t : WilkiesDesign.CG.LRc.Term ι), REx (ι ⊕ Fin 1) (GraphSet t)) :
    REx ι {x : ι → ℝ | FirstOrder.Language.Term.realize x t₁ =
      FirstOrder.Language.Term.realize x t₂} := by
  refine (REx_proj 1 (REx_inter (hgraph t₁) (hgraph t₂))).congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_graphSet_iff]
  constructor
  · rintro ⟨u, h1, h2⟩
    exact h1.symm.trans h2
  · intro h
    exact ⟨fun _ => FirstOrder.Language.Term.realize x t₁, rfl, h⟩

end Work.WilC1
