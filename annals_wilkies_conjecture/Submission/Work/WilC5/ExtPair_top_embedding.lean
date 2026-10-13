import Mathlib
import Submission.Work.WilC5.ExtChain

namespace Work.WilC5

open FirstOrder Language

/-- A partial extension whose domain is all of `M` gives an embedding of `M`.

If the domain `p.dom` of a partial extension `p : ExtPair T A₀ σ₀` contains every element of
`M`, the identity-on-elements equivalence `p.dom ≃[L] M` composed with `p.emb` yields an
embedding `M ↪[L] N` extending `σ₀`.  This is the step turning the maximal element of the
Zorn poset into a global extension. -/
theorem ExtPair_top_embedding {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N] {A₀ : L.Substructure M}
    {σ₀ : L.Embedding A₀ N} (p : Work.WilC5.ExtPair T A₀ σ₀) (htop : ∀ x : M, x ∈ p.dom) :
    ∃ g : L.Embedding M N, ∀ a : A₀, g a = σ₀ a := by
  -- The equivalence between `p.dom` and `M` given by the identity on elements.
  let e : p.dom ≃[L] M :=
  { toFun := fun x => (x : M)
    invFun := fun m => ⟨m, htop m⟩
    left_inv := fun x => Subtype.ext rfl
    right_inv := fun _ => rfl
    map_fun' := fun {n} f x => rfl
    map_rel' := fun {n} r x => Iff.rfl }
  refine ⟨p.emb.comp e.symm.toEmbedding, ?_⟩
  intro a
  have h1 : e.symm a = (⟨(a : M), p.le_dom a.2⟩ : p.dom) := Subtype.ext rfl
  simp only [Embedding.comp_apply]
  rw [show e.symm.toEmbedding a = e.symm a from rfl, h1, p.agrees a]

end Work.WilC5
