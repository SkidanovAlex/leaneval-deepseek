import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.FinishSetup

namespace Work.Deep.Kahn

/-- **Extracting a proper list colouring from a sample point avoiding all bad events.**  Let
`φ : ListSpace L` be a choice of a colour from each list (so `(φ e).val ∈ L e` for every edge
`e`), and suppose `φ` avoids the bad event `badEvent L i` for every index
`i : BadIdx 𝓗` — where `BadIdx 𝓗` consists of the canonically ordered pairs of distinct edges
that meet, and `badEvent L i = {φ | (φ i.1.1).val = (φ i.1.2).val}` is the event that the two
edges of `i` get the same colour.  Then `φ` is a proper colouring from the lists: `𝓗` is
`ListColorable` with respect to `L`.

Sketch: the colouring is `fun e : 𝓗 => (φ e).val`, whose membership in `L e` is
`(φ e).2`.  For distinct edges `e₁ ≠ e₂` meeting in a vertex, convert the hypothesis
`(e₁ ∩ e₂ : Set (Fin n)).Nonempty` into
`(verts e₁ ∩ verts e₂).Nonempty` (`ErdosFaberLovaszConjecture.mem_verts`) and apply `hφ` to
the index `canonIdx 𝓗 e₁ e₂ _ _`, whose underlying ordered pair is `(e₁, e₂)` or `(e₂, e₁)`
(`Work.Deep.Kahn.canonIdx_val`); the two components of that index have distinct values under
`φ`, which gives `(φ e₁).val ≠ (φ e₂).val`. -/
theorem listColorable_of_avoids {n c : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    [Fintype 𝓗] (L : 𝓗 → Finset (Fin c)) (φ : Work.Deep.Kahn.ListSpace L)
    (hφ : ∀ i : Work.Deep.Kahn.BadIdx 𝓗, φ ∉ Work.Deep.Kahn.badEvent L i) :
    ErdosFaberLovaszConjecture.Hypergraph.ListColorable L := by
  refine ⟨{ labels := fun e : 𝓗 => (φ e).val, isColoring := ?_ }, fun e => (φ e).2⟩
  intro e₁ e₂ he hnon
  -- `e₁` and `e₂` share the vertex `v`, so they meet also in the sense of `BadIdx`.
  obtain ⟨v, hv⟩ := hnon
  have hint : (ErdosFaberLovaszConjecture.verts (e₁ : Set (Fin n)) ∩
      ErdosFaberLovaszConjecture.verts (e₂ : Set (Fin n))).Nonempty :=
    ⟨v, Finset.mem_inter.mpr
      ⟨(ErdosFaberLovaszConjecture.mem_verts _ v).mpr hv.1,
        (ErdosFaberLovaszConjecture.mem_verts _ v).mpr hv.2⟩⟩
  -- If the two edges received the same colour, `φ` would lie in the bad event of
  -- their canonical index; but the underlying pair of that index is `(e₁, e₂)` or
  -- `(e₂, e₁)`, in either case a pair whose components get the same colour.
  intro hcon
  refine hφ (canonIdx 𝓗 e₁ e₂ he hint) ?_
  show (φ (canonIdx 𝓗 e₁ e₂ he hint).1.1).val = (φ (canonIdx 𝓗 e₁ e₂ he hint).1.2).val
  rcases canonIdx_val 𝓗 he hint with h | h
  · rw [h]; exact hcon
  · rw [h]; exact hcon.symm

end Work.Deep.Kahn
