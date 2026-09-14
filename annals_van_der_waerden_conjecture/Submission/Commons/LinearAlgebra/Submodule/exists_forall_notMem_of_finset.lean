import Mathlib.Algebra.Module.Submodule.Union

/-!
# A finite union of proper subspaces is proper

Over an **infinite** field `k`, a `k`-vector space is never the union of finitely many proper
submodules: given a finite family `S i` of proper submodules there is a vector `v` lying outside
all of them.  This is the "generic element" lemma used to produce a vector avoiding finitely many
hyperplanes.

The proof reduces the indexed statement to Mathlib's
`Submodule.exists_forall_notMem_of_forall_ne_top` by re-indexing over the subtype of indices
belonging to the given `Finset`.
-/

namespace Commons.LinearAlgebra.Submodule

/-- **A finite union of proper subspaces is proper**: if `S i ≠ ⊤` for all `i ∈ s`, then there is
`v : V` with `v ∉ S i` for all `i ∈ s`.  (The field is required to be infinite.) -/
theorem exists_forall_notMem_of_finset {k V ι : Type*} [Field k] [Infinite k] [AddCommGroup V]
    [Module k V] (s : Finset ι) (S : ι → Submodule k V) (h : ∀ i ∈ s, S i ≠ ⊤) :
    ∃ v : V, ∀ i ∈ s, v ∉ S i := by
  classical
  -- Re-index along the subtype of indices occurring in `s`, so that the hypothesis is available
  -- for every index.
  haveI : Finite {i // i ∈ s} := (s.finite_toSet).to_subtype
  let f : {i // i ∈ s} → Submodule k V := fun i => S i.1
  have hf : ∀ i, f i ≠ ⊤ := fun i => h i.1 i.2
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top f hf
  exact ⟨v, fun i hi => hv ⟨i, hi⟩⟩

end Commons.LinearAlgebra.Submodule