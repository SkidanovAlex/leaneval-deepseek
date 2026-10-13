import Mathlib

namespace Work.DSG3

/-- In a Noetherian `T₀` space, every nonempty subset `S` contains a point `z` which is minimal
for the specialisation order restricted to `S`, i.e. `closure {z} ∩ S = {z}`.

The argument: the subspace `S` is Noetherian (hence compact) and `T₀`, so by
`IsClosed.exists_closed_singleton` the whole (closed) subspace `S` contains a point `y` whose
singleton is closed in the subspace. Concretely there is a closed set `F ⊆ α` with
`{y} = Subtype.val ⁻¹' F`, which unwinds to `closure {y} ∩ S = {y}`. -/
theorem exists_mem_closure_eq_singleton {α : Type*} [TopologicalSpace α] [T0Space α]
    [TopologicalSpace.NoetherianSpace α] (S : Set α) (hS : S.Nonempty) :
    ∃ z ∈ S, closure ({z} : Set α) ∩ S = {z} := by
  obtain ⟨x0, hx0⟩ := hS
  -- In the subspace `S`, the whole space is a nonempty closed set.
  obtain ⟨y, -, hy⟩ := IsClosed.exists_closed_singleton (X := S) isClosed_univ
    ⟨⟨x0, hx0⟩, Set.mem_univ _⟩
  -- `{y}` is closed in the subspace, so it is the preimage of a closed set `F` of `α`.
  obtain ⟨F, hFcl, hF⟩ := isClosed_induced_iff.mp hy
  refine ⟨y, y.2, ?_⟩
  have hyF : (y : α) ∈ F := by
    have : y ∈ Subtype.val ⁻¹' F := by rw [hF]; exact Set.mem_singleton y
    exact this
  have hsub : closure ({↑y} : Set α) ⊆ F :=
    closure_minimal (Set.singleton_subset_iff.mpr hyF) hFcl
  ext a
  constructor
  · intro ha
    rw [Set.mem_singleton_iff]
    have haS : a ∈ S := ha.2
    have haF : a ∈ F := hsub ha.1
    have hmem : (⟨a, haS⟩ : S) ∈ Subtype.val ⁻¹' F := haF
    rw [hF] at hmem
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  · intro ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨subset_closure rfl, y.2⟩

end Work.DSG3
