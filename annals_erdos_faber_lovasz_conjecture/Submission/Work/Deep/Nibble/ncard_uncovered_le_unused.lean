import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs

/-!
# Uncovered edges through `w` versus unused objects through `w`

The edges of `𝓜` through `w` that are covered by none of the object matchings
`N i` inject into the edge objects through `w` that lie in none of the `N i`
(the image of the unused objects under `toSet` *contains* the uncovered-edge
set, and `toSet` is injective on non-singletons; here it suffices that each
uncovered edge has at least one unused object above it).
-/

set_option autoImplicit false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

theorem ncard_uncovered_le_unused {n : ℕ} {ι : Type*} [Fintype ι]
    {𝓜 : MultiHypergraph n}
    (hlin : MultiHypergraph.IsLinear 𝓜)
    (N : ι → Set (EdgeObj 𝓜)) (w : Fin n) :
    ({e ∈ MultiHypergraph.edgeSet 𝓜 | w ∈ e} \
        (⋃ i, objFam (N i))).ncard ≤
      ({x ∈ objThrough 𝓜 w | ∀ i, x ∉ N i} :
        Set (EdgeObj 𝓜)).ncard := by
  classical
  haveI : Finite (EdgeObj 𝓜) := finite_edgeObj 𝓜
  set L : Set (Set (Fin n)) := {e ∈ MultiHypergraph.edgeSet 𝓜 | w ∈ e} \
    (⋃ i, objFam (N i)) with hL
  set U : Set (EdgeObj 𝓜) := {x ∈ objThrough 𝓜 w | ∀ i, x ∉ N i} with hU
  have key : ∀ e ∈ L, ∃ x : EdgeObj 𝓜, EdgeObj.toSet x = e ∧ x ∈ U := by
    intro e he
    obtain ⟨⟨heE, hwe⟩, heU⟩ := he
    rcases heE with he | ⟨v, rfl, hv⟩
    · refine ⟨propObj 𝓜 e he, propObj_toSet 𝓜 e he, ?_, ?_⟩
      · exact hwe
      · intro i hx
        exact heU (Set.mem_iUnion.mpr ⟨i, ⟨propObj 𝓜 e he, hx, propObj_toSet 𝓜 e he⟩⟩)
    · refine ⟨copyObj 𝓜 v ⟨0, hv⟩, copyObj_toSet 𝓜 v ⟨0, hv⟩, ?_, ?_⟩
      · simpa [objThrough] using hwe
      · intro i hx
        exact heU (Set.mem_iUnion.mpr
          ⟨i, ⟨copyObj 𝓜 v ⟨0, hv⟩, hx, copyObj_toSet 𝓜 v ⟨0, hv⟩⟩⟩)
  have hsub : L ⊆ EdgeObj.toSet '' U := by
    rintro e he
    obtain ⟨x, hx1, hx2⟩ := key e he
    exact ⟨x, hx2, hx1⟩
  calc L.ncard ≤ (EdgeObj.toSet '' U).ncard := Set.ncard_le_ncard hsub
    _ ≤ U.ncard := Set.ncard_image_le

end Work.Deep.Nibble
