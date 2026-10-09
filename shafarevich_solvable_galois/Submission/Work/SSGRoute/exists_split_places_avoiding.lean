import Mathlib
import Submission.Work.SSGRoute.exists_split_place_avoiding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `d` splitting places avoiding a prescribed finite set of places

This refines `Work.SSGRoute.exists_split_place_avoiding` (Chebotarev's density theorem together
with the standard correspondence between primes of `k` and `G_k`-orbits of places of `Ω`): not
only is there *one* finite place of `Ω` which splits completely in the finite Galois extension
`Λ/k` and avoids a prescribed finite set `S` of finite places, but there are `d` *pairwise
non-conjugate* such places, for every prescribed `d : ℕ`.

The proof is an induction on `d`.  Given `d` pairwise non-conjugate finite places `T` splitting in
`Λ` and avoiding `S`, apply the single-place statement to the finite set `S ∪ T`; the place `P` it
produces splits in `Λ`, avoids `S` and is not conjugate to any element of `T`.  Moreover `P` is
conjugate to itself, so it cannot lie in `T`: inserting it gives `d + 1` pairwise non-conjugate
places avoiding `S`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.style.haveILetI false

theorem exists_split_places_avoiding (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (S : Finset (ValuationSubring Ω)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (d : ℕ) :
    ∃ T : Finset (ValuationSubring Ω), T.card = d ∧
      (∀ A ∈ T, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ T, SSGRoute.IsSplitIn k Λ A) ∧
      (∀ A ∈ T, ∀ B ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      (∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace k A B → A = B) := by
  classical
  induction d with
  | zero =>
      exact ⟨∅, by simp, by simp, by simp, by simp, by simp⟩
  | succ d ih =>
      obtain ⟨T, hcard, hfin, hsplit, havoid, hdisj⟩ := ih
      -- the finite set of places the new place has to avoid
      have hS' : ∀ A ∈ S ∪ T, SSGRoute.IsFinPlace k A := by
        intro A hA
        rcases Finset.mem_union.mp hA with hA | hA
        · exact hS A hA
        · exact hfin A hA
      obtain ⟨P, hPfin, hPsplit, hPavoid⟩ :=
        exists_split_place_avoiding k Ω Λ (S ∪ T) hS'
      -- `P` is conjugate to itself, so it does not already lie in `T`
      have hPnotT : P ∉ T := by
        intro hPT
        exact hPavoid P (Finset.mem_union_right S hPT) (isConjPlace_refl P)
      refine ⟨insert P T, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hPnotT, hcard]
      · intro A hA
        rcases Finset.mem_insert.mp hA with hAP | hA
        · rw [hAP]; exact hPfin
        · exact hfin A hA
      · intro A hA
        rcases Finset.mem_insert.mp hA with hAP | hA
        · rw [hAP]; exact hPsplit
        · exact hsplit A hA
      · intro A hA B hB
        rcases Finset.mem_insert.mp hA with hAP | hA
        · intro h
          exact hPavoid B (Finset.mem_union_left T hB) (isConjPlace_symm (hAP ▸ h))
        · exact havoid A hA B hB
      · intro A hA B hB hconj
        rcases Finset.mem_insert.mp hA with hAP | hA
        · rcases Finset.mem_insert.mp hB with hBP | hB
          · rw [hAP, hBP]
          · exact absurd (hAP ▸ isConjPlace_symm hconj)
              (hPavoid B (Finset.mem_union_right S hB))
        · rcases Finset.mem_insert.mp hB with hBP | hB
          · exact absurd (hBP ▸ hconj) (hPavoid A (Finset.mem_union_right S hA))
          · exact hdisj A hA B hB hconj

end Work.SSGRoute
