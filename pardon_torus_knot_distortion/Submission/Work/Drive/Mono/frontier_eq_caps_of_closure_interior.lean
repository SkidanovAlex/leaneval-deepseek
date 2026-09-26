import Mathlib

namespace Work.Drive.Mono

/-- The frontier of a set, expressed through its closure and interior in terms of
"big" sets `B`, `P` and the cut-off sets `S, S', T, T'`, can be written as the
disjoint-style union of the part of `B \ P` lying outside `B ∩ S ∩ T` and the
part of `B ∩ S ∩ T` where one of the cuts `S \ S'`, `T \ T'` is active.

This is a purely point-set identity: writing `frontier R = closure R \ interior R`
reduces it to propositional logic, using `S' ⊆ S` and `T' ⊆ T` to rule out the
inconsistent case `S' ∩ T' ≠ ∅` while `S ∩ T = ∅`. -/
theorem frontier_eq_caps_of_closure_interior {α : Type*} [TopologicalSpace α]
    {R P B D U S S' T T' E L : Set α}
    (hcl : closure R = B \ (S' ∩ T')) (hint : interior R = P \ (S ∩ T))
    (hD : D = B \ P) (hU : U = B ∩ S ∩ T)
    (hSS' : S' ⊆ S) (hTT' : T' ⊆ T)
    (hE : E = S \ S') (hL : L = T \ T') :
    frontier R = (D \ U) ∪ (U ∩ (E ∪ L)) := by
  rw [frontier, hcl, hint, hD, hU, hE, hL]
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union]
  have hs : x ∈ S' → x ∈ S := fun h => hSS' h
  have ht : x ∈ T' → x ∈ T := fun h => hTT' h
  tauto

end Work.Drive.Mono
