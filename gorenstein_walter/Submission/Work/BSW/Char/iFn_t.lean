import Mathlib
import Submission.Work.BSW.Vocab
import Submission.Work.BSW.Char.inv_inverting_t_mem_coset
import Submission.Work.BSW.Char.coset_sK_involutions
import Submission.Work.BSW.Char.ncard_coset_sK

namespace Work.BSW.Char

open Subgroup Work.GW2

/-- `i(t) = |K| + 1`: the involutions inverting the involution `t` are exactly the elements of the
coset `sK` (which has `|K|` elements, all involutions inverting `t`) together with `t` itself. -/
theorem iFn_t {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) : Work.BSW.iFn G t = Nat.card ↥K + 1 := by
  -- the set counted by `iFn G t` is `{t} ∪ K s`
  have hA : {u : G | orderOf u = 2 ∧ u⁻¹ * t * u = t⁻¹}
      = {t} ∪ {x : G | ∃ k ∈ K, x = k * s} := by
    ext u
    constructor
    · rintro ⟨hu2, hu⟩
      rcases inv_inverting_t_mem_coset h hu2 hu with heq | ⟨k, hk, hks⟩
      · rw [heq]
        exact Or.inl (Set.mem_singleton t)
      · exact Or.inr ⟨k, hk, hks⟩
    · rintro (heq | hmem)
      · rw [heq]
        exact ⟨(coset_sK_involutions h).2.1, (coset_sK_involutions h).2.2⟩
      · obtain ⟨k, hk, hks⟩ := hmem
        rw [hks]
        exact (coset_sK_involutions h).1 k hk
  rw [Work.BSW.iFn, hA]
  obtain ⟨hcard, htnot⟩ := ncard_coset_sK h
  -- `{t}` and the coset `Ks` are disjoint, so the cardinalities add up
  have hdisj : Disjoint ({t} : Set G) {x : G | ∃ k ∈ K, x = k * s} := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_singleton_iff] at hx1
    rw [hx1] at hx2
    exact htnot hx2
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton, hcard]
  omega

end Work.BSW.Char
