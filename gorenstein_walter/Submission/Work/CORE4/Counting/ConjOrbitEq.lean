import Mathlib
import Submission.Work.CORE4.ConjSubgroupCount

namespace Work.CORE4.Counting

theorem ConjOrbitEq {G : Type} [Group G] [Finite G] (r N : ℕ)
    (hcountS : {X : Subgroup G | Nat.card X = r}.ncard = N)
    (Y : Subgroup G) (hY : Nat.card Y = r)
    (hindex : (Subgroup.normalizer (Y : Set G)).index = N) :
    ∀ Y' : Subgroup G, Nat.card Y' = r →
      ∃ e : G, Y' = Y.map (MulAut.conj e).toMonoidHom := by
  intro Y' hY'
  -- The set `S` of subgroups of order `r` and the conjugation orbit `O` of `Y` both have
  -- cardinality `N` (`O` by orbit–stabiliser, `S` by hypothesis), and `O ⊆ S` since
  -- conjugation preserves the order.  Hence `O = S` and every order-`r` subgroup is
  -- conjugate to `Y`.
  have hOcard : {X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g Y}.ncard = N := by
    rw [Work.CORE4.ConjSubgroupCount G Y, hindex]
  have hOS : {X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g Y} ⊆
      {X : Subgroup G | Nat.card X = r} := by
    rintro X ⟨g, rfl⟩
    show Nat.card ↥(Work.GW2.conjSub g Y) = r
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hY]
  have hEq := Set.eq_of_subset_of_ncard_le hOS (by rw [hOcard, hcountS])
  have hmem : Y' ∈ {X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g Y} := by
    rw [hEq]; exact hY'
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg⟩

end Work.CORE4.Counting
