import Mathlib

namespace Work.BG

/-- Group-theoretic input for `Work.BG.nOrbCosets` (oddness part): if `S` is a Sylow
`2`-subgroup of a finite group `G` and `S` is commutative, then `|N_G(S) : C_G(S)|` is odd.

Route: `S ≤ C_G(S)` because `S` is commutative, so with `C = C_G(S) ≤ N = N_G(S)` we have
`|N : C| ∣ |N : S|` (`Subgroup.relIndex_mul_index` for `C ≤ S`, using
`Subgroup.index_dvd_of_le` after passing to `subgroupOf N`), and `|N : S| ∣ |G : S| = S.index`
(`Subgroup.relIndex_mul_index` for `S ≤ N`); finally `S.index` is odd (`Sylow.not_dvd_index`,
`Nat.not_even_iff_odd`). -/
theorem nOrbIndexOdd {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (hcomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x) :
    Odd ((Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((S : Subgroup G) : Set G))) := by
  let C : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G)
  let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  -- `S` is abelian, hence `S ≤ C_G(S) = C`.
  have hSC : (S : Subgroup G) ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  -- `|N : C| ∣ |N : S|` since `S ≤ C ≤ N`.
  have hdiv1 : C.relIndex N ∣ (S : Subgroup G).relIndex N := by
    rw [← Subgroup.relIndex_mul_relIndex (S : Subgroup G) C N hSC hCN]
    exact dvd_mul_left _ _
  -- `|N : S| ∣ |G : S| = S.index` since `S ≤ N`.
  have hdiv2 : (S : Subgroup G).relIndex N ∣ (S : Subgroup G).index := by
    rw [← Subgroup.relIndex_mul_index hSN]
    exact dvd_mul_right _ _
  -- `S.index` is odd because `S` is a Sylow `2`-subgroup.
  have hodd : Odd (S : Subgroup G).index := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    rw [even_iff_two_dvd] at hev
    exact S.not_dvd_index hev
  exact Odd.of_dvd_nat hodd (hdiv1.trans hdiv2)

end Work.BG
