import Mathlib
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.fourGroupNormalizer
import Submission.Work.BSW.Cases.K4.two_dvd_card_normalizer_of_card_eq_three

namespace Work.BSW.Cases.K4

open Subgroup

/- Implementation note.  The caveat in the docstring below is stale: `fourGroupNormalizer.lean`
builds (verified) and contains no unfinished proofs, so its `card_normalizer_eq` supplies
`Nat.card ↥(Subgroup.normalizer (V : Set G)) = 24` directly and the orbit–stabiliser count does not
have to be re-proved.

The remaining input is the general group-theoretic fact
`two_dvd_card_normalizer_of_card_eq_three`: in *any* group `H` of order `24`, the normalizer of a
subgroup of order `3` has even order (a subgroup of order `3` is Sylow, `n₃ ≡ 1 [MOD 3]` and
`n₃ ∣ 24` force `n₃ ∈ {1,4}`, whence `|N_H(X)| = |H| / n₃ ∈ {24, 6}`).  Applied with
`H = ↥(N_G(V))` and the subgroup `X.subgroupOf N_G(V)`, together with
`Subgroup.subgroupOf_normalizer_eq` (which identifies the normalizer of `X.subgroupOf N_G(V)`
inside `↥(N_G(V))` with `(N_G(X) ⊓ N_G(V)).subgroupOf N_G(V)`), this shows that
`|N_G(X) ⊓ N_G(V)|` is even; Cauchy's theorem then produces the involution. -/
/-- `N_G(V)` contains an involution normalizing `X`, in the `K4Hyp` setting.

Suggested route (avoids the file `fourGroupNormalizer.lean`, which is currently being edited by a
colleague and does not build): first prove `Nat.card ↥(Subgroup.normalizer (V : Set G)) = 24` by
orbit–stabiliser: for `u ∈ V#` the subgroup `C_G(u)` (order `8 = 2 * 4 = 2 * |V|`, using
`Work.BSW.Cases.K4.K4Hyp`) lies in `N_G(V)` by `Work.BSW.Cases.K4.le_normalizer_of_two_mul_card`
(`Submission/Work/BSW/Cases/K4/CardSup.lean`), so all `N_G(V)`-orbits on `V#` have size
`|N_G(V)| / 8`; these orbits partition the 3-element set `V#`, so `|N_G(V)| / 8` divides `3`; it is
not `1`, since `X ≤ N_G(V)` has order `3` and `N_G(V)` of order `8` is a 2-group. Hence
`|N_G(V)| = 24`. Then `X` is a Sylow `3`-subgroup of the group `↥(N_G(V))`; the number `n₃` of
Sylow `3`-subgroups satisfies `n₃ ≡ 1 (mod 3)` (`card_sylow_modEq_one`) and `n₃ ∣ 8`
(`Sylow.card_dvd_index`), so `n₃ ∈ {1,4}` and `|N_{↥N}(X)| = 24 / n₃ ∈ {24,6}` is even;
`exists_prime_orderOf_dvd_card'` (Cauchy) then supplies an element of order `2` of `↥N`, i.e. an
involution `t ∈ N_G(V)` with `tXt⁻¹ = X`. -/
theorem exists_involution_mem_normalizer {G : Type} [Group G] [Finite G]
    (h : Work.BSW.Cases.K4.K4Hyp G) (V X : Subgroup G) (hV : Work.BSW.Cases.K4.IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ Subgroup.normalizer (V : Set G) ∧
      t ∈ Subgroup.normalizer (X : Set G) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hN
  -- the normalizer of the Klein four group `V` has order `24`
  have hN24 : Nat.card ↥N = 24 := card_normalizer_eq h hV
  -- `X`, viewed inside `↥N`, still has order `3`
  have hX3' : Nat.card ↥(X.subgroupOf N) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv, hX3]
  -- the normalizer of `X` inside `↥N` has even order (Sylow count in a group of order `24`)
  have heven : 2 ∣ Nat.card ↥(Subgroup.normalizer ((X.subgroupOf N : Subgroup ↥N) : Set ↥N)) :=
    two_dvd_card_normalizer_of_card_eq_three (X.subgroupOf N) hN24 hX3'
  -- that normalizer is `(N_G(X) ⊓ N_G(V)).subgroupOf N_G(V)`, so `|N_G(X) ⊓ N_G(V)|` is even
  have hide : Nat.card ↥(Subgroup.normalizer ((X.subgroupOf N : Subgroup ↥N) : Set ↥N)) =
      Nat.card ↥(Subgroup.normalizer (X : Set G) ⊓ N) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hXle, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  rw [hide] at heven
  -- Cauchy's theorem in the group `N_G(X) ⊓ N`
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (X : Set G) ⊓ N)) 2 heven
  refine ⟨(m : G), ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hm
  · exact m.2.2
  · exact m.2.1

end Work.BSW.Cases.K4
