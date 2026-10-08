/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area FUS, `Work.FUS`)

# `C_G(t)` has a normal 2-complement (`Work.FUS.centralizer_has_normal_two_complement`)

For `t` the central involution of a dihedral Sylow 2-subgroup `S` of `G`, the centralizer
`C_G(t)` has a normal 2-complement.  The proof applies the Frobenius normal `p`-complement
theorem (Isaacs §5E, `OddOrder.Isaacs.Ch05.hasNormalPComplement_of_prime_subgroups_centralize`)
to `T = C_G(t)`: the `N/C`-condition
`N_T(X)/C_T(X)` is a 2-group for every 2-subgroup `X ≤ T` is supplied by
`Work.FUS.DihedralSylow.odd_normalizer_centralizes_of_center`
(Bender's Lemma 1.1 input, the `N/C`-theorem in the dihedral case).

Said `N/C`-input: if `T` has a dihedral Sylow 2-subgroup and a central involution `t`, and
`y ∈ N_T(X)` has odd order, then `y ∈ C_T(X)`.  Its content is that a 2-subgroup of a group
with dihedral Sylow `2`-subgroup is cyclic or dihedral (subgroups of dihedral groups are),
`Aut` of a cyclic or of a `D_{2^j}` (`j ≥ 2`) 2-group is a 2-group, and the only exceptional
case — the Klein four-group `V₄` — is killed by the central involution `t ∈ Z(T)`, which lies
in every four-subgroup because `T` has 2-rank `2`.
-/
import Mathlib
import Submission.Work.FUS.Dihedral
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.FUS.AutFacts.mulAut_cyclic_eq_one_of_odd
import Submission.Work.FUS.AutFacts.mulAut_dihedral_eq_one_of_odd
import Submission.Work.FUS.AutFacts.mulAut_fourGroup_eq_one_of_odd
import Submission.Work.FUS.DihedralSylow.odd_normalizer_centralizes_of_center
import Submission.OddOrder.Isaacs.Ch05_Transfer.Main

namespace Work.FUS

open Subgroup

/-- **`Work.FUS.centralizer_has_normal_two_complement`**: if `t` is the central involution of a
dihedral Sylow `2`-subgroup `S` of `G`, then `C_G(t)` has a normal `2`-complement, i.e. a normal
subgroup `N` complementary to every Sylow `2`-subgroup of `C_G(t)`. -/
theorem centralizer_has_normal_two_complement {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hn : 2 ≤ n) (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (t : G) (htS : t ∈ (S : Subgroup G)) (ht2 : orderOf t = 2)
    (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) :
    ∃ N : Subgroup ↥(Subgroup.centralizer ({t} : Set G)), N.Normal ∧
      ∀ P : Sylow 2 ↥(Subgroup.centralizer ({t} : Set G)),
        N.IsComplement' (P : Subgroup ↥(Subgroup.centralizer ({t} : Set G))) := by
  -- `S` is contained in `C_G(t)`, because `t` is central in `S`.
  have hSH : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (htc x hx).symm
  let T : Subgroup G := Subgroup.centralizer ({t} : Set G)
  -- The Sylow `2`-subgroup `ST` of `T = C_G(t)` obtained from `S`.
  let ST : Sylow 2 T := Sylow.subtype S hSH
  have hSTcoe : (ST : Subgroup T) = (S : Subgroup G).subgroupOf T := Sylow.coe_subtype S hSH
  have hisoT : Nonempty (↥(ST : Subgroup T) ≃* DihedralGroup n) := by
    rw [hSTcoe]
    obtain ⟨e⟩ := hiso
    exact ⟨(Subgroup.subgroupOfEquivOfLe hSH).trans e⟩
  -- The central involution `t`, as an element of `T`.
  have htC : t ∈ T := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  let tT : T := ⟨t, htC⟩
  have ht2T : orderOf tT = 2 := by
    change orderOf (⟨t, htC⟩ : T) = 2
    rw [Subgroup.orderOf_mk, ht2]
  have htcT : tT ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    show (u : G) * t = t * (u : G)
    exact (u.2 t (Set.mem_singleton t)).symm
  -- Frobenius' normal `p`-complement theorem for `p = 2`, via the `N/C`-condition.
  refine OddOrder.Isaacs.Ch05.hasNormalPComplement_of_prime_subgroups_centralize (p := 2) ?_
  intro q hq hqne X Q hX hQ hQN y hy
  have hqodd : Odd q := hq.out.odd_of_ne_two hqne
  have hyN : y ∈ Subgroup.normalizer (X : Set T) := hQN hy
  -- every element of the `q`-group `Q` (`q` odd) has odd order
  have hodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := q)).mp hQ ⟨y, hy⟩
    have hk' : orderOf y = q ^ k := by rw [← Subgroup.orderOf_mk y hy]; exact hk
    rw [hk']
    exact hqodd.pow
  exact Work.FUS.DihedralSylow.odd_normalizer_centralizes_of_center ST n hn hisoT tT ht2T htcT X hX y hyN hodd

end Work.FUS
