import Mathlib
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.FUS.AutFacts.mulAut_cyclic_eq_one_of_odd
import Submission.Work.FUS.AutFacts.mulAut_dihedral_eq_one_of_odd
import Submission.Work.FUS.AutFacts.mulAut_fourGroup_eq_one_of_odd
import Submission.Work.FUS.odd_normalizer_centralizes

namespace Work.FUS.DihedralSylow

/-- **Odd-order elements of the normalizer of a `2`-subgroup centralize it.**

Let `U` be a finite group whose Sylow `2`-subgroups are dihedral (`S ≃* DihedralGroup n`,
`n ≥ 2`) and which contains a *central* involution `t`.  If `X ≤ U` is a `2`-subgroup and
`y ∈ N_U(X)` has odd order, then `y ∈ C_U(X)`.

This is the `t ∈ Z(U)` form of `Work.FUS.odd_normalizer_centralizes`.  The extra hypotheses
of that lemma are automatic here:

* a central involution of order `2` lies in *every* `2`-subgroup normalized by a Sylow
  `2`-subgroup: `⟨t⟩` is centralized by `S`, so `S ⊔ ⟨t⟩` is a `2`-group, and maximality of
  the Sylow subgroup `S` forces `S ⊔ ⟨t⟩ = S`, whence `t ∈ S`;
* `t` central in `U` trivially centralizes `S`, is centralized by `X` and by `y`. -/
theorem odd_normalizer_centralizes_of_center {U : Type*} [Group U] [Finite U]
    (S : Sylow 2 U) (n : ℕ) (hn : 2 ≤ n)
    (hiso : Nonempty ((S : Subgroup U) ≃* DihedralGroup n))
    (t : U) (ht2 : orderOf t = 2) (htc : t ∈ Subgroup.center U)
    (X : Subgroup U) (hX : IsPGroup 2 X) (y : U)
    (hyN : y ∈ Subgroup.normalizer (X : Set U)) (hodd : Odd (orderOf y)) :
    y ∈ Subgroup.centralizer (X : Set U) := by
  -- `t` commutes with every element of `U`.
  have ht_comm : ∀ g : U, g * t = t * g := Subgroup.mem_center_iff.mp htc
  -- (1) `t` lies in the Sylow `2`-subgroup `S`.
  have hcent_le : (Subgroup.center U : Subgroup U) ≤ Subgroup.centralizer (S : Set U) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact Subgroup.mem_center_iff.mp hx h
  have htN : t ∈ Subgroup.normalizer (S : Set U) :=
    Subgroup.centralizer_le_normalizer (S : Set U) (hcent_le htc)
  have hzpow2 : IsPGroup 2 (Subgroup.zpowers t : Subgroup U) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
  have hsup2 : IsPGroup 2 ↥((S : Subgroup U) ⊔ Subgroup.zpowers t) :=
    IsPGroup.to_sup_of_normal_left' (H := (S : Subgroup U)) (K := Subgroup.zpowers t)
      S.isPGroup' hzpow2 (Subgroup.zpowers_le.mpr htN)
  have htS : t ∈ (S : Subgroup U) := by
    have hEq : ((S : Subgroup U) ⊔ Subgroup.zpowers t) = S :=
      S.is_maximal' hsup2 le_sup_left
    have htmem : t ∈ ((S : Subgroup U) ⊔ Subgroup.zpowers t) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rwa [hEq] at htmem
  -- (2) `t` centralizes `S`.
  have htcS : ∀ x ∈ (S : Subgroup U), x * t = t * x := fun x _ => ht_comm x
  -- (3) `X` and `y` centralize `t`.
  have hXC : X ≤ Subgroup.centralizer ({t} : Set U) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (ht_comm x).symm
  have hyC : y ∈ Subgroup.centralizer ({t} : Set U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (ht_comm y).symm
  exact Work.FUS.odd_normalizer_centralizes S n hn hiso t htS ht2 htcS X hX hXC y hyN hyC hodd

end Work.FUS.DihedralSylow
