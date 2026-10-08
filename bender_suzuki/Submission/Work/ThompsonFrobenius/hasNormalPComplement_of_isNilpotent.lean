import Mathlib
import Submission.Work.NPC.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThompsonFrobenius

/-- **A finite nilpotent group is `p`-nilpotent**: it has a normal `p`-complement for every prime
`p`.

Proof.  A finite nilpotent group has normal subgroups of every order dividing `|G|`
(`Group.IsNilpotent.exists_normal_card_eq_of_dvd_card`).  Take `N ⊴ G` of order the `p`-free part
`|G| / p ^ (factorization of |G| at p)` of `|G|` (`Nat.ordCompl`).  Then `|N|` is coprime to `p`
by construction (`Nat.coprime_ordCompl`), and since `|N| * N.index = |G|` and
`p ^ (|G|.factorization p) * (|G| / p ^ (|G|.factorization p)) = |G|`, cancelling the common
factor `|N| = |G| / p ^ (|G|.factorization p)` gives `N.index = p ^ (|G|.factorization p)`.
Hence the quotient `G ⧸ N`, of order `N.index = |G| / |N|`, is a `p`-group
(`IsPGroup.of_card`).  So `N` is a normal `p`-complement of `G`. -/
theorem hasNormalPComplement_of_isNilpotent {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G] {p : ℕ} (hp : p.Prime) : Work.NPC.HasNormalPComplement p G := by
  -- `N` is a normal subgroup of `G` whose order is the `p`-free part of `|G|`.
  obtain ⟨N, hNcard, hNnorm⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card
      (n := Nat.card G / p ^ (Nat.card G).factorization p) (Nat.ordCompl_dvd (Nat.card G) p)
  have hm0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hn0 : 0 < Nat.card G / p ^ (Nat.card G).factorization p := by
    have := Nat.card_pos (α := N); rw [hNcard] at this; exact this
  -- `|N|` is coprime to `p`.
  have hcop : (Nat.card N).Coprime p := by
    rw [hNcard]
    exact (Nat.coprime_ordCompl hp hm0).symm
  -- The index of `N` is the full `p`-part of `|G|`.
  have hindex : N.index = p ^ (Nat.card G).factorization p := by
    have hcard : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
    have h1 : (Nat.card G / p ^ (Nat.card G).factorization p) * N.index = Nat.card G := by
      rw [← hNcard]; exact hcard
    have h2 : (Nat.card G / p ^ (Nat.card G).factorization p) * p ^ (Nat.card G).factorization p
        = Nat.card G := by
      rw [Nat.mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p
    exact Nat.eq_of_mul_eq_mul_left hn0 (h1.trans h2.symm)
  have hpg : IsPGroup p (G ⧸ N) := by
    refine IsPGroup.of_card (n := (Nat.card G).factorization p) ?_
    rw [← Subgroup.index_eq_card]
    exact hindex
  exact ⟨N, hNnorm, hcop, hpg⟩

end Work.ThompsonFrobenius
