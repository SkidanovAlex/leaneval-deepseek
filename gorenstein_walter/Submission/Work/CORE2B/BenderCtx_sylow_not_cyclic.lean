import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.OddOrder.FeitThompson
import Submission.OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# CORE2B — `BenderCtx`: Sylow 2-subgroups are not cyclic

`Work.GW2.BenderCtx G` says that `G` is a non-abelian finite simple group whose Sylow
2-subgroups are cyclic or dihedral (`Work.GW2.DihOrCycSylow`).  Here we remove the cyclic
alternative: every Sylow 2-subgroup of `G` is non-cyclic.

* A non-abelian finite simple group has even order (`even_card_of_isSimpleGroup_nonabelian`):
  a group of odd order is solvable by Feit–Thompson, and a solvable simple group is commutative.
* Hence a Sylow 2-subgroup `S` with `S = ⊥` is impossible: the order of `G` is even, so `S`
  is nontrivial (`Sylow.ne_bot_of_dvd_card`).
* If `S ≠ ⊥`, a cyclic `S` is excluded by Isaacs Cor. 5.19
  (`OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two`): a non-abelian finite group
  with a nontrivial cyclic Sylow 2-subgroup is not simple.
-/

namespace Work.CORE2B

/-- **A non-abelian finite simple group has even order.**

If `|G|` were odd then `G` would be solvable by Feit–Thompson, and for a simple group solvability
is equivalent to commutativity (`IsSimpleGroup.comm_iff_isSolvable`), contradicting
non-abelianness. -/
theorem even_card_of_isSimpleGroup_nonabelian {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Even (Nat.card G) := by
  by_contra hodd'
  have hodd : Odd (Nat.card G) := Nat.not_even_iff_odd.mp hodd'
  have hsolv : Group.IsSolvable G := OddOrder.feitThompson hodd
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((@IsSimpleGroup.comm_iff_isSolvable G _ hsimple).mpr hsolv a b)

theorem BenderCtx_sylow_not_cyclic {G : Type} [Group G] [Finite G] (h : Work.GW2.BenderCtx G)
    (S : Sylow 2 G) : ¬ IsCyclic (S : Subgroup G) := by
  intro hcyc
  have hnonab : ¬ IsMulCommutative G := fun hc => by
    obtain ⟨a, b, hab⟩ := h.nonab
    exact hab (@mul_comm' G _ hc a b)
  by_cases hbot : (S : Subgroup G) = ⊥
  · -- `|G|` is even, so a Sylow 2-subgroup cannot be trivial
    exact (Sylow.ne_bot_of_dvd_card S
      (even_iff_two_dvd.mp (even_card_of_isSimpleGroup_nonabelian h.simple h.nonab))) hbot
  · -- Isaacs Cor. 5.19 for a nontrivial cyclic Sylow 2-subgroup
    exact (OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two
      (G := G) (hPcyc := hcyc) hnonab S hbot) h.simple

end Work.CORE2B
