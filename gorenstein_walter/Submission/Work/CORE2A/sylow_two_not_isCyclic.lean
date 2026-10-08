import Mathlib
import Submission.OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# CORE2A: a simple non-abelian group has no cyclic Sylow 2-subgroup

If `G` is finite and simple and non-abelian, then no Sylow 2-subgroup of `G` is cyclic
(Isaacs, *Finite Group Theory*, Corollary 5.19).  This is the "cyclic" half of Bender's
D-group dichotomy: a minimal counterexample to Gorenstein–Walter has Sylow 2-subgroups that
are dihedral, not cyclic.

The proof is a direct application of `OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two`,
which formalises Isaacs Cor. 5.19: a finite non-abelian group with a nontrivial cyclic Sylow
2-subgroup is not simple.  The hypothesis `2 ≤ Nat.card S` rules out the trivial Sylow
2-subgroup (i.e. `|G|` odd), so no appeal to Feit–Thompson is needed here.
-/

namespace Work.CORE2A

theorem sylow_two_not_isCyclic {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (hS : 2 ≤ Nat.card S) :
    ¬ IsCyclic (S : Subgroup G) := by
  intro hcyc
  haveI : IsSimpleGroup G := hsimple
  -- `2 ≤ |S|` forces `S ≠ ⊥`, i.e. the Sylow 2-subgroup is nontrivial.
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro h
    have hcard : Nat.card S = 1 := by
      rw [h]
      exact Subgroup.card_bot
    omega
  -- Non-abelian as `¬ IsMulCommutative`.
  have hnonab' : ¬ IsMulCommutative G := fun hc => by
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (@mul_comm' G _ hc a b)
  haveI : IsCyclic ↥(S : Subgroup G) := hcyc
  exact (OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two (G := G) hnonab' S hSne)
    ‹IsSimpleGroup G›

end Work.CORE2A
