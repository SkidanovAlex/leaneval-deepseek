import Submission.Work.ASM.Basic
import Submission.OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# ASM: a simple non-abelian group has no cyclic Sylow 2-subgroup

The missing case of the Bender setup: `SimpleStepProp` is proved for a minimal counterexample
`G` whose Sylow 2-subgroups are dihedral, but `DihOrCycSylow G` also allows *cyclic* Sylow
2-subgroups.  Those are impossible here:

* if the Sylow 2-subgroup is trivial then `|G|` is odd, so `G` is solvable by Feit–Thompson;
* otherwise Isaacs Cor. 5.19 (`OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two`)
  says a non-abelian finite group with a nontrivial cyclic Sylow 2-subgroup is not simple.
-/

open scoped MatrixGroups
open Subgroup

namespace Work.ASM

open Work.GW2

/-- A finite simple non-abelian group has no cyclic Sylow 2-subgroup. -/
theorem false_of_cyclic_sylow_two {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hFT : FeitThompsonProp)
    (P : Sylow 2 G) (hcyc : IsCyclic ↥(P : Subgroup G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hbot : (P : Subgroup G) = ⊥
  · have hodd : Odd (Nat.card G) := by
      rw [← Subgroup.index_bot (G := G), ← hbot]
      refine Nat.not_even_iff_odd.mp fun h2 => ?_
      exact Sylow.not_dvd_index P (even_iff_two_dvd.mp h2)
    exact false_of_solvable_simple hnonab (hFT G hodd)
  · exact absurd ‹IsSimpleGroup G›
      (OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_isCyclic_sylow_two
        (not_isMulCommutative_of_exists_mul_ne hnonab) P hbot (hPcyc := hcyc))

end Work.ASM
