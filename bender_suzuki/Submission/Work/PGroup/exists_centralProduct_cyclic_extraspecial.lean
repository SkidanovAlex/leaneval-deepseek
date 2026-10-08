import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Symplectic.Main
import Submission.Work.PGroup.Symplectic.allAbelianCharCyclic_subtype
import Submission.Work.PGroup.Symplectic.conclusion_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- **Feit–Thompson 3.5 (P. Hall's theorem on `p`-groups of symplectic type).**

Let `G` be a group, `p` an odd prime, and `P ≤ G` a finite nonabelian `p`-subgroup.  Assume that
every abelian subgroup `A ≤ P` which is invariant under conjugation by the normalizer `N_G(P)`
is cyclic.  Then `P` is the internal central product of a cyclic subgroup `Cc` and an
extraspecial subgroup `E` of exponent dividing `p`. -/
theorem exists_centralProduct_cyclic_extraspecial {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (P : Subgroup G) [Finite P] (hP : IsPGroup p P)
    (hnonab : ¬ IsMulCommutative P)
    (h : ∀ A : Subgroup G, A ≤ P → (∀ g : G, g ∈ Subgroup.normalizer (P : Set G) →
        Work.PGroup.conjBy g A = A) → IsMulCommutative A → ∃ a : G, A = Subgroup.zpowers a) :
    ∃ Cc E : Subgroup G, Work.PGroup.IsCentralProduct P Cc E ∧
      (∃ a : G, Cc = Subgroup.zpowers a) ∧
      Work.PGroup.IsExtraspecial p E ∧ Monoid.exponent E ∣ p := by
  exact Work.PGroup.Symplectic.conclusion_map_subtype P
    (Work.PGroup.Symplectic.symplectic_main hp hodd hP hnonab
      (Work.PGroup.Symplectic.allAbelianCharCyclic_subtype h))

end Work.PGroup
