import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.group_fg_of_augIdeal_fg
import Submission.Work.ORHomAlg.GroupAlgebra

set_option autoImplicit false

namespace Work.ORFlatness

universe u

open MulOpposite

section Helpers

variable (K : Type u) [CommRing K] (G : Type u) [Group G]

/-- If the augmentation of `f` vanishes, then `f` is a `K`-linear combination of the elements
`single t 1 - 1`, `t` ranging over the support of `f`. -/
lemma eq_sum_smul_single_sub_one_of_augmentation_eq_zero {f : MonoidAlgebra K G}
    (hf : Work.ORFP2.augmentation K G f = 0) :
    f = ∑ t ∈ f.coeff.support, f.coeff t • (MonoidAlgebra.single t 1 - 1) := by
  conv_lhs => rw [Work.ORFP2.eq_sum_smul_single K G f]
  have hsub : (∑ t ∈ f.coeff.support, f.coeff t • (MonoidAlgebra.single t 1 - 1))
      = (∑ t ∈ f.coeff.support, f.coeff t • MonoidAlgebra.single t 1)
        - (∑ t ∈ f.coeff.support, f.coeff t • (1 : MonoidAlgebra K G)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => smul_sub _ _ _
  have hz : ∑ t ∈ f.coeff.support, f.coeff t = 0 := by
    have h1 := hf
    rw [Work.ORFP2.augmentation_eq_sum_coeff K G f] at h1
    exact h1
  rw [hsub, ← Finset.sum_smul, hz, zero_smul, sub_zero]

/-- Every element of the kernel of the augmentation is in the augmentation ideal. -/
lemma ker_augmentation_le_augIdeal :
    RingHom.ker (Work.ORFP2.augmentation K G) ≤ Work.ORFP2.augIdeal K G := by
  intro f hf
  rw [RingHom.mem_ker] at hf
  rw [eq_sum_smul_single_sub_one_of_augmentation_eq_zero K G hf]
  apply Submodule.sum_mem
  intro t _
  exact Submodule.smul_of_tower_mem _ (f.coeff t) (Work.ORFP2.single_sub_one_mem_augIdeal K G t)

/-- The augmentation ideal is the kernel of the augmentation. -/
lemma augIdeal_eq_ker_augmentation :
    Work.ORFP2.augIdeal K G = RingHom.ker (Work.ORFP2.augmentation K G) :=
  le_antisymm (Work.ORFP2.augIdeal_le_ker_augmentation K G)
    (ker_augmentation_le_augIdeal K G)

/-- The augmentation ideal is two-sided (it is a kernel of a ring homomorphism). -/
instance instIsTwoSidedAugIdeal : (Work.ORFP2.augIdeal K G).IsTwoSided := by
  rw [augIdeal_eq_ker_augmentation K G]
  infer_instance

end Helpers

/-- The augmentation ideal `Work.ORFP2.augIdeal K G` of the group algebra is two-sided, being the kernel of the algebra homomorphism `Work.ORFP2.augmentation K G : K[G] →+* K` (`x ∈ augIdeal ↔ augmentation K G x = 0`, and `augmentation` is multiplicative). Hence right multiplication by `K[G]` makes it a right `K[G]`-module: `op a • x := x * a`. This bundled form of the statement asks for that `Module (K[G])ᵐᵒᵖ ↥(augIdeal K G)` structure together with the two compatibility conditions with the `K`-module structure (which is the restriction along `K → K[G]`, `k • x := (algebraMap K K[G] k) * x`).

Suggested route: show `Work.ORFP2.augIdeal K G = RingHom.ker (Work.ORFP2.augmentation K G)` from `Work.ORFP2.augIdeal_eq_span` (the generators `single g 1 - 1` lie in the kernel, and every element of the kernel is in the span), then `mul_mem_right`. Define the right action by `op a • x = ⟨(x : K[G]) * a, htwo_sided x.2 a⟩`. `IsScalarTower` is associativity of multiplication in `K[G]` (and centrality of `algebraMap K K[G]`), and `SMulCommClass` reduces to `(algebraMap k) * (x * a) = ((algebraMap k) * x) * a`. -/
theorem exists_augIdeal_rightModule (K : Type u) [CommRing K] (G : Type u) [Group G] :
    ∃ (inst : Module (MonoidAlgebra K G)ᵐᵒᵖ ↥(Work.ORFP2.augIdeal K G)),
      (letI := inst;
        IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ ↥(Work.ORFP2.augIdeal K G) ∧
        SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ ↥(Work.ORFP2.augIdeal K G)) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · refine ⟨fun k a x => ?_⟩
    apply Subtype.ext
    show x.1 * (k • a).unop = k • (x.1 * a.unop)
    rw [MulOpposite.unop_smul]
    exact Algebra.mul_smul_comm k x.1 a.unop
  · refine ⟨fun k a x => ?_⟩
    apply Subtype.ext
    show k • (x.1 * a.unop) = (k • x.1) * a.unop
    rw [Algebra.smul_mul_assoc]

end Work.ORFlatness
