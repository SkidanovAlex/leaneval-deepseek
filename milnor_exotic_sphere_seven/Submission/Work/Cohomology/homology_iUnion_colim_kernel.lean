import Mathlib
import Submission.Work.Cohomology.SingularTopFreeDefs
import Submission.Work.Cohomology.pdHom_iUnion_kill

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

/-- The inclusion of a subspace into a larger one as `Work.Cohomology.inclSet` agrees with the
inclusion `Work.Cohomology.pdIncl` of `Work.Cohomology.pd_good`. -/
theorem inclSet_eq_pdIncl {X : TopCat} {A B : Set X} (h : A ⊆ B) :
    inclSet h = pdIncl B A h := rfl

/-- The inclusion `V n ⊆ ⋃ k, V k` agrees with the corresponding `pdIncl`. -/
theorem toUnion_eq_pdIncl {X : TopCat} (V : ℕ → Set X) (n : ℕ) :
    toUnion V n = pdIncl (⋃ k, V k) (V n) (Set.subset_iUnion V n) := rfl

theorem homology_iUnion_colim_kernel {X : TopCat} (V : ℕ → Set X)
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V) (m : ℕ) (n : ℕ)
    (y : ↥((Work.Cohomology.singularChains ℤ (TopCat.of (V n))).homology m))
    (hy : (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
      (TopCat.of (⋃ k, V k)) (Work.Cohomology.toUnion V n)) m).hom y = 0) :
    ∃ (k : ℕ) (hk : n ≤ k),
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (V k)) (Work.Cohomology.inclSet (hmono hk))) m).hom y = 0 := by
  exact pdHom_iUnion_kill V hopen hmono m n y hy

end Work.Cohomology
