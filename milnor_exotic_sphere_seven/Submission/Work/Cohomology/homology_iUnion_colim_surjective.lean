import Mathlib
import Submission.Work.Cohomology.SingularTopFreeDefs
import Submission.Work.Cohomology.pdHom_iUnion_lift

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

/-- The two inclusions `V n ↪ ⋃ k, V k` used in this development agree: `toUnion` is the
subtype-inclusion map written for `inclSet`, and `pdIncl` is the same map written for the
Poincaré-duality development. -/
theorem toUnion_eq_pdIncl {X : TopCat} (V : ℕ → Set X) (n : ℕ) :
    toUnion V n = pdIncl (⋃ k, V k) (V n) (Set.subset_iUnion V n) := by
  ext z; rfl

/-- **Homology of an increasing union of open sets, surjectivity part.** Every homology class of
the union is in the image of the homology of one member.  This is the statement
`Work.Cohomology.pdHom_iUnion_lift` (proved in `pdHom_iUnion_lift.lean` for the inclusion
`pdIncl`), transported to the inclusion `toUnion` used here. -/
theorem homology_iUnion_colim_surjective {X : TopCat} (V : ℕ → Set X)
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V) (m : ℕ)
    (x : ↥((Work.Cohomology.singularChains ℤ (TopCat.of (⋃ k, V k))).homology m)) :
    ∃ (n : ℕ) (y : ↥((Work.Cohomology.singularChains ℤ (TopCat.of (V n))).homology m)),
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (⋃ k, V k)) (Work.Cohomology.toUnion V n)) m).hom y = x := by
  obtain ⟨n, y, hy⟩ := pdHom_iUnion_lift V hopen hmono m x
  exact ⟨n, y, by rw [toUnion_eq_pdIncl]; exact hy⟩

end Work.Cohomology
