import Mathlib
import Submission.Work.LerayHirsch.Twist
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_map
import Submission.Work.Gen.LineTensor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The unit law `L ⊗ ε ≅ L` for the twist

For a complex line bundle `L`, the twist `Work.LerayHirsch.twistCore L ε` by the trivial rank-one
bundle is isomorphic to `L`: the transition functions of the twist are `scl (L.c) • id`, which is
`L.c` by `Work.Gen.scl_smul_id`.  This is the unit law used by the splitting principle, where the
complement produced by Whitney's splitting lemma is `W ⊕ ε¹` and the ε¹-summand becomes the
tautological line bundle after twisting.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ιL ι₀ : Type}

/-- **The unit law of the twist**: `L ⊗ ε ≅ L`. -/
theorem nonempty_bundleIso_twist_trivial [Inhabited ι₀]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL) :
    Nonempty (Work.Thom.BundleIso
      (Work.LerayHirsch.twistCore L
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)) L) := by
  refine Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_map
    (Work.LerayHirsch.twistCore L
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)) L
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) Prod.fst ?_ ?_ ?_
  · intro p
    rw [twistCore_baseSet, trivialVectorBundleCore]
    exact (Set.inter_univ _).symm
  · intro b
    rfl
  · intro p b
    show L.coordChange (L.indexAt b) p.1 b = Work.Gen.scl (L.coordChange (L.indexAt b) p.1 b) •
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    exact Work.Gen.scl_smul_id (L.coordChange (L.indexAt b) p.1 b)

end

end Work.LerayHirsch
