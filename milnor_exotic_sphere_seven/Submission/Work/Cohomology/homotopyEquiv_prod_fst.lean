import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

/-- If `Y` is contractible, the projection `X × Y → X` is a homotopy equivalence. -/
theorem homotopyEquiv_prod_fst (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] :
    Nonempty (ContinuousMap.HomotopyEquiv (X × Y) X) := by
  obtain ⟨y₀, hy₀⟩ := id_nullhomotopic Y
  refine ⟨{ toFun := ContinuousMap.fst
            invFun := ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y₀)
            left_inv := ?_
            right_inv := ?_ }⟩
  · have hmain : ((ContinuousMap.id X).prodMap (ContinuousMap.const Y y₀)).Homotopic
        ((ContinuousMap.id X).prodMap (ContinuousMap.id Y)) :=
      (ContinuousMap.Homotopic.refl (ContinuousMap.id X)).prodMap hy₀.symm
    have h1 : (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y₀)).comp
        ContinuousMap.fst = (ContinuousMap.id X).prodMap (ContinuousMap.const Y y₀) := by
      ext p <;> simp [ContinuousMap.prodMap_apply, Prod.map]
    have h2 : (ContinuousMap.id X).prodMap (ContinuousMap.id Y) = ContinuousMap.id (X × Y) := by
      ext p <;> simp [ContinuousMap.prodMap_apply, Prod.map]
    simpa [h1, h2.symm] using hmain
  · have h1 : ContinuousMap.fst.comp
        (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y₀))
        = ContinuousMap.id X := by
      ext p; simp
    rw [h1]

end Work.Cohomology
