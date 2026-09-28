import Mathlib

namespace Work.EMFG

/-- An arbitrary (possibly infinite) product of contractible spaces is contractible.

Each factor `X i` is homotopy equivalent to `Unit`, and `ContinuousMap.HomotopyEquiv.piCongrRight`
promotes a family of homotopy equivalences to a homotopy equivalence of the indexed products
`(i : ι) → X i ≃ₕ (i : ι) → Unit`. The latter is a nonempty subsingleton, hence contractible,
and contractibility transfers back along the homotopy equivalence. -/
theorem contractibleSpace_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (h : ∀ i, ContractibleSpace (X i)) : ContractibleSpace ((i : ι) → X i) := by
  classical
  have hpi : ContinuousMap.HomotopyEquiv ((i : ι) → X i) ((i : ι) → Unit) :=
    ContinuousMap.HomotopyEquiv.piCongrRight (fun i => by
      haveI : ContractibleSpace (X i) := h i
      exact (ContractibleSpace.hequiv_unit (X i)).some)
  exact hpi.contractibleSpace

end Work.EMFG
