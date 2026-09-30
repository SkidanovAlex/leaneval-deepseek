import Mathlib
import Submission.Work.Pi6.MSS.TensorDefs
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.homotopyEquivDual
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cohomology of the normalized chain complex is singular cohomology

The normalized chain complex `X.normalizedChainComplex 𝕜` of the singular simplicial set of a space
`B` is homotopy equivalent to the (unnormalized) singular chain complex `X.chainComplex 𝕜`, by the
split-epi/split-mono pair `toNormalizedChainComplex`/`fromNormalizedChainComplex` of
`SSet.homotopyEquivNormalizedChainComplex`.  Dualising this homotopy equivalence
(`Work.Cohomology.homotopyEquivDual`) and taking homology gives the comparison
`H^s(Hom_𝕜(N_*(B;𝕜),𝕜)) ≅ H^s(B;𝕜)`.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

theorem normCoh (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ) :
    Nonempty ((Work.Cohomology.dualComplex 𝕜 (Work.Pi6.MSS.normC 𝕜 B)).homology s ≅
      Work.Pi6.Coh 𝕜 B s) := by
  obtain ⟨e⟩ := Work.Cohomology.homotopyEquivDual 𝕜
    ((TopCat.toSSet.obj (TopCat.of B)).homotopyEquivNormalizedChainComplex (ModuleCat.of 𝕜 𝕜))
  exact ⟨e.toHomologyIso s⟩

end Work.Pi6.MSS
