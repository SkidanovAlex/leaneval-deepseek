import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusMain
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_at_pole
import Submission.Lib.Unif2.Work.Modulus.poleOrderModulus

/-!
# The holomorphic modulus of a Green function on a simply connected surface

This module assembles the "periods" step of the hyperbolic case of uniformization in the simply
connected case, using the triviality of the monodromy of the modulus bundle rather than the
classical period computation:

* `Work.SC.ModulusMain` produces a global branch `Φ` of the multivalued function `exp (-(E + iE*))`
  from a *continuous section* of the modulus bundle — which exists because the monodromy of the
  covering `Work.SC.branchProj` over the simply connected `X` is trivial;
* `Work.SimplyConnected.Modulus.exists_isModulusBranch_at_pole` (with
  `Work.Modulus.localHolomorphicModulus`) supplies a branch at the pole, hence the non-emptiness of
  the bundle and the logarithmic pole of the branch;
* `Work.Modulus.poleOrderModulus` recovers the *simple* zero of the global branch (equivalently its
  logarithmic pole) from the modulus identity and the two-sided pole estimate of `E`.

The only input is the covering-space property of the projection of the modulus bundle, isolated as
the explicit hypothesis `hcov` of the theorem below (it is provided by
`Work.SC.isCoveringMap_branchProj`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The holomorphic modulus of a strong Green function on a simply connected surface.**  Given
the covering-space property of the modulus bundle (`hcov`), a Green function `E` with pole `z₀`
admits a global branch `Φ` of the multivalued function `exp (-(E + iE*))`; subtracting the pole
order of `E` from the growth of `Φ`, `Φ` has a simple zero (a logarithmic pole) at `z₀`. -/
theorem exists_holomorphic_modulus_of_hasGreenFunctionE [SimplyConnectedSpace X] {z₀ : X}
    {E : X → ℝ} (hE : Submission.HasGreenFunctionE z₀ E)
    (hcov : @IsCoveringMap (ModulusBundle z₀ E) X (modulusBundleTopology z₀ E) _
      (branchProj z₀ E)) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  obtain ⟨U, Φ₀, hbr, hU, _hpole⟩ :=
    Work.SimplyConnected.Modulus.exists_isModulusBranch_at_pole (X := X) hE
  have hne : (branchSet z₀ E).Nonempty :=
    ⟨(z₀, Φ₀ z₀, chartDeriv Φ₀ z₀),
      ⟨U, Φ₀, hbr, mem_of_mem_nhds hU, rfl, rfl⟩⟩
  obtain ⟨Φ, hhol, hne0, hmod⟩ :=
    exists_holomorphic_modulus_of_isCoveringMap (z₀ := z₀) (E := E) hcov hne
  exact ⟨Φ, hhol, Work.Modulus.poleOrderModulus hE hhol hne0 hmod, hmod⟩

end Work.SC
