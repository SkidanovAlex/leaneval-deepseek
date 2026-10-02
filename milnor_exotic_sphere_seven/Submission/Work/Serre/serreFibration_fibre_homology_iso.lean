import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.Chains
import Submission.Work.Stems.Engine.E2c
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Stems.Cubical.Kop
import Submission.Work.Serre.E2dFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre homology of a Serre fibration is independent of the base point along a path

For a Serre fibration `q : X → B` and a path `γ : I → B`, the homology of the fibre `q⁻¹(γ 0)` is
isomorphic to that of `q⁻¹(γ 1)`, in every degree:

`Work.Serre.serreFibration_fibre_homology_iso`.

This is the "fibre transport" statement that makes the Serre exact sequence of a fibration
(`Work.Serre.Engine`, `Work.StemsB.SerreExact`) independent of the choice of base point: the
homology of the fibre `F` of a fibration over a path-connected base is well defined up to
isomorphism, so the E2-page of the Serre spectral sequence can be written with `H_*(F)`.

The mathematical content (the vanishing of the relative homology of the pair
`(X, q⁻¹{z₀})` for a base contracted onto `z₀`, hence the isomorphism `H_*(q⁻¹{z₀}) ≅ H_*(X)`, and
the resulting identification of the two fibres of the pullback `γ^*X → I`) is developed in the
`Work.Serre` engine, in the cubical form `Work.Serre.fibre_iso_pullback`, which is stated for a
cube base `I^m`.  The present file is the interval case: `I = I¹` via the standard identification
`Work.Stems.Cubical.icOneToUnit`, and the fibre of `q` over the endpoints `γ 0`, `γ 1` of the path
is the fibre of the pullback fibration `Work.StemsB.pullbackSnd q γ` over the vertices `0`, `1` of
the cube (a definitional identity).

Note that no hypothesis on `B` (path connectedness, say) is needed: the path `γ` itself already
connects the two base points, and the two fibres are simultaneously empty or simultaneously
nonempty, so the statement is not vacuous and does not need an ambient nonemptiness assumption.
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- **The fibre homology of a Serre fibration does not depend on the point of the base along a
path.** -/
theorem serreFibration_fibre_homology_iso {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (γ : C(unitInterval, B)) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q (γ 0)))).homology n ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q (γ 1)))).homology n) := by
  -- `fibre_iso_pullback` for the cube `I¹` replaces the base points `γ 0`, `γ 1` by the vertices
  -- `icOnePt 0`, `icOnePt 1` of `I¹`; `icOneToUnit (icOnePt b) = b` definitionally.
  obtain ⟨e⟩ := fibre_iso_pullback 1 q hq (γ.comp Work.Stems.Cubical.icOneToUnit)
    (Work.Stems.Cubical.icOnePt 0) (Work.Stems.Cubical.icOnePt 1) n
  exact ⟨e.symm⟩

end Work.Serre
