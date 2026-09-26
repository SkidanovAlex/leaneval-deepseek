import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.TorusCover.ParamTorus_exists_liftOf
import Submission.Work.TorusCover.Basic
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square

/-!
# Components of a surface-open set are path connected

`Work.PinchLemma3.ClosedDiscA.isPathConnected_connectedComponentIn_carrier`:
if `K ⊆ ℝ³` lies in the surface `F = P.carrier` of a parametrised torus `P` and is **open in
that surface**, then the connected component of any `x ∈ K` is path connected.

The point is that `F` is a topological surface: it is homeomorphic to `ℝ²/2πℤ²`
(`Work.TorusCover.quotHomeo`), a quotient of the locally path connected plane, hence locally
path connected.  An open subset of a locally path connected space is again locally path
connected, and in a locally path connected space the connected components coincide with the
path components, which are path connected.

## Layout of the file

* `locallyPathConnected_carrier` — the surface `F = P.carrier` is locally path connected;
* `subtypePreimageHomeo` — for `K ⊆ P.carrier`, the subtype `↥K ⊆ ℝ³` is canonically
  homeomorphic to the subspace `↥(P.carrier ∩ K)` of the surface;
* `locallyPathConnected_of_isOpenInCarrier` — the subspace `↥K ⊆ ℝ³` is locally path
  connected when `K` is open in the surface;
* the main theorem, obtained from `connectedComponentIn_eq_image`,
  `IsPathConnected.image`, `pathComponent_eq_connectedComponent` and
  `isPathConnected_pathComponent`.
-/

-- The three local instances below are genuinely used as typeclass instances, so `haveI` (rather
-- than the `have` suggested by this linter) is the correct binder.
set_option linter.style.haveILetI false

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The surface of a parametrised torus is locally path connected.**  It is homeomorphic to
`ℝ²/2πℤ²` (`Work.TorusCover.quotHomeo`), a quotient of the locally path connected parameter
plane. -/
theorem locallyPathConnected_carrier (P : Work.CoreTopology.ParamTorus) :
    LocallyPathConnectedSpace ↥P.carrier := by
  haveI : LocallyPathConnectedSpace ((ℝ × ℝ) ⧸ Work.TorusCover.lattice) := by
    change LocallyPathConnectedSpace (Quot (QuotientAddGroup.leftRel Work.TorusCover.lattice))
    infer_instance
  exact Topology.IsOpenEmbedding.locallyPathConnectedSpace
    (Homeomorph.isOpenEmbedding (Work.TorusCover.quotHomeo P).symm)

/-- For `K ⊆ P.carrier`, the subtype `↥K` of `ℝ³` is canonically homeomorphic to the subspace
`↥(Subtype.val ⁻¹' K)` of the surface `↥P.carrier`; both carry the subspace topology of `K`. -/
noncomputable def subtypePreimageHomeo {K : Set R3} (hKc : K ⊆ P.carrier) :
    ↥K ≃ₜ ↥(Subtype.val ⁻¹' K : Set P.carrier) where
  toFun y := ⟨⟨y.1, hKc y.2⟩, y.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv y := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **A subset of the surface which is open in the surface is locally path connected** (as a
subspace of `ℝ³`): it is open inside the locally path connected surface. -/
theorem locallyPathConnected_of_isOpenInCarrier {K : Set R3}
    (hK : Work.SurgeryInvariance.IsOpenInCarrier P K) (hKc : K ⊆ P.carrier) :
    LocallyPathConnectedSpace ↥K := by
  haveI : LocallyPathConnectedSpace ↥P.carrier := locallyPathConnected_carrier P
  haveI : LocallyPathConnectedSpace ↥(Subtype.val ⁻¹' K : Set P.carrier) :=
    IsOpen.locallyPathConnectedSpace hK
  exact Topology.IsOpenEmbedding.locallyPathConnectedSpace
    (Homeomorph.isOpenEmbedding (subtypePreimageHomeo (P := P) hKc))

theorem isPathConnected_connectedComponentIn_carrier {P : Work.CoreTopology.ParamTorus}
    {K : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK : Work.SurgeryInvariance.IsOpenInCarrier P K) (hKc : K ⊆ P.carrier)
    {x : LeanEval.KnotTheory.PardonDistortion.R3} (hx : x ∈ K) :
    IsPathConnected (connectedComponentIn K x) := by
  haveI : LocallyPathConnectedSpace ↥K := locallyPathConnected_of_isOpenInCarrier hK hKc
  rw [connectedComponentIn_eq_image hx]
  refine IsPathConnected.image ?_ continuous_subtype_val
  rw [← pathComponent_eq_connectedComponent]
  exact isPathConnected_pathComponent

end

end Work.PinchLemma3.ClosedDiscA
