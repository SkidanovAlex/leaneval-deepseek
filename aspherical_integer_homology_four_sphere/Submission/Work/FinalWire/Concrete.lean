/-
# `FinalWire/Concrete.lean` — the concrete assembly `Work.RTOwed.rtData`

The generic wiring of `Submission/Work/FinalWire/Basic.lean` is parameterised by an ambient
`[rt : Work.Space.RTData]`, a `[Work.FinalWire.TorusStandard rt]` and a
`[Work.CurvModels.ModelCurvature rt.models]`.  For the concrete assembly of the project — the
instance `Work.RTOwed.rtData` registered by the area `RTOwed` — both of the latter are provided
here:

* `Work.FinalWire.instTorusStandardRTData`: the filling tori of `Work.RTOwed.rtData` *are*
  `(ℝ/ℤ)²`, with the identification being the `tor` field of the cusp chart data
  (`Work.RTOwed.cuspGlueData v`); and
* the curvature datum `Work.CurvModels.ModelCurvature` is the instance
  `Work.RTOwed.modelCurvature` of the area `RTOwed` (imported, not restated).

Consequently the two entry points below have *exactly* the two named inputs,
`hA` — in the exact form exported by the area `MbarHomology`, i.e. phrased for
`Work.FoldInst.Mbar` — and the bridge square `hsq`.  They are the recommended spelling of the
wiring of `Submission.lean`; see `Submission/Work/FinalWire/Wiring.lean`.
-/
import Submission.Work.FinalWire.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.defProp false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace Work.FinalWire

noncomputable section

/-! ## §1  The standard-torus identification of the concrete assembly -/

/-- **The filling torus of `Work.RTOwed.rtData` is the standard `(ℝ/ℤ)²`**, by the cusp chart data
of the area `RTOwed` (`Work.RTOwed.cuspGlueData v |>.tor`); note that `rt.core.Torus v` *is*
`Fin 2 → AddCircle 1` definitionally, so the homeomorphism is an identity on the nose, but the
`tor` field is the proof that the *registry* (the assembly datum) is the standard one. -/
instance instTorusStandardRTData : TorusStandard Work.RTOwed.rtData where
  homeo := fun v => (Work.RTOwed.cuspGlueData v).tor

/-- **The same for the registered instance constant** `Work.RTOwed.instRTData` (the name that
typeclass inference actually returns when it searches for an element of `Work.Space.RTData`):
instance search does not unfold a plain `def` such as `Work.RTOwed.instRTData` (`:= rtData`), so
this second registration is what makes the `[TorusStandard rt]` argument of the generic entry
points of `Submission/Work/FinalWire/Basic.lean` *inferable* rather than explicit.  The two
constants are definitionally equal, hence so are the two instances. -/
instance instTorusStandardInstRTData : TorusStandard Work.RTOwed.instRTData where
  homeo := fun v => (Work.RTOwed.cuspGlueData v).tor

/-- The registered `Work.Space.RTData` instance is the assembly datum of the area `RTOwed`. -/
theorem instRTData_eq_rtData : Work.RTOwed.instRTData = Work.RTOwed.rtData := rfl

/-- The identification of the concrete filling torus with `(ℝ/ℤ)²`, as a named definition. -/
def torus_homeo_concrete (v : Work.Space.Cusp) :
    (Work.RTOwed.rtData).core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)) :=
  (TorusStandard.homeo (rt := Work.RTOwed.rtData) v)

/-- **The hyperbolic piece of the concrete assembly is `Work.FoldInst.Mbar`** (definitional), which
is what makes the `eA` hypothesis below *literally* the export `Work.MbarHomology.eA`. -/
theorem mbar_concrete : (Work.RTOwed.rtData).core.Mbar = Work.FoldInst.Mbar := rfl

/-! ## §2  The concrete named inputs -/

/-- **The `eA` input of the concrete assembly**, in the exact exported form of the area
`MbarHomology` (`Work.MbarHomology.eA : ∀ k, ModelA k ≅ H_k(M̄)`, `M̄ = Work.FoldInst.Mbar`). -/
abbrev EAConcrete : Type _ :=
  ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
    LeanEval.Topology.intHomology k (TopCat.of Work.FoldInst.Mbar)

/-- **The bridge square of the concrete assembly**: the first Mayer–Vietoris map of the cover
`M̂ = A ∪ B` is the concrete matrix `Work.HomologyMV.wConcrete`, in the bases of the models induced
by the concrete computations of the pieces. -/
abbrev SquareOfConcrete (hA : EAConcrete) : Prop :=
  SquareOf (rt := Work.RTOwed.rtData)
    (pieceData_of (rt := Work.RTOwed.rtData) hA)

/-- **`EAConcrete` and the generic `EA` of the concrete assembly are the same type**
(definitionally: `(Work.RTOwed.rtData).core.Mbar = Work.FoldInst.Mbar`,
`Work.FinalWire.mbar_concrete`).  The two conversions are the identity, and they are provided so
that a caller can move the `eA` input of the area `MbarHomology` between the two spellings
explicitly if an elaboration ever needs the help. -/
def EAConcrete_to_EA (h : EAConcrete) : EA Work.RTOwed.rtData := h

/-- The converse direction of `Work.FinalWire.EAConcrete_to_EA`. -/
def EA_to_EAConcrete (h : EA Work.RTOwed.rtData) : EAConcrete := h

/-! ## §3  The two entry points -/

/-- **`Work.Final.FinalInputs` of the concrete assembly**, from `eA` and the bridge square: the
wiring of `Submission.lean`, with the two remaining named inputs explicit. -/
def finalInputs_of_concrete (hA : EAConcrete) (hsq : SquareOfConcrete hA) :
    Work.Final.FinalInputs :=
  finalInputs_of (rt := Work.RTOwed.rtData) hA hsq

/-- **`Work.Final.FinalInputs` of the concrete assembly**, from `eA` and the delivered bridge
interface `Work.PieceHomology.Bridge`. -/
def finalInputs_of_bridge_concrete (hA : EAConcrete)
    (B : Work.PieceHomology.Bridge (rt := Work.RTOwed.rtData)
      (pieceData_of (rt := Work.RTOwed.rtData) hA)) : Work.Final.FinalInputs :=
  finalInputs_of_bridge (rt := Work.RTOwed.rtData) hA B

/-- **The challenge theorem, from the two named inputs of the concrete assembly.** -/
theorem aspherical_integer_homology_four_sphere_of_concrete (hA : EAConcrete)
    (hsq : SquareOfConcrete hA) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  aspherical_integer_homology_four_sphere_of (rt := Work.RTOwed.rtData) hA hsq

/-- **The challenge theorem, from `eA` and the bridge interface.** -/
theorem aspherical_integer_homology_four_sphere_of_bridge_concrete (hA : EAConcrete)
    (B : Work.PieceHomology.Bridge (rt := Work.RTOwed.rtData)
      (pieceData_of (rt := Work.RTOwed.rtData) hA)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  aspherical_integer_homology_four_sphere_of_bridge (rt := Work.RTOwed.rtData) hA B

/-! ## §4  The `FinalInputs` of the concrete assembly, field by field -/

/-- The hidden `rt` of the concrete wiring is the registered instance `Work.RTOwed.rtData`
(so the space of the challenge theorem is `M̂` of the area `RTOwed`). -/
theorem finalInputs_of_concrete_rt (hA : EAConcrete) (hsq : SquareOfConcrete hA) :
    (finalInputs_of_concrete hA hsq).rt = Work.RTOwed.rtData := rfl

/-- The `L` field is the Mayer–Vietoris sequence of `M̂ = A ∪ B` built in `Work.HomologyIso`. -/
theorem finalInputs_of_concrete_L (hA : EAConcrete) (hsq : SquareOfConcrete hA) :
    (finalInputs_of_concrete hA hsq).L
      = Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData) := rfl

/-- The `eM` field of the concrete wiring. -/
theorem finalInputs_of_concrete_eM (hA : EAConcrete) (hsq : SquareOfConcrete hA) (k : ℤ) :
    (finalInputs_of_concrete hA hsq).eM k
      = Work.HomologyIso.eM (rt := Work.RTOwed.rtData)
          (pieceData_of (rt := Work.RTOwed.rtData) hA) k := rfl

/-- The `eN` field of the concrete wiring. -/
theorem finalInputs_of_concrete_eN (hA : EAConcrete) (hsq : SquareOfConcrete hA) (k : ℤ) :
    (finalInputs_of_concrete hA hsq).eN k
      = Work.HomologyIso.eN (rt := Work.RTOwed.rtData)
          (pieceData_of (rt := Work.RTOwed.rtData) hA) k := rfl

/-- The `hX` field of the concrete wiring. -/
theorem finalInputs_of_concrete_hX (hA : EAConcrete) (hsq : SquareOfConcrete hA) (k : ℕ) :
    (finalInputs_of_concrete hA hsq).hX k
      = Work.HomologyIso.mhatLES_hX (rt := Work.RTOwed.rtData) k := rfl

/-! ## §5  The two named inputs, bundled — the instance-shaped wiring -/

/-- **The two named inputs of the final assembly, bundled.**  Its fields are the two still-owed
exports of the areas:

* `ea` — `Work.MbarHomology.eA`, the homology of the hyperbolic piece `M̄`, and
* `square` — the bridge square (`Work.HomologyIso.Inputs.hsq` / the `hsq` field of
  `Work.PieceHomology.Bridge`), i.e. the Mayer–Vietoris matrix certificate of `rtdata/`.

Bundling them makes the wiring of `Submission.lean` literally an instance registration, see
`Work.FinalWire.instFinalInputsOfNamedInputs`. -/
class NamedInputs where
  /-- The homology of the hyperbolic piece `M̄` (`Work.MbarHomology.eA`). -/
  ea : EAConcrete
  /-- The bridge square: the first Mayer–Vietoris map is `Work.HomologyMV.wConcrete`. -/
  square : SquareOfConcrete ea

/-- **The `Work.Final.FinalInputs` of the challenge, from the bundled named inputs.**  This is
registered as an instance: as soon as an instance `Work.FinalWire.NamedInputs` is available (the
one line `instance : Work.FinalWire.NamedInputs := ⟨Work.MbarHomology.eA, hsQ⟩`), the challenge
theorem is `Work.Final.aspherical_integer_homology_four_sphere`, with no further argument. -/
instance instFinalInputsOfNamedInputs [I : NamedInputs] : Work.Final.FinalInputs :=
  finalInputs_of_concrete I.ea I.square

/-- **The challenge theorem from the bundled named inputs.** -/
theorem aspherical_integer_homology_four_sphere_of_namedInputs [I : NamedInputs] :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere

/-- **The challenge theorem from the two named inputs, in the generic spelling** (the instance
arguments `Work.Space.RTData`, `Work.FinalWire.TorusStandard` and
`Work.CurvModels.ModelCurvature` are all inferred). -/
example (hA : EAConcrete) (hsq : SquareOfConcrete hA) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  aspherical_integer_homology_four_sphere_of hA hsq

end

end Work.FinalWire
