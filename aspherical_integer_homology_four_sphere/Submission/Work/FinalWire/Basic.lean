/-
# Area `Submission/Work/FinalWire/` — the final wiring of the challenge theorem

This area is the **final assembly**: it wires the delivered areas into a single
`Work.Final.FinalInputs`, from which `Work.Final.aspherical_integer_homology_four_sphere` gives

```lean
∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere
```

(the statement of `Challenge.lean`).  The module map and the exact list of the *named inputs* that
are still owed by other areas are in `Submission/Work/FinalWire/NOTES.md`; the ready-to-apply
wiring of `Submission.lean` is in `Submission/Work/FinalWire/Wiring.lean`.

## What is discharged here, and what is not

All the *structural* fields of `Work.Final.FinalInputs` are produced by the delivered areas and are
consumed here without further input:

| field | produced by |
|---|---|
| `rt` | `Work.RTOwed.rtData` (instance `Work.Space.RTData`) |
| `cov_smooth` | `Work.LCSmooth.instContMDiffCovariantDerivativeMhatCov` (instance) |
| `curvLe` | `Work.CurvModels.hmodels` + `Work.Final.curvLe_of_models` (`Work.CurvModels.ModelCurvature` instance) |
| `L` | `Work.HomologyIso.mhatLES` (= `Work.Final.FinalInputs.mhatLES`) |
| `hX` | `Work.HomologyIso.mhatLES_hX` |

What is *not* delivered yet, and therefore enters as a named hypothesis:

* `hA` — the homology of the hyperbolic piece `M̄`, i.e. `Work.MbarHomology.eA`
  (`∀ k, ModelA k ≅ H_k(M̄)`; the area `MbarHomology` is finishing `Mbar.mbarAtlas_exists`), and
* `hsq` — the bridge: the first Mayer–Vietoris map of the cover `M̂ = A ∪ B` is the concrete matrix
  `Work.HomologyMV.wConcrete` in the bases of the models.  In the delivered interface this is an
  inhabitant of `Work.PieceHomology.Bridge`; `Work.FinalWire.SquareOf` below is the plain `Prop`
  form (literally the type of the field `Work.HomologyIso.Inputs.hsq`).

Everything else — the per-cusp computations `eTorus` (`H_k(∂[-1,1]² × T²_v)`, from
`Work.PieceHomology.eTorus_concrete`) and `eT2` (`H_k(T²_v)`, from
`Work.PieceHomology.eT2_concrete`), the algebra of the five cusps, the passage from the
`ℕ`-graded pieces to the `ℤ`-graded Mayer–Vietoris sequence and the `eN`-splitting — is proved in
the areas `PieceHomology` and `HomologyIso` and is *used* here, not restated.
-/
import Mathlib
import Submission.Work.Final.All
import Submission.Work.LCSmooth.All
import Submission.Work.CurvModels.FinalBridge
import Submission.Work.RTOwed.FinalInstance
import Submission.Work.HomologyIso.Final
import Submission.Work.PieceHomology.Main
import Submission.Work.PieceHomology.Concrete

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

variable [rt : Work.Space.RTData]

/-! ## §1  The two named inputs -/

/-- **The filling tori of `M̂` are the standard two-torus `(ℝ/ℤ)²`.**

This is *data* that the assembly provider has: for the concrete assembly of
`Work.RTInstance`/`Work.RTOwed`, `rt.core.Torus v` is *definitionally* `Fin 2 → AddCircle 1`, and
the homeomorphism is the `tor` field of the cusp chart data
(`(Work.RTOwed.cuspGlueData v).tor`), see `Work.FinalWire.instTorusStandardRTData` and (for the
instance constant `Work.RTOwed.instRTData` that inference returns) 
`Work.FinalWire.instTorusStandardInstRTData`.

It is a class so that the concrete instance is found by typeclass inference: the named inputs of
`Work.FinalWire.finalInputs_of` are then exactly `hA` and the bridge square. -/
class TorusStandard (rt : Work.Space.RTData) where
  /-- The identification of the `v`-th filling torus with `(ℝ/ℤ)²`. -/
  homeo : ∀ v : Work.Space.Cusp, rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))

/-- **The `eA` input: the homology of the hyperbolic piece `M̄`**, in the exact form in which the
area `MbarHomology` exports it (`Work.MbarHomology.eA`, whose statement is phrased for
`Work.FoldInst.Mbar = rt.core.Mbar` of the concrete assembly). -/
abbrev EA (rt : Work.Space.RTData) : Type _ :=
  ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
    LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar)

/-- **The bridge square**, in the plain `Prop` form of the field `Work.HomologyIso.Inputs.hsq`:
the first Mayer–Vietoris map `H_k(A ∩ B) ⟶ H_k(A) ⊞ H_k(B)` is the concrete matrix
`Work.HomologyMV.wConcrete k` in the bases of the models (the cusp-major bases of
`Work.HomologyMV.Data`, `H_k(M̄)` first on the right).

An inhabitant of the delivered interface `Work.PieceHomology.Bridge D` gives one of these
(`Work.PieceHomology.Bridge.mvSquare`); conversely `Work.FinalWire.bridgeOfSquare` shows that the
identity complexes (`C₁ = C_*(A ∩ B)`, `C₂ = C_*(A) ⊞ C_*(B)`, `φ = mvLeft`) turn a square into a
`Bridge`, so the two formulations carry the same content. -/
def SquareOf (D : Work.HomologyIso.PieceData (rt := rt)) : Prop :=
  ∀ k : ℕ, (D.eAB k).hom ≫ Work.HomologyIso.mvFhat (rt := rt) k
    = Work.HomologyMV.wConcrete (k : ℤ) ≫ (D.eN k).hom

/-! ## §2  The three homology computations of the geometry, from `eA` -/

/-- **The per-cusp data of the geometry from `eA` alone.**  Two of the three declared fields of
`Work.HomologyIso.CuspData` are *proved* (they are the outputs of the area `PieceHomology`):

* `eTorus` — `H_k(∂[-1,1]² × T²_v) ≅ ℤ^{rankT k}` from `∂[-1,1]² ≃ S¹` and Künneth with a circle
  (`Work.PieceHomology.eTorus_concrete`), transported along the torus identification;
* `eT2` — `H_k(T²_v) ≅ ℤ^{rankT2 k}` from the `Δ`-structure of `T²` and Hatcher 2.27
  (`Work.PieceHomology.eT2_concrete`), transported likewise;

and the only input is `hA` (`H_k(M̄) ≅ ℤ^{rankA k}`). -/
def cuspData_of [T : TorusStandard rt] (hA : EA rt) :
    Work.HomologyIso.CuspData (rt := rt) :=
  Work.PieceHomology.cuspData_of_concrete (fun v => T.homeo v) hA

/-- **The three computations of the pieces `A ∩ B`, `A`, `B`**, assembled from the per-cusp data
by the area `HomologyIso` (`Work.HomologyIso.CuspData.toPieceData`: the homotopy equivalences
`A ∩ B ≃ₕ ⊔_v (∂[-1,1]² × T²_v)`, `A ≃ₕ M̄`, `B ≃ₕ ⊔_v T²_v`, the additivity of homology over the
five cusps and the algebra of the free models). -/
def pieceData_of [T : TorusStandard rt] (hA : EA rt) :
    Work.HomologyIso.PieceData (rt := rt) :=
  (cuspData_of (rt := rt) hA).toPieceData

/-! ## §3  The bridge -/

/-- **`Work.HomologyIso.Inputs` from a piece data and the bridge square.**  This is the point
where the last geometric input (the Mayer–Vietoris certificate of `rtdata/`) enters. -/
def inputs_of_data (D : Work.HomologyIso.PieceData (rt := rt)) (hsq : SquareOf (rt := rt) D) :
    Work.HomologyIso.Inputs (rt := rt) where
  toPieceData := D
  hsq := hsq

/-- **The bridge interface gives the square** (this is `Work.PieceHomology.Bridge.mvSquare`). -/
theorem square_of_bridge (D : Work.HomologyIso.PieceData (rt := rt))
    (B : Work.PieceHomology.Bridge (rt := rt) D) : SquareOf (rt := rt) D :=
  fun k => B.mvSquare k

/-- **`Work.HomologyIso.Inputs` from the delivered bridge interface.** -/
def inputs_of_bridge (D : Work.HomologyIso.PieceData (rt := rt))
    (B : Work.PieceHomology.Bridge (rt := rt) D) : Work.HomologyIso.Inputs (rt := rt) :=
  Work.PieceHomology.Bridge.toInputs D B

/-! ## §4  The curvature and smoothness side -/

/-- **`Work.HomologyIso.Remaining` from the delivered instances**: the smoothness of `mhatCov` is
the instance of the area `LCSmooth`, and the curvature bound is the curvature bridge
`Work.Final.curvLe_of_models` fed with the chart-model datum `Work.CurvModels.hmodels` of the
atlas (the `Work.CurvModels.ModelCurvature` instance, registered by the provider of
`Work.Space.RTData`). -/
def remaining [C : Work.CurvModels.ModelCurvature rt.models] :
    Work.HomologyIso.Remaining (rt := rt) where
  cov_smooth := inferInstance
  curvLe := Work.CurvModels.curvLe_of_models (rt := rt)

/-- **`Work.HomologyIso.Remaining` from an explicit curvature bound** (the form used when the
caller has the bound in a different vocabulary, e.g. from `Work.CurvModels.hmodels` or from the
pointwise `sec ≤ 0` route `Work.LCSmooth.curvLe_of_secNonpos_mhat`). -/
def remainingOf
    (curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K) :
    Work.HomologyIso.Remaining (rt := rt) where
  cov_smooth := inferInstance
  curvLe := curvLe

/-! ## §5  The final assembly -/

/-- **THE DELIVERABLE: `Work.Final.FinalInputs` from `eA` and the bridge square.**

The named inputs are exactly the two not-yet-delivered exports; every other field of
`Work.Final.FinalInputs` is produced by the delivered areas (see the module docstring).  The
instance arguments `[TorusStandard rt]` and `[Work.CurvModels.ModelCurvature rt.models]` are
discharged by the registered instances of the concrete assembly
(`Work.FinalWire.instTorusStandardRTData`, `Work.RTOwed.modelCurvature`). -/
def finalInputs_of [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    Work.Final.FinalInputs :=
  Work.HomologyIso.finalInputs (remaining (rt := rt))
    (inputs_of_data (rt := rt) (pieceData_of (rt := rt) hA) hsq)

/-- **THE DELIVERABLE, in the bridge-interface form**: the same, with the last input given as an
inhabitant of the delivered structure `Work.PieceHomology.Bridge`. -/
def finalInputs_of_bridge [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (B : Work.PieceHomology.Bridge (rt := rt) (pieceData_of (rt := rt) hA)) :
    Work.Final.FinalInputs :=
  Work.HomologyIso.finalInputs (remaining (rt := rt))
    (inputs_of_bridge (rt := rt) (pieceData_of (rt := rt) hA) B)

/-- **The challenge theorem from the two named inputs.**

This is the statement of `Challenge.lean`, proved from `Work.FinalWire.finalInputs_of`; the only
hypotheses are the not-yet-delivered exports `hA` and the bridge square. -/
theorem aspherical_integer_homology_four_sphere_of [T : TorusStandard rt]
    [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere (D := finalInputs_of (rt := rt) hA hsq)

/-- The same, from the bridge interface. -/
theorem aspherical_integer_homology_four_sphere_of_bridge [T : TorusStandard rt]
    [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (B : Work.PieceHomology.Bridge (rt := rt) (pieceData_of (rt := rt) hA)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere (D := finalInputs_of_bridge (rt := rt) hA B)

/-- **`Work.HomologyIso.CuspInputs` from `eA` and the bridge square** — the per-cusp form of the
same data, in the vocabulary of the areas `HomologyIso`/`PieceHomology`.  With it the wiring is
literally `Work.HomologyIso.finalInputs_of_cusps (remaining) (cuspInputs_of hA hsq)`
(`Work.FinalWire.finalInputs_of_cusps` below), the delivered per-cusp assembly of the challenge. -/
def cuspInputs_of [T : TorusStandard rt] (hA : EA rt)
    (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    Work.HomologyIso.CuspInputs (rt := rt) where
  toCuspData := cuspData_of (rt := rt) hA
  hsq := hsq

/-- The same wiring as `Work.FinalWire.finalInputs_of`, through the delivered per-cusp assembler
`Work.HomologyIso.finalInputs_of_cusps`. -/
def finalInputs_of_cusps [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    Work.Final.FinalInputs :=
  Work.HomologyIso.finalInputs_of_cusps (remaining (rt := rt)) (cuspInputs_of (rt := rt) hA hsq)

/-- The two spellings of the wiring are the same term (definitional). -/
theorem finalInputs_of_cusps_eq [T : TorusStandard rt]
    [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    finalInputs_of_cusps (rt := rt) hA hsq = finalInputs_of (rt := rt) hA hsq := rfl

/-! ## §6  The fields of the assembled `FinalInputs` (definitional) -/

/-- The `L` field is the Mayer–Vietoris sequence of the area `HomologyIso`
(`= Work.Final.FinalInputs.mhatLES`). -/
theorem finalInputs_of_L [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    (finalInputs_of (rt := rt) hA hsq).L = Work.HomologyIso.mhatLES (rt := rt) := rfl

/-- The `eM` field is `Work.HomologyIso.eM`. -/
theorem finalInputs_of_eM [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) (k : ℤ) :
    (finalInputs_of (rt := rt) hA hsq).eM k
      = Work.HomologyIso.eM (rt := rt) (pieceData_of (rt := rt) hA) k := rfl

/-- The `eN` field is `Work.HomologyIso.eN`. -/
theorem finalInputs_of_eN [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) (k : ℤ) :
    (finalInputs_of (rt := rt) hA hsq).eN k
      = Work.HomologyIso.eN (rt := rt) (pieceData_of (rt := rt) hA) k := rfl

/-- The `hsq` field is `Work.HomologyIso.hsq`, i.e. the input square. -/
theorem finalInputs_of_hsq [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) (k : ℤ) :
    (finalInputs_of (rt := rt) hA hsq).hsq k
      = Work.HomologyIso.hsq (rt := rt)
          (inputs_of_data (rt := rt) (pieceData_of (rt := rt) hA) hsq) k :=
  rfl

/-- The `hX` field is `Work.HomologyIso.mhatLES_hX`. -/
theorem finalInputs_of_hX [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) (k : ℕ) :
    (finalInputs_of (rt := rt) hA hsq).hX k = Work.HomologyIso.mhatLES_hX (rt := rt) k := rfl

/-- The `rt` field is the ambient instance (so `M̂` of the assembly is `rt.Mhat`). -/
theorem finalInputs_of_rt [T : TorusStandard rt] [C : Work.CurvModels.ModelCurvature rt.models]
    (hA : EA rt) (hsq : SquareOf (rt := rt) (pieceData_of (rt := rt) hA)) :
    (finalInputs_of (rt := rt) hA hsq).rt = rt := rfl

end

end Work.FinalWire
