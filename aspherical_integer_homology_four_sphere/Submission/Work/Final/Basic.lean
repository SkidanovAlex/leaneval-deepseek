/-
# `Final/`: the final assembly of `aspherical_integer_homology_four_sphere`

This is the interface file of the area `Final/`.  It records the **remaining inputs** of the
challenge theorem

```
theorem aspherical_integer_homology_four_sphere :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere
```

in a single class, `Work.Final.FinalInputs`, so that the whole chain

```
Challenge  ⟵  Mhat4 : Closed4Manifold            (SPACE: Work.Space.RTData)
           ⟵  IsAspherical                        (CH + LC + CURV)
           ⟵  IsIntegerHomologySphere             (HMV + Homology)
```

is machine-checked **now**, modulo `FinalInputs`; the fields of `FinalInputs` are exactly the
statements still owed by the areas in flight, each documented with its owner.  See
`NOTES_FINAL.md` for the full report.

## The chain, as implemented

* `Work.Final.Mhat4 [FinalInputs] : Closed4Manifold` — the carrier is `M̂` and all six instance
  fields (`TopologicalSpace`, `T2Space`, `SecondCountableTopology`, `ChartedSpace`, `CompactSpace`,
  `ConnectedSpace`) come from `Work.Space.RTData` by typeclass inference.
* `Work.Final.isAspherical_Mhat4` — the blueprint's

  ```
  CH.aspherical_of_curvLe (hmet := LC.lcConn_compat) (htor := LC.lcConn_torsion)
      (CH.curvLe_all ∘ CURV.curvLe_of_models SPACE.chartGram_is_model)
  ```

  literally: the connection is `Work.LeviCivita.lcConn` (delivered), its metric compatibility and
  torsion freeness are `Work.LeviCivita.lcConn_compat` and `Work.LeviCivita.lcConn_torsion`
  (delivered), and the parametric curvature bound is the field `curvLe`.  The alternative
  constructor `Work.Final.FinalInputs.ofSecNonpos` shows how the pointwise `sec ≤ 0` form produced
  by the curvature bridge is turned into that field by `Work.CartanHadamard.curvLe_all`.
* `Work.Final.isIntegerHomologySphere_Mhat4` — the Mayer–Vietoris computation: it applies
  `Work.HomologyMV.intHomology_of_concrete` and composes with the sphere computation
  `Work.Homology.intHomology_sphere_four`.
* `Work.Final.aspherical_integer_homology_four_sphre` — the two together, in the exact shape of
  `Challenge.lean`.

## Owners of the fields

| field | statement | owner |
|---|---|---|
| `rt` | the assembled space `M̂` (`Work.Space.RTData`) | SPACE (with the `Fold` instantiation, CUSP, data agent) |
| `cov_smooth` | `lcConn` is a smooth covariant derivative | LEVICIVITA (`Work.LeviCivita.lcConn_contMDiff`) |
| `curvLe` | `∀ K > 0, RauchK.CurvLe lcConn K` | CURV Part 2 (`Work.Curvature.curvLe_of_models`) |
| `L` | the Mayer–Vietoris long exact sequence of `M̂ = A ∪ B` | HMV (`Work.Final.coverMVLES`, `Final/Cover.lean`) |
| `eM`, `eN` | `H_*(A∩B)`, `H_*(A) ⊞ H_*(B)` are the free models | DELTAHOMOLOGY + CERTIFICATES (HS2/HS3/G0 + SDR) |
| `hsq` | the Mayer–Vietoris map is the concrete matrix `wConcrete` | DELTAHOMOLOGY + CERTIFICATES (bridge witnesses) |
| `hX` | the `X`-slot is the singular homology of `M̂` | HMV (`coverMVLES` gives it by `rfl` + `smallIso`) |
| `h0` | `H_0(M̂) ≅ ℤ` | derivable from `hX 0` and connectedness of `M̂` |

The metric compatibility and torsion freeness of the connection, which the blueprint's final line
also needs, are **delivered** (`Work.LeviCivita.lcConn_compat`, `Work.LeviCivita.lcConn_torsion`)
and are used directly, so they are not fields.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Space.All
import Submission.Work.CartanHadamard.All
import Submission.Work.HomologyMV.All
import Submission.Work.Homology.All
import Submission.Work.Cohomology.MVSequence
import Submission.Work.LeviCivita.Defs

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
set_option warn.classDefReducibility false

open LeanEval.Topology
open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

open Work.Space

noncomputable section

/-- **The connection of the final chain**: the Levi-Civita connection of `M̂`, in the framework
variable block of the project.  It is `Work.LeviCivita.lcConn`, already delivered by the `LC` area,
specialised to `E = E4`, `I = I4`, `M = M̂`. -/
abbrev mhatCov [rt : Work.Space.RTData] :
    CovariantDerivative Work.Space.I4 Work.Space.E4
      (TangentSpace Work.Space.I4 (M := rt.Mhat)) :=
  Work.LeviCivita.lcConn (I := Work.Space.I4) (M := rt.Mhat)

/-- **The remaining inputs of the final assembly.**

A single `instance : FinalInputs` yields the challenge theorem (see
`Work.Final.aspherical_integer_homology_four_sphere`); every field is a statement owed by one of
the areas of the project, see the module docstring for the table. -/
class FinalInputs where
  /-- **SPACE.**  The assembled Ratcliffe–Tschantz space `M̂`, with its finite atlas of isometric
  chart models.  Owner: area `Space` (with the `Fold` instantiation and the cusp data). -/
  [rt : Work.Space.RTData]
  /-- **LEVICIVITA.**  The connection of `M̂` (the Levi-Civita connection `Work.LeviCivita.lcConn`)
  is smooth.  Owner: `Work.LeviCivita.lcConn_contMDiff`, area `LeviCivita`. -/
  [cov_smooth : CovariantDerivative.ContMDiffCovariantDerivative
    (mhatCov (rt := rt)) ∞]
  /-- **CURVATURE PART 2.**  The curvature bound: `sec ≤ 0`, in the parametric form consumed by the
  Cartan–Hadamard area.  This is the output of the curvature bridge
  `Work.Curvature.curvLe_of_models`: it consumes `Work.Space.RTData.chartGram_is_model` together
  with the pointwise non-positivity of the three metric models
  (`Work.Curvature.secNonposAt_uhs`, `secNonposAt_warped`, `secNonposAt_flat`) and the chart Koszul
  identity `Work.LeviCivita.chartGram_chrB_eq_koszul` of the `LeviCivita` area. -/
  curvLe : ∀ K : ℝ, 0 < K →
    Submission.RauchK.CurvLe (mhatCov (rt := rt)) K
  /-- **HMV.**  The Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B` of
  `Work.Space.Assembly.Aset_sup_Bset`. -/
  L : Work.HomologyMV.MVLES
  /-- **DELTAHOMOLOGY / CERTIFICATES.**  `H_k(A ∩ B)` is the free model `ℤ^{rankM k}`
  (`Work.HomologyMV.ModelM`); the identifications come from the quasi-isomorphisms of the
  `Δ`-complex structures and the Smith-normal-form certificates of `Certificates/`. -/
  eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ L.H (k, 0)
  /-- **DELTAHOMOLOGY / CERTIFICATES.**  `H_k(A) ⊞ H_k(B)` is the free model `ℤ^{rankN k}`. -/
  eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ L.H (k, 1)
  /-- **CERTIFICATES.**  The first Mayer–Vietoris map is the concrete matrix `wConcrete k`, i.e.
  the commuting square with the identifications `eM`, `eN`. -/
  hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom
  /-- **HMV.**  The `X`-slot of the sequence is the singular homology of `M̂`. -/
  hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
    LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)

namespace FinalInputs

/-- The space `M̂` of the final input. -/
abbrev Mhat (D : FinalInputs) : Type _ := D.rt.Mhat

/-- **The smoothness of the connection of the final chain**, in the exact form consumed by the
Cartan–Hadamard area.  (This is the `cov_smooth` field, re-exported with an explicit type so that
typeclass inference finds it without having to invert the projection `FinalInputs.cov_smooth`.) -/
theorem mhatCov_contMDiff [D : FinalInputs] :
    CovariantDerivative.ContMDiffCovariantDerivative (mhatCov (rt := D.rt)) ∞ :=
  D.cov_smooth

/-- **`M̂` is path connected**: it is connected and locally path connected (locally path connected
because it is charted on `E4`). -/
theorem pathConnectedSpace_Mhat [D : FinalInputs] : PathConnectedSpace D.Mhat := by
  haveI : LocallyPathConnectedSpace D.Mhat :=
    ChartedSpace.locallyPathConnectedSpace Work.Space.E4 D.Mhat
  exact PathConnectedSpace.of_locallyPathConnectedSpace

instance instPathConnectedSpaceMhat [D : FinalInputs] : PathConnectedSpace D.Mhat :=
  pathConnectedSpace_Mhat (D := D)

/-- **`H_0(M̂; ℤ) ≅ ℤ`** — from the path connectedness of `M̂` and
`Work.Homology.singHomologyZeroIsoOfPathConnected` (`H_0` of a path connected space is the
coefficient ring). -/
theorem intHomology_zero_Mhat [D : FinalInputs] :
    Nonempty (LeanEval.Topology.intHomology 0 (TopCat.of D.Mhat) ≅ ModuleCat.of ℤ ℤ) :=
  ⟨Work.Homology.singHomologyZeroIsoOfPathConnected Work.Homology.ZMod (TopCat.of D.Mhat)⟩

/-- **The degree-`0` input of the Mayer–Vietoris computation**, derived rather than assumed: the
`(0,2)`-slot is `ℤ`.  It is `hX 0` composed with `intHomology_zero_Mhat`. -/
theorem h0_of_hX [D : FinalInputs] :
    Nonempty (D.L.H (0, 2) ≅ Work.HomologyMV.Sol 0) :=
  ⟨(D.hX 0) ≪≫ (intHomology_zero_Mhat (D := D)).some⟩

/-- **The curvature bridge in the pointwise form.**  If the curvature input is given as `sec ≤ 0`
pointwise — the form in which the curvature bridge `Work.Curvature.curvLe_of_models` delivers it,
from the chart models of `Work.Space.RTData` — then `Work.CartanHadamard.curvLe_all` turns it into
the `curvLe` field.

This is the composition `CH.curvLe_all ∘ (curvature bridge)` of the blueprint's final line. -/
def ofSecNonpos [J : FinalInputs]
    (hsec : ∀ x : J.Mhat, ∀ u v : TangentSpace Work.Space.I4 x,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
        inner ℝ (Submission.CurvatureVec.curvVec (mhatCov (rt := J.rt)) x u v v) u ≤ 0) :
    FinalInputs where
  rt := J.rt
  cov_smooth := J.cov_smooth
  curvLe := by
    haveI := J.mhatCov_contMDiff
    exact Work.CartanHadamard.curvLe_all (cov := mhatCov (rt := J.rt)) hsec
  L := J.L
  eM := J.eM
  eN := J.eN
  hsq := J.hsq
  hX := J.hX

end FinalInputs

end

end Work.Final
