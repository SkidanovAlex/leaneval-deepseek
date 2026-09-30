/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.ChartDict
import Submission.Work.DescentGeom.Main
import Submission.Work.RiemannRoch.ExportCB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the challenge's `jacPkgExists`

This file contains the final wiring: from the assembly `Work.JacFinal.Inputs.nonempty_input` —
with the `Γ`-stable affine cover *proved* in `Submission/Work/JacFinal/Orbit.lean` — and the
geometric half of the descent (`Work.DescentGeom.jacPkgExists_of_inputs`) we obtain

`Work.JacFinal.jacPkgExists : ∀ P0, Nonempty (Work.Packaging.JacPkg C P0)`

for a curve `C` over a field `k` with the hypotheses of the challenge (plus the three fields of
`Work.CurveBasics.Curve` that are not in Mathlib: geometrically reduced, Krull dimension of the
stalks at most one, nontrivial).

## The wiring of `Submission.lean`

`Submission.lean` (which cannot be edited by this area) has exactly one `sorry`, in

```lean
theorem jacPkgExists (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Work.Packaging.JacPkg C P0) :=
  fun _ => sorry
```

It is replaced by the one line

```lean
  Work.JacFinal.jacPkgExists C hred hdim hnt h
```

where

```lean
  h : ∀ P0, Nonempty (Work.JacFinal.Data (CurveBasics.Curve.ofOver C hred hdim hnt) P0)
```

is the datum assembled per base point from the live areas (see `NOTES.md` of this directory);
the three extra arguments `hred`, `hdim`, `hnt` are the missing fields of
`Work.CurveBasics.Curve` (they are also what `Work.DescentGeom.jacPkgExists_of_inputs` asks
for).
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

namespace Work.JacFinal

noncomputable section

variable {k : Type u} [Field k]

/-- **The inputs of the final assembly, bundled.**  For every `k`-point `P0` of the curve:

* `inputs` — the outputs of the areas of the drive over a finite Galois extension `k'/k`
  (`Work.JacFinal.Inputs`: the chart datum of areas `SY`/`RR`/`CH`/`DM` and the group chunk,
  quotient property and key lemma of areas `GC`/`SY`/`KL`);
* `hV` — the Brill–Noether chart of `Sym^g C` over `k'` is affine (area `CH`,
  `Work.Charts.ChartDatum.isAffineOpen_V`; it is not a field of `Work.GroupChunk.Input`);
* `horbit` — every point of `G'` has one chart whose range contains its whole `Γ`-orbit
  (§1.4(f) of the lead's notes: the chart form of COV′).

The `Γ`-stable affine cover `Work.JacFinal.Cover` — the last field of `Work.DescentGeom.Input`
— is a *theorem* about these two: `Work.JacFinal.Inputs.cover_of_chart_orbit` (in
`Submission/Work/JacFinal/Orbit.lean`). -/
structure Data (C : CurveBasics.Curve k) (P0 : 𝟙_ (Sch k) ⟶ C.toOver) where
  /-- the outputs of the areas over the finite Galois extension -/
  inputs : Inputs C P0
  /-- **(CH)** the Brill–Noether chart of `Sym^g C` is affine -/
  hV : IsAffineOpen inputs.chart.V
  /-- **(CH + §1.4(f))** the Γ-orbit of every point of `G'` lies in one chart range -/
  horbit : ∀ x : inputs.toChunk.G.left, ∃ i : inputs.chart.Idx,
    ∀ σ : Work.Descent.Gal k inputs.k',
      (inputs.toChunk.galAct σ).hom x ∈ inputs.chartRange i

variable {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}


/-- **`Data` from area `CH`'s two items** (`Work.JacFinal.Inputs.CovOrbit`): the Brill–Noether chart is
affine, and the `Γ`-orbit of the class of every point of `G'` lies in one chart.  The step from
the second item to §1.4(f) (`Work.JacFinal.Inputs.horbit`) is
`Work.JacFinal.Inputs.horbit_of_inChart_orbit`, proved in `Submission/Work/JacFinal/
ChartDict.lean`; no further mathematics is assumed. -/
def Data.of_covOrbit (d : Inputs C P0) (h : Inputs.CovOrbit d) : Data C P0 where
  inputs := d
  hV := h.hV
  horbit := Inputs.horbit_of_inChart_orbit d h.hcov

/-- **The `Γ`-stable affine cover of the bundled inputs**, proved by
`Work.JacFinal.Inputs.cover_of_chart_orbit`. -/
theorem dataCover (d : Data C P0) : Cover d.inputs :=
  Inputs.cover_of_chart_orbit d.inputs d.hV d.horbit

/-- **The final assembly, as a function of `P0`.**  From the bundled outputs of the areas — the
cover now being a theorem — we produce the chart datum of area `DescentGeom` for every `k`-point
of `C`. -/
theorem jacFinal_inputs (C : CurveBasics.Curve k)
    (h : ∀ P0 : 𝟙_ (Sch k) ⟶ C.toOver, Nonempty (Data C P0)) :
    ∀ P0 : 𝟙_ (Sch k) ⟶ C.toOver, Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  fun P0 => (h P0).map fun d => (nonempty_input d.inputs (dataCover d)).some

/-- **The Riemann–Roch genus of the curve of the challenge**, in the normalisation of area
`RR` (`Work.RiemannRoch.Curve.genus`).  The case `gC = 0` is the one in which the interface
`Work.GroupChunk.Input` — whose field `curveAdd_divOf` uses the `ℕ`-multiple `(g - 1) •` — cannot
be inhabited (`Work.JacFinal.genus_zero_no_input`), so that the final theorem has to be split. -/
abbrev gC (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z))
    (hnt : Nontrivial C.left) : ℕ :=
  RiemannRoch.Curve.genus (CurveBasics.Curve.ofOver C hred hdim hnt)

/-- **The `g ≥ 1` half of the wiring.**  For a curve over `k` given by the hypotheses of the
challenge (and the three fields of `Work.CurveBasics.Curve` which are not yet in Mathlib), the
outputs of the areas of the drive produce the Jacobian package of `C` at every `k`-point.

This is unconditional in the genus; the caller supplies the `Data` for every base point (which is
where the interface `Work.GroupChunk.Input` enters, hence where `g ≠ 0` is needed). -/
theorem jacPkgExists_of_data (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left)
    (h : ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C,
      Nonempty (Data (CurveBasics.Curve.ofOver C hred hdim hnt) P0)) :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Packaging.JacPkg C P0) :=
  Work.DescentGeom.jacPkgExists_of_inputs C hred hdim hnt
    (jacFinal_inputs (CurveBasics.Curve.ofOver C hred hdim hnt) h)

/-- **The wiring of the challenge's `jacPkgExists`, split at genus zero** (the design of
`Submission/Work/NOTES_LEAD_jacobian_gaps2.md` §3).

* `hpos` is the `g ≥ 1` branch: the `Data` of the areas of the drive, for every base point
  (`g` here is `Work.RiemannRoch.Curve.genus`, which the builder of `Inputs.chart` sets to
  `genus (C.baseChange k')` and which equals `gC` by `RiemannRoch.Curve.genus_eq
  (Curve.bcSquare C k')`; `gC ≠ 0` then gives `NeZero g`, hence `1 ≤ g`, which is what the
  concrete `curveAdd` of area `SY` and the field `curveAdd_divOf` need).
* `hzero` is the genus-zero branch, `Work.GenusZero.jacPkg_of_genus_zero` of the area
  `GenusZero`: there the Jacobian is the trivial group scheme.

Because `gC` does not depend on the base point, the split is taken outside `fun P0`, so both
branches deliver `∀ P0` at once. -/
theorem jacPkgExists (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom] (hred : GeometricallyReduced C.hom)
    (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left)
    (hpos : gC C hred hdim hnt ≠ 0 → ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C,
      Nonempty (Data (CurveBasics.Curve.ofOver C hred hdim hnt) P0))
    (hzero : gC C hred hdim hnt = 0 → ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C,
      Nonempty (Packaging.JacPkg C P0)) :
    ∀ P0 : 𝟙_ (Over (Spec (.of k))) ⟶ C, Nonempty (Packaging.JacPkg C P0) := by
  by_cases hg : gC C hred hdim hnt = 0
  · exact hzero hg
  · exact jacPkgExists_of_data C hred hdim hnt (hpos hg)

end

end Work.JacFinal
