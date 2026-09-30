/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.Orbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the chart/class dictionary, and §1.4(f)

The `Γ`-stable affine cover needs one chart whose range contains the whole `Γ`-orbit of a point
`x` of `G'` (`Work.JacFinal.Inputs.horbit`).  This file proves the *dictionary* between the
ranges of the chart maps and the chart datum of the chart point (`Work.GroupChunk.Input.InChart`),
in the direction that matters, and derives `horbit` from the class-level covering statement.

The key point (as in §1.4(f) of `NOTES_LEAD_jacobian_final.md`) is that a class in the chart `i`
is represented by a point of `V`, a point of `V` factors through `V`, and two chart points have
the same image in `G'` exactly when their classes agree (`Work.GroupChunk.Glued.eq_iff_class`,
used through `Glued.cls_chart` and `Glued.cls_injective`).  No base-change bookkeeping is
needed here: both the class of a point of `G'` and the representing point of `V` are taken over
the *residue field of the point*, so the two sides of `cls_chart` live over the same field.

What is *not* proved here — and cannot be, from the interfaces on disk — is that the whole
`Γ`-orbit of `x` admits a single chart index.  That is COV′ at the level of `G'`; it needs the
`Γ`-action on the index set of the charts, which area `CH`'s `GalCharts` provides (`act`,
`E_act`, `orbit_cov`) but which the interfaces `GroupChunk.Input`, `Charts` and `ChartDatum`
*all* discard (no field of any of them mentions the Galois group).  See `NOTES.md` §2.2 (G2).
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

variable {k : Type u} [Field k] {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}

namespace Inputs

variable (d : Inputs C P0)

/-- **The chart/class dictionary.**  If the class of a point `x` of `G'` is represented in the
chart `i` (i.e. `x`'s class is `InChart i`), then `x` lies in the range of the chart map
`chart i`.  This is the provable half of §1.4(f). -/
theorem mem_chartRange_of_inChart (x : (d.toChunk.G).left) (i : d.chart.Idx)
    (h : d.chart.InChart i
      (d.exports.glued.cls (Work.GCBasics.resPt d.toChunk.G x))) :
    x ∈ chartRange d i := by
  obtain ⟨y, hy, hc⟩ := h
  obtain ⟨q, hq, -⟩ := Work.GCBasics.FPt.factor_of_landsIn (K := d.k') d.chart.V y hy
  have hcls : d.exports.glued.cls (q ≫ d.exports.glued.chart i) =
      d.exports.glued.cls (Work.GCBasics.resPt d.toChunk.G x) := by
    rw [d.exports.glued.cls_chart i q, hq, hc]
  have heq : q ≫ d.exports.glued.chart i = Work.GCBasics.resPt d.toChunk.G x :=
    d.exports.glued.cls_injective hcls
  haveI : IsOpenImmersion (d.exports.glued.chart i).left :=
    d.exports.glued.isOpenImmersion i
  rw [chartRange, Scheme.Hom.mem_opensRange]
  refine ⟨q.left (IsLocalRing.closedPoint (Work.GCBasics.resField d.toChunk.G x)), ?_⟩
  have h1 : ((q.left ≫ (d.exports.glued.chart i).left)
      (IsLocalRing.closedPoint (Work.GCBasics.resField d.toChunk.G x))) = x := by
    rw [← Over.comp_left, heq]
    exact Work.GCBasics.resPt_apply d.toChunk.G x _
  exact h1

/-- **COV′ for the `Γ`-orbits of classes implies §1.4(f).**  If a single chart index `i`
represents the class of every point of the `Γ`-orbit of `x` (the form in which area `CH`'s
equivariant covering `GalCharts.orbit_cov` presents COV′ at the level of `G'`), then the whole
orbit of `x` lies in the range of the chart `chart i`. -/
theorem horbit_of_inChart_orbit
    (h : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', d.chart.InChart i
        (d.exports.glued.cls (Work.GCBasics.resPt d.toChunk.G
          ((d.toChunk.galAct σ).hom x)))) :
    ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ chartRange d i := by
  intro x
  obtain ⟨i, hi⟩ := h x
  exact ⟨i, fun σ => mem_chartRange_of_inChart d ((d.toChunk.galAct σ).hom x) i (hi σ)⟩

/-- **The `Γ`-stable affine cover from the class-level covering of area `CH`.** -/
theorem cover_of_inChart_orbit (hV : IsAffineOpen d.chart.V)
    (h : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', d.chart.InChart i
        (d.exports.glued.cls (Work.GCBasics.resPt d.toChunk.G
          ((d.toChunk.galAct σ).hom x)))) :
    Cover d :=
  cover_of_chart_orbit d hV (horbit_of_inChart_orbit d h)

/-- **The assembly from the class-level covering**: the outputs of the areas of the drive, the
chart `V` (affine) and the equivariant covering of `Pic⁰` produce `Work.DescentGeom.Input`
directly, without mentioning the chart ranges of `G'`. -/
theorem nonempty_input_of_inChart_orbit (hV : IsAffineOpen d.chart.V)
    (h : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', d.chart.InChart i
        (d.exports.glued.cls (Work.GCBasics.resPt d.toChunk.G
          ((d.toChunk.galAct σ).hom x)))) :
    Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  nonempty_input d (cover_of_inChart_orbit d hV h)

/-- **The two items of area `CH` that the interface `Work.GroupChunk.Input` does not carry**,
in the exact form in which the assembly consumes them:

* the Brill–Noether chart is affine (`Work.Charts.ChartDatum.isAffineOpen_V` /
  `Work.Charts.BNData.isAffineOpen_V`);
* the *equivariant* covering COV′ at the level of `G'`: one chart index represents the class of
  every point of the `Γ`-orbit of `x` (area `CH`'s `GalCharts.orbit_cov`, transported to the
  chart datum over `k'` and combined with the `Γ`-equivariance `cls (Φ(σ) x) = σ (cls x)` of
  the class map, §1.4(a)–(c)).

By `Work.JacFinal.Inputs.horbit_of_inChart_orbit` the second item *implies* §1.4(f)
(`Work.JacFinal.Inputs.horbit`), and by `Work.JacFinal.Inputs.cover_of_chart_orbit` the two
together give the `Γ`-stable affine cover `Work.JacFinal.Cover`, hence
`Work.DescentGeom.Input` — with no further mathematics. -/
structure CovOrbit (d : Inputs C P0) where
  /-- **(CH)** the Brill–Noether chart of `Sym^g C` is affine -/
  hV : IsAffineOpen d.chart.V
  /-- **(CH, COV′)** the `Γ`-orbit of the class of every point of `G'` lies in one chart -/
  hcov : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
    ∀ σ : Work.Descent.Gal k d.k', d.chart.InChart i
      (d.exports.glued.cls (Work.GCBasics.resPt d.toChunk.G
        ((d.toChunk.galAct σ).hom x)))

/-- **`Work.DescentGeom.Input` from area `CH`'s two items**; this is the final assembly with
*every* step between COV′ and the `Γ`-stable affine cover performed here. -/
theorem nonempty_input_of_covOrbit (h : CovOrbit d) :
    Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  nonempty_input_of_inChart_orbit d h.hV h.hcov

/-- **The §1.4(d)–(f) form of the two items of area `CH`**, i.e. the output that the redone
transport `GalCharts → k'` must produce (the design of
`Submission/Work/NOTES_LEAD_jacobian_gaps2.md`: it takes `(B : Work.Charts.SymBC R k' R')`
exactly as `Charts.GalCharts.toCharts` does, but keeps `act`/`E_act`/`orbit_cov` instead of
discarding them):

* `hV` — the Brill–Noether chart of `Sym^g C_{k'}` is affine
  (`B.β ⁻¹ᵁ d.V` for the base change `d'` of area `CH`'s chart `d`);
* `act` — the `Γ`-action on the index set of the centres, transported from `GalCharts.act`;
* `hmem` — the action permutes the chart ranges.  This is §1.4(e): it follows from the
  chart-translate formula §1.4(a) (`chart i = V.ι ≫ AJSym ≫ transl (a i)⁻¹`), from
  `Inputs.AJSym_galAct_left` (§1.4(c), proved in `Submission/Work/JacFinal/GalSym.lean`) and from
  the fact that `galAct` preserves the group law of `G'` (so that it commutes with the
  translations).  Since §1.4(a) needs a `transl` on the glued group — no field of
  `Work.GroupChunk.Input`/`Work.Universal.Input` mentions one — `hmem` is **not** derivable from
  the interfaces on disk and is stated as data here (see `NOTES.md` §2.2 (G2), §6);
* `horbit` — the equivariant covering §1.4(f), which the redone transport obtains from
  `GalCharts.orbit_cov` and `SymBC` by the same argument as `GalCharts.toCharts`. -/
structure ChartOrbit (d : Inputs C P0) where
  /-- **(CH)** the Brill–Noether chart of `Sym^g C_{k'}` is affine -/
  hV : IsAffineOpen d.chart.V
  /-- **(CH, `GalCharts.act`)** the `Γ`-action on the index set of the centres -/
  act : Work.Descent.Gal k d.k' →* Equiv.Perm d.chart.Idx
  /-- **(CH + §1.4(a),(c),(e))** the `Γ`-action permutes the chart ranges -/
  hmem : ∀ σ i, (d.toChunk.galAct σ⁻¹).hom ⁻¹ᵁ chartRange d (act σ i) = chartRange d i
  /-- **(CH, `GalCharts.orbit_cov`, §1.4(f))** every point of `G'` lies in a full `Γ`-orbit of
  chart ranges -/
  horbit : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
    ∀ σ : Work.Descent.Gal k d.k', x ∈ chartRange d (act σ i)

/-- **The `Γ`-stable affine cover from the §1.4(d)–(f) data of area `CH`**: this is
`Work.JacFinal.Inputs.cover_of_chart_orbit_act` of `Submission/Work/JacFinal/Orbit.lean`, read
through the structure `ChartOrbit`. -/
theorem cover_of_chartOrbit (h : ChartOrbit d) : Cover d :=
  cover_of_chart_orbit_act d h.hV h.act h.hmem h.horbit

/-- **`Work.DescentGeom.Input` from the §1.4(d)–(f) data of area `CH`.**  This is the final
assembly in the language of the redone transport: the only inputs are the outputs of the areas
of the drive (bundled in `d : Inputs C P0`) and the `ChartOrbit` data of area `CH`. -/
theorem nonempty_input_of_chartOrbit (h : ChartOrbit d) :
    Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  nonempty_input d (cover_of_chartOrbit d h)

/-- The `Γ`-stable affine cover from area `CH`'s two items. -/
theorem cover_of_covOrbit (h : CovOrbit d) : Cover d :=
  cover_of_inChart_orbit d h.hV h.hcov

end Inputs

end

end Work.JacFinal
