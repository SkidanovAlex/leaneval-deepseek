/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the `Γ`-stable affine cover is a theorem

`Work.DescentGeom.Input.hcover` asks for a `Γ`-stable affine open around every point of the
group chunk `G'`.  This file *proves* it from the two geometric statements of §1.4 of
`NOTES_LEAD_jacobian_final.md`:

* `IsAffineOpen V` — the Brill–Noether chart of `Sym^g C` (area `CH`,
  `Work.Charts.ChartDatum.isAffineOpen_V`; it is *not* a field of `Work.GroupChunk.Input`);
* the orbit-in-one-chart statement `∀ x, ∃ i, ∀ σ, galAct σ x ∈ range (chart i)`
  (§1.4(f): COV′ plus the fact that `galAct` permutes the chart ranges).

The construction is the one of §1.4(g): for `W` an affine open of `G'` containing the whole
`Γ`-orbit of `x`, the open

`Ω := ⨅ σ : Γ, (galAct σ)⁻¹ᵁ W`

is affine (finite intersection of affines in the separated `G'`), contains `x`, and is
`Γ`-stable.  The stability is purely formal — it holds for *every* `W` — and only uses the
action laws `galAct_mul`, `galAct_one` of the constructed semilinear action:

`y ∈ (galAct τ)⁻¹ᵁ Ω ↔ (galAct τ) y ∈ Ω ↔ ∀σ, (galAct σ)((galAct τ) y) ∈ W
   ↔ ∀σ, (galAct (σ τ)) y ∈ W ↔ ∀ρ, (galAct ρ) y ∈ W ↔ y ∈ Ω`.

Hence the cover exists exactly when every `Γ`-orbit of a point of `G'` lies in an affine open
(`Work.JacFinal.Inputs.cover_of_affine_orbit`), and that is what the chart computation
`Work.JacFinal.Inputs.cover_of_chart_orbit` supplies.
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

/-- The Galois group of the finite extension is finite (area `DS`: the index set of the
descent is finite). -/
instance instFiniteGal : Finite (Work.Descent.Gal k d.k') := by
  haveI : Fintype (Work.Descent.Gal k d.k') := AlgEquiv.fintype k d.k'
  infer_instance

/-- The Galois group is nonempty. -/
instance instNonemptyGal : Nonempty (Work.Descent.Gal k d.k') := ⟨1⟩

/-- **The range of the `i`-th chart** `chart i : V ⟶ G'`, an open subscheme of `G'`.  It is
affine as soon as the chart `V` of `Sym^g C` is (`Inputs.cover_of_chart_orbit`). -/
abbrev chartRange (i : d.chart.Idx) : (d.toChunk.G).left.Opens :=
  Scheme.Hom.opensRange (d.exports.glued.chart i).left
    (H := d.exports.glued.isOpenImmersion i)

/-- Membership in `⨅ σ, (galAct σ)⁻¹ᵁ W`: a point lies in the intersection exactly when its
whole `Γ`-orbit lies in `W`. -/
theorem mem_iInf_preimage (W : (d.toChunk.G).left.Opens)
    (y : (d.toChunk.G).left) :
    y ∈ (⨅ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom ⁻¹ᵁ W) ↔
      ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom y ∈ W := by
  change y ∈ (↑(⨅ σ : Work.Descent.Gal k d.k',
      (d.toChunk.galAct σ).hom ⁻¹ᵁ W) : Set ((d.toChunk.G).left)) ↔
    ∀ σ : Work.Descent.Gal k d.k',
      (d.toChunk.galAct σ).hom y ∈ (↑W : Set ((d.toChunk.G).left))
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact forall_congr' fun σ =>
    Scheme.Hom.mem_preimage (f := (d.toChunk.galAct σ).hom) (x := y) (U := W)

/-- The action law, read at the level of points. -/
theorem galAct_mul_apply (τ σ : Work.Descent.Gal k d.k')
    (y : (d.toChunk.G).left) :
    (d.toChunk.galAct σ).hom ((d.toChunk.galAct τ).hom y) =
      (d.toChunk.galAct (τ * σ)).hom y := by
  rw [d.toChunk.galAct_mul, Iso.trans_hom]
  rfl

/-- `galAct σ⁻¹` is a left inverse of `galAct σ` on points. -/
theorem galAct_inv_apply (σ : Work.Descent.Gal k d.k')
    (y : (d.toChunk.G).left) :
    (d.toChunk.galAct σ⁻¹).hom ((d.toChunk.galAct σ).hom y) = y := by
  have h : (d.toChunk.galAct σ).hom ≫ (d.toChunk.galAct σ⁻¹).hom = 𝟙 _ := by
    rw [← Iso.trans_hom, ← d.toChunk.galAct_mul, mul_inv_cancel, d.toChunk.galAct_one]
    rfl
  show ((d.toChunk.galAct σ).hom ≫ (d.toChunk.galAct σ⁻¹).hom) y = y
  rw [h]
  rfl

/-- The reindexing identity used for the `Γ`-stability: applying `galAct τ` and then
`galAct (τ⁻¹ * ρ)` is applying `galAct ρ`. -/
theorem galAct_mul_apply_inv (τ ρ : Work.Descent.Gal k d.k')
    (y : (d.toChunk.G).left) :
    (d.toChunk.galAct (τ⁻¹ * ρ)).hom ((d.toChunk.galAct τ).hom y) =
      (d.toChunk.galAct ρ).hom y := by
  rw [d.toChunk.galAct_mul, Iso.trans_hom]
  show (d.toChunk.galAct ρ).hom
      ((d.toChunk.galAct τ⁻¹).hom ((d.toChunk.galAct τ).hom y)) =
    (d.toChunk.galAct ρ).hom y
  rw [galAct_inv_apply]

/-- **`Ω` is `Γ`-stable, for every open `W`.**  This is the formal heart of §1.4(g). -/
theorem galAct_preimage_iInf (τ : Work.Descent.Gal k d.k')
    (W : (d.toChunk.G).left.Opens) :
    (d.toChunk.galAct τ).hom ⁻¹ᵁ
        (⨅ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom ⁻¹ᵁ W) =
      ⨅ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom ⁻¹ᵁ W := by
  refine le_antisymm ?_ ?_
  · rw [SetLike.le_def]
    intro y hy
    rw [Scheme.Hom.mem_preimage, mem_iInf_preimage d W] at hy
    rw [mem_iInf_preimage d W]
    intro ρ
    have h1 := hy (τ⁻¹ * ρ)
    rwa [galAct_mul_apply_inv d τ ρ y] at h1
  · rw [SetLike.le_def]
    intro y hy
    rw [mem_iInf_preimage d W] at hy
    rw [Scheme.Hom.mem_preimage, mem_iInf_preimage d W]
    intro σ
    rw [galAct_mul_apply d τ σ y]
    exact hy (τ * σ)

/-- The diagonal of `G'` (over the terminal scheme) is affine, because `G'` is separated over
`k'` and `Spec k'` is affine. -/
theorem isAffineHom_diagonal_terminal :
    IsAffineHom (pullback.diagonal (terminal.from ((d.toChunk.G).left))) := by
  haveI : IsSeparated (d.toChunk.G).hom := d.exports.isSeparated_G
  have hfac : terminal.from ((d.toChunk.G).left) =
      (d.toChunk.G).hom ≫ terminal.from (Spec (CommRingCat.of d.k')) :=
    (terminal.comp_from (d.toChunk.G).hom).symm
  haveI hsep : IsSeparated (terminal.from ((d.toChunk.G).left)) := by
    rw [hfac]
    infer_instance
  exact inferInstance

/-- **The cover, from an affine open containing every `Γ`-orbit.**  This is the exact
mathematical content of `hcover`: the `Γ`-stable affine cover of `G'` exists if and only if
every `Γ`-orbit of a point of `G'` is contained in an affine open (the converse is immediate,
`Ω` itself being such an open). -/
theorem cover_of_affine_orbit
    (h : ∀ x : (d.toChunk.G).left, ∃ W : (d.toChunk.G).left.Opens,
      IsAffineOpen W ∧ ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ W) :
    Cover d := by
  refine ⟨fun x => ?_⟩
  obtain ⟨W, hWaff, hWmem⟩ := h x
  refine ⟨⨅ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom ⁻¹ᵁ W, ?_, ?_, ?_⟩
  · haveI := isAffineHom_diagonal_terminal d
    exact IsAffineOpen.iInf
      (U := fun σ : Work.Descent.Gal k d.k' => (d.toChunk.galAct σ).hom ⁻¹ᵁ W)
      fun σ => hWaff.preimage_of_isIso _
  · intro τ
    exact galAct_preimage_iInf d τ W
  · rw [mem_iInf_preimage d W]
    exact hWmem

/-- **The cover, from the Brill–Noether chart.**  If the chart `V ⊆ Sym^g C` is affine (area
`CH`, `Work.Charts.ChartDatum.isAffineOpen_V`, which the interface `Work.GroupChunk.Input`
does not carry) and every point of `G'` has *one* chart whose range contains its whole
`Γ`-orbit (§1.4(f), the chart form of COV′), then `hcover` holds. -/
theorem cover_of_chart_orbit (hV : IsAffineOpen d.chart.V)
    (horbit : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ chartRange d i) :
    Cover d := by
  refine cover_of_affine_orbit d fun x => ?_
  obtain ⟨i, hi⟩ := horbit x
  refine ⟨chartRange d i, ?_, hi⟩
  haveI : IsAffine (Work.GCBasics.Opens.toOver d.chart.V).left := hV
  haveI : IsOpenImmersion (d.exports.glued.chart i).left :=
    d.exports.glued.isOpenImmersion i
  exact isAffineOpen_opensRange (d.exports.glued.chart i).left

/-- **The assembly with the cover proved**: the outputs of the areas of the drive over `k'`,
together with the chart form of the covering statement, produce the chart datum of area
`DescentGeom`. -/
theorem nonempty_input_of_chart_orbit (hV : IsAffineOpen d.chart.V)
    (horbit : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ chartRange d i) :
    Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  nonempty_input d (cover_of_chart_orbit d hV horbit)

/-- **The assembly with the cover proved**, in the form that mentions `G'` only through the
affine-orbit condition. -/
theorem nonempty_input_of_affine_orbit
    (h : ∀ x : (d.toChunk.G).left, ∃ W : (d.toChunk.G).left.Opens,
      IsAffineOpen W ∧ ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ W) :
    Nonempty (Work.DescentGeom.Input C.toOver P0) :=
  nonempty_input d (cover_of_affine_orbit d h)


/-- **The charts cover `G'`** (the `factor` field of area `GC`'s `Glued`): every point of the
group chunk lies in the range of one of the chart maps.  This is the first half of §1.4(f); the
second half — that the whole `Γ`-orbit of a point lies in *one* chart range — is COV′ at the
level of `G'` and is taken as the hypothesis `horbit` of `cover_of_chart_orbit`. -/
theorem exists_chartRange (x : (d.toChunk.G).left) :
    ∃ i : d.chart.Idx, x ∈ chartRange d i := by
  obtain ⟨i, q, hq⟩ :=
    d.exports.glued.factor (Work.GCBasics.resPt d.exports.glued.G x)
  refine ⟨i, ?_⟩
  haveI : IsOpenImmersion (d.exports.glued.chart i).left :=
    d.exports.glued.isOpenImmersion i
  rw [chartRange, Scheme.Hom.mem_opensRange]
  refine ⟨q.left (IsLocalRing.closedPoint (Work.GCBasics.resField d.exports.glued.G x)), ?_⟩
  have h2 : ((q.left ≫ (d.exports.glued.chart i).left)
      (IsLocalRing.closedPoint (Work.GCBasics.resField d.exports.glued.G x))) = x := by
    rw [← Over.comp_left, hq]
    exact Work.GCBasics.resPt_apply d.exports.glued.G x _
  exact h2

/-- **The cover, in the chart-orbit form of the lead's §1.4(e)+(f).**  If `Γ` permutes the chart
ranges through a permutation `act` of the index set (`hmem`, §1.4(e)) and every point lies in
every chart of a full `Γ`-orbit of charts (`horbit`, §1.4(f) in the form supplied by COV′ /
`GalCharts.orbit_cov`), then the `Γ`-stable affine cover exists. -/
theorem cover_of_chart_orbit_act (hV : IsAffineOpen d.chart.V)
    (act : Work.Descent.Gal k d.k' →* Equiv.Perm d.chart.Idx)
    (hmem : ∀ (σ : Work.Descent.Gal k d.k') (i : d.chart.Idx),
      (d.toChunk.galAct σ⁻¹).hom ⁻¹ᵁ chartRange d (act σ i) = chartRange d i)
    (horbit : ∀ x : (d.toChunk.G).left, ∃ i : d.chart.Idx,
      ∀ σ : Work.Descent.Gal k d.k', x ∈ chartRange d (act σ i)) :
    Cover d := by
  refine cover_of_chart_orbit d hV fun x => ?_
  obtain ⟨i, hi⟩ := horbit x
  refine ⟨i, fun σ => ?_⟩
  rw [← hmem σ i, Scheme.Hom.mem_preimage, galAct_inv_apply d σ x]
  exact hi σ

/-- The range of a chart is affine, provided the chart `V ⊆ Sym^g C` of `Sym^g C` is (area
`CH`): the range of an open immersion out of an affine scheme is affine. -/
theorem isAffineOpen_chartRange (hV : IsAffineOpen d.chart.V) (i : d.chart.Idx) :
    IsAffineOpen (chartRange d i) := by
  haveI : IsAffine (Work.GCBasics.Opens.toOver d.chart.V).left := hV
  haveI : IsOpenImmersion (d.exports.glued.chart i).left :=
    d.exports.glued.isOpenImmersion i
  exact isAffineOpen_opensRange (d.exports.glued.chart i).left

/-- The converse of `cover_of_affine_orbit`: a `Γ`-stable affine open containing `x` shows that
the `Γ`-orbit of `x` is contained in an affine open. -/
theorem affineOrbit_of_cover (hc : Cover d) :
    ∀ x : (d.toChunk.G).left, ∃ W : (d.toChunk.G).left.Opens,
      IsAffineOpen W ∧ ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ W := by
  intro x
  obtain ⟨Ω, haff, hstab, hx⟩ := hc.hcover x
  refine ⟨Ω, haff, fun σ => ?_⟩
  have hmem := (Scheme.Hom.mem_preimage (f := (d.toChunk.galAct σ).hom)
    (x := x) (U := Ω)).mp
  rw [hstab σ] at hmem
  exact hmem hx

/-- **`hcover` is exactly the statement that every `Γ`-orbit of a point of `G'` is contained in
an affine open.**  This is the precise form of the remaining gap of the drive (§1.4(f)/(g) of
`NOTES_LEAD_jacobian_final.md`). -/
theorem cover_iff_affineOrbit :
    Nonempty (Cover d) ↔
      (∀ x : (d.toChunk.G).left, ∃ W : (d.toChunk.G).left.Opens,
        IsAffineOpen W ∧ ∀ σ : Work.Descent.Gal k d.k', (d.toChunk.galAct σ).hom x ∈ W) :=
  ⟨fun ⟨hc⟩ => affineOrbit_of_cover d hc, fun h => ⟨cover_of_affine_orbit d h⟩⟩

end Inputs

end

end Work.JacFinal
