import Submission.Work.PTGeometric.LevelOrientation
import Submission.Work.ThomBordism.Interface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the orientation datum with the **chart structure chosen by the producer**

`Work.PTGeometric.LevelOrientationDatum` states the orientation datum of the level set on the
**canonical model** `Work.PTGeometric.levelModel W hWcl L` (`Lvl.Setup`): its chart structure is the
submersion normal form of the local defining functions `L.g x`, extracted from the *existential*
`Manifold.IsSubmersionAt` by `Classical.choose` (`Lvl.Setup.normForm`).

That extraction is **opaque**: `SubmersionAtProp` constrains only the *first* component of the linear
equivalence `E ≃L E'' × F` (`codChart ∘ f ∘ domChart⁻¹ = Prod.fst ∘ equiv`), so the second component
— which is what the level chart of `Lvl/Chart.lean` is built from — is an *arbitrary* witness, and the
orientation that the chart induces on the level set is therefore not controlled by any lemma.  A
statement whose content is "the level set carries an orientation family *in this chart structure*"
is consequently not provable (a proof could only use `Classical.choose_spec`, hence would have to
hold for every witness, and witnesses with the opposite second component exist).  The same obstruction
is recorded from the analytic side in `NOTE_G5_REPAIR.md`.

The repair carried out here: **state the datum on the space `↥W` with the chart structure supplied by
the producer.**  The datum still exhibits the level set `W`, its level data `L` and the identification
`e` of its boundary part with the pieces — so the geometric content is unchanged — but the chart
structure is now data, and a producer is free to build one whose orientation it controls (for example
by correcting the charts of the canonical model with a computable reflection, see
`NOTE_G5_REPAIR.md`).

The two directions are proved:

* `Work.PTGeometric.levelOrientationDatumFree_of_datum` — the *old* datum (on the canonical model)
  implies the new one (take the canonical chart structure).  Hence the new datum is **weaker** and
  nothing that was proved from the old one is lost;
* `Work.PTGeometric.exists_nullBordismFamily_of_levelOrientationModelData` — the new datum implies
  the endgame's conclusion `Nonempty (NullBordismFamily ι Fam)` directly, with no reference to the
  canonical model at all.

## Main definitions

* `Work.PTGeometric.LevelOrientationModelData`
* `Work.PTGeometric.LevelOrientationDatumFree`
* `Work.PTGeometric.AmbientOrientationDataFree`

## Main results

* `Work.PTGeometric.exists_nullBordismFamily_of_levelOrientationModelData`
* `Work.PTGeometric.exists_nullBordismFamily_of_ambientOrientationDataFree`
* `Work.PTGeometric.levelOrientationDatumFree_of_datum`
* `Work.PTGeometric.ambientOrientationDataFree_of_datum`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

/-- **The orientation datum of a level set, with the chart structure supplied by the producer.**

`W ⊆ M` is a closed subset of a compact smooth `(9+k)`-manifold with boundary carrying local
level-set data `L` (so that it *is* a `9`-manifold with boundary `W ∩ ∂M`, by the preimage theorem),
and `e` identifies that boundary part with the disjoint union of the pieces of the family.

The structure supplies:

* a `C^∞` `9`-manifold-with-boundary structure on the space `↥W` (the *subtype* topology — the same
  space as in `Work.PTGeometric.levelModel`; only the chart structure is data now), with
  `bdry_eq` pinning its boundary to the part `W ∩ ∂M` of the source's boundary;
* a relative fundamental class `w` of `(↥W, ∂)` which is a local generator at every interior point
  (G5-(i): this is exactly ORIENT's relative fundamental class, and it *is* an orientation of the
  level set — the family `x ↦ locClass w x` is an orientation family by
  `Work.Orient.isOrientFamily_locClass` / `locClass_eq_relClass`), and
* whose boundary is the **sum** of the pieces' fundamental classes under the identification
  `bdryPreimage.trans e` (G5-(ii), the sign: ORIENT's own boundary formula
  `Work.Orient.BoundaryOrientationConvention` is deliberately sign-blind, and the sign is the
  geometric statement computed by TUBULAR's local degree).

No orientation family is a field: it would be redundant with `w_fund` (see the remark above) and
would make the datum harder to satisfy than the geometry actually is. -/
structure LevelOrientationModelData (k : ℕ) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    {ι : Type} [Fintype ι] (Fam : ι → Man8)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)) where
  /-- the chart structure of the model (chosen by the producer) -/
  [chartedSpace : ChartedSpace (EuclideanHalfSpace 9) ↥W]
  /-- it is a `C^∞` manifold -/
  [isManifold : IsManifold (𝓡∂ 9) ∞ ↥W]
  /-- it is compact (the topology is the subtype topology of the compact `M`) -/
  [compactSpace : CompactSpace ↥W]
  /-- it is Hausdorff -/
  [t2Space : T2Space ↥W]
  /-- **the boundary of the model is the boundary part of the level set** -/
  bdry_eq : (𝓡∂ 9).boundary ↥W = {x : ↥W | (x : M) ∈ (𝓡∂ ((8 + k) + 1)).boundary M}
  /-- the identification of the model's boundary with the level set's boundary part -/
  bdryPreimage : ((𝓡∂ 9).boundary ↥W) ≃ₜ ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M)
  /-- **the relative fundamental class** -/
  w : (Work.Cohomology.relChains (TopCat.of ↥W) ((𝓡∂ 9).boundary ↥W)).homology 9
  /-- **`w` is a relative fundamental class**: at every interior point its local class generates the
  local homology (this is exactly the field `Work.ThomBordism.NullBordismFamily.w_fund`, and it is
  what ORIENT's `Work.Orient.exists_relFundClass_of_halfOrientation` produces from `γ`; the stronger
  statement "the local class *equals* `γ x hx`" is not needed by any consumer) -/
  w_fund : ∀ (x : ↥W) (hx : x ∉ (𝓡∂ 9).boundary ↥W),
    Submodule.span ℤ {(HomologicalComplex.homologyMap
      (Work.ThomBordism.relChainsInclPunct (TopCat.of ↥W) ((𝓡∂ 9).boundary ↥W) x hx) 9 w)} = ⊤
  /-- **the boundary of the class is the sum of the pieces' fundamental classes** -/
  sign : Work.Cohomology.hPairδ (TopCat.of ↥W) ((𝓡∂ 9).boundary ↥W) 8 w
      = ∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X
            (TopCat.of ((𝓡∂ 9).boundary ↥W))
            (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
              (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c

/-- **The orientation datum in the free-model form.** -/
def LevelOrientationDatumFree {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    {ι : Type} [Fintype ι] (Fam : ι → Man8)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)) : Prop :=
  Nonempty (LevelOrientationModelData k W hWcl L Fam e)

/-- **The endgame from the free-model orientation datum.**

The chart structure and the class are exactly the `NullBordismFamily` data (`w_fund` is its
`w_fund`, `sign` is its `hw`), so the null-bordism is the model itself. -/
theorem exists_nullBordismFamily_of_levelOrientationModelData {k : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {W : Set M} {hWcl : IsClosed W} {L : LocalLevelData k M W}
    {ι : Type} [Fintype ι] {Fam : ι → Man8}
    {e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)}
    (D : LevelOrientationModelData k W hWcl L Fam e) :
    Nonempty (NullBordismFamily ι Fam) := by
  letI := D.chartedSpace
  letI := D.isManifold
  letI := D.compactSpace
  letI := D.t2Space
  haveI : IsManifold (𝓡∂ 9) 1 ↥W := IsManifold.of_le (n := ∞) (by simp)
  exact ⟨{ W := ↥W, bdry := D.bdryPreimage.trans e, w := D.w, hw := D.sign, w_fund := D.w_fund }⟩

/-- **The free-model datum implies the conclusion** (the `Prop` form). -/
theorem exists_nullBordismFamily_of_levelOrientationDatumFree {k : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {W : Set M} {hWcl : IsClosed W} {L : LocalLevelData k M W}
    {ι : Type} [Fintype ι] {Fam : ι → Man8}
    {e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)}
    (h : LevelOrientationDatumFree W hWcl L Fam e) :
    Nonempty (NullBordismFamily ι Fam) :=
  h.elim exists_nullBordismFamily_of_levelOrientationModelData

/-- **The canonical-model datum implies the free-model datum**: take the canonical chart structure
(`Lvl.Setup.instChartedSpace`).  So the free-model datum is *weaker*, and every consumer of the
canonical-model datum (`Work.PTGeometric.LevelOrientationDatum`) still has one. -/
theorem levelOrientationDatumFree_of_datum {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {W : Set M} {hWcl : IsClosed W} {L : LocalLevelData k M W}
    {ι : Type} [Fintype ι] {Fam : ι → Man8}
    {e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)}
    (h : LevelOrientationDatum W hWcl L Fam e) : LevelOrientationDatumFree W hWcl L Fam e := by
  let S : Lvl.Setup k := levelSetup W hWcl L
  letI := Lvl.Setup.instChartedSpace S
  letI := Lvl.Setup.instIsManifold S
  letI := Lvl.Setup.instCompactSpace S
  obtain ⟨γ, hγ, bdryPreimage, w, htie, hsign⟩ := h
  -- the canonical-model datum states the tie to `γ`, which implies the span form
  have key : ∀ (x : S.Pre) (hx : x ∉ (𝓡∂ 9).boundary S.Pre),
      Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre)
          x hx) 9 w)} = ⊤ := by
    intro x hx
    rw [htie x hx]
    exact hγ.1 x hx
  exact ⟨{ chartedSpace := Lvl.Setup.instChartedSpace S, isManifold := Lvl.Setup.instIsManifold S, compactSpace := Lvl.Setup.instCompactSpace S, t2Space := inferInstance, bdry_eq := Set.ext fun x => Lvl.Setup.mem_boundary_iff S x, bdryPreimage := bdryPreimage, w := w, w_fund := key, sign := hsign }⟩

end

end Work.PTGeometric

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The orientation datum of the last mile in the free-model form, for an ambient collapse end**:
the end exhibits the bounding level set `W`, its local level data and the identification of its
boundary part with the pieces (as `Work.PTGeometric.AmbientOrientationDatum`), and the level set
carries an orientation datum with a chart structure chosen by the producer
(`Work.PTGeometric.LevelOrientationDatumFree`). -/
def AmbientOrientationDataFree (D : AmbientCollapseEnd n k ι Fam) : Prop :=
  ∃ (W : Set D.M) (hW : IsClosed W) (L : LocalLevelData k D.M W)
    (hset : W ∩ (𝓡∂ ((8 + k) + 1)).boundary D.M = D.S ∩ {x : D.M | D.v x = 0}),
    LevelOrientationDatumFree W hW L Fam ((Homeomorph.setCongr hset).trans D.endHomeo)

/-- **The endgame from the free-model orientation datum of an ambient collapse end.** -/
theorem exists_nullBordismFamily_of_ambientOrientationDataFree {D : AmbientCollapseEnd n k ι Fam}
    (h : AmbientOrientationDataFree D) : Nonempty (NullBordismFamily ι Fam) := by
  obtain ⟨W, hW, L, hset, hfree⟩ := h
  exact exists_nullBordismFamily_of_levelOrientationDatumFree hfree

/-- **The canonical-model datum implies the free-model datum** (at the level of an ambient collapse
end): so `Work.PTGeometric.OrientationProducer` in its canonical-model form still feeds the free
one, i.e. the free form is *weaker* and nothing is lost. -/
theorem ambientOrientationDataFree_of_datum {D : AmbientCollapseEnd n k ι Fam}
    (h : AmbientOrientationDatum D) : AmbientOrientationDataFree D := by
  obtain ⟨W, hW, L, hset, hd⟩ := h
  exact ⟨W, hW, L, hset, levelOrientationDatumFree_of_datum hd⟩

end

end Work.PTGeometric
