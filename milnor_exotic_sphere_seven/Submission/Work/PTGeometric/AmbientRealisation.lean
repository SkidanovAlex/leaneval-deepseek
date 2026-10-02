import Submission.Work.PTGeometric.exists_nullBordismFamily_of_levelData
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.PTGeometric.localLevelData_of_ambientCollapseEnd
import Submission.Work.PTGeometric.GenuineTransversality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the realisation in the ambient form, and G6 from it

This file wires the last-mile chain of `LastMile.lean` / `localLevelData_of_ambientCollapseEnd.lean` /
`exists_nullBordismFamily_of_levelData.lean` into the deliverable.

* `Work.PTGeometric.LevelOrientationData` — the orientation datum of the situation for a preimage
  *given as a set* (a closed subset locally cut out by submersions), the named form of the `orient`
  hypothesis of `exists_nullBordismFamily_of_levelData`;
* `Work.PTGeometric.AmbientOrientationData` — the same datum for an `AmbientCollapseEnd`, quantified
  over the sets `W` that the bridge `localLevelData_of_ambientCollapseEnd` produces;
* `Work.PTGeometric.exists_nullBordismFamily_of_ambientCollapseEnd` — **the endgame**: the ambient
  collapse-end data plus that orientation datum give a `NullBordismFamily` of the pieces;
* `Work.PTGeometric.AmbientRealisation` — the geometric realisation in the ambient form: for every
  finite family, every choice of normal and genuine collapse data and every `m > 0` with trivial
  `m`-th power of the product of the pieces' collapse classes, a *positive multiple* of the family
  carries `AmbientCollapseEnd` + orientation data;
* `Work.PTGeometric.genuineTransversality_of_ambientRealisation` — it gives G6, i.e.
  `Work.PTGeometric.GenuineTransversality`;
* `Work.PTGeometric.transversalityCoreFamily_of_ambientRealisation` (`Assembly.lean`) — the
  deliverable from it.

The difference between `AmbientRealisation` and `GenuineRealisation`/`GenuineNullBordismData`
(`GenuineTransversality.lean`) is exactly the content of this session's work: the latter demands a
*globally smooth* map into the manifold part `X.E` of the Thom space, which the genuine null-homotopy
cannot provide (it takes values in the one-point compactification, see `LastMile.lean`), while the
former demands the ambient data of the collapse on a source on which the null-homotopy avoids `∞` —
and from that data everything down to the consumer is now proved.

## Main results

* `Work.PTGeometric.exists_nullBordismFamily_of_ambientCollapseEnd`
* `Work.PTGeometric.genuineTransversality_of_ambientRealisation`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-- **The orientation datum of the situation for a level set** — on the **canonical model**.

The datum is: on the manifold model of `W` built by the preimage theorem from the local level-set data
(`Work.PTGeometric.levelModel W hWcl L`, i.e. `↥W` with the submersion-normal-form charts of
`Submission/Work/PTGeometric/Lvl/`), there is a relative fundamental class of `(W', ∂W')` which is a
local generator of the local homology at every interior point and whose boundary is the sum of the
pieces' fundamental classes along the identification `e` of `W ∩ ∂M` with the pieces.

This is `Work.PTGeometric.GenuinePullbackOrientationData` with `CorePreimage X c` replaced by the level
set `W`: the preimage is *given* (locally cut out by submersions) rather than obtained from a global
defining function.

**Why the canonical model and not "every model `W' ≃ₜ ↥W`".**  An earlier revision quantified over
every smooth model of the *space* `W` and asked each of them to carry an orientation family.  That
statement is not derivable from the geometry — a non-orientable manifold has no orientation family, and
whether a *given* smooth model admits one is a property of its smooth structure, which a mere
homeomorphism `W' ≃ₜ ↥W` does not transport constructively.  The canonical model, by contrast, is the
explicit manifold that the source construction produces, and on it the orientation is a computation
(the ambient orientation together with the normal trivialisation furnished by the local submersions).
-/
def LevelOrientationData {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    {ι : Type} [Fintype ι] (Fam : ι → Man8)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)) : Prop :=
  let S : Lvl.Setup k := levelSetup W hWcl L
  letI := Lvl.Setup.instChartedSpace S
  letI := Lvl.Setup.instIsManifold S
  letI := Lvl.Setup.instCompactSpace S
  ∃ (bdryPreimage : ((𝓡∂ 9).boundary S.Pre) ≃ₜ
        ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M))
    (w : (Work.Cohomology.relChains (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre)).homology 9),
    (∀ (x : S.Pre) (hx : x ∉ (𝓡∂ 9).boundary S.Pre),
      Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre) x hx) 9 w)}
        = ⊤) ∧
    (Work.Cohomology.hPairδ (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre) 8 w
      = ∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X
            (TopCat.of ((𝓡∂ 9).boundary S.Pre))
            (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
              (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c)

/-- **The endgame with the named orientation datum.** -/
theorem exists_nullBordismFamily_of_levelData' {k : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt))
    (h : LevelOrientationData W hWcl L Fam e) : Nonempty (NullBordismFamily ι Fam) :=
  exists_nullBordismFamily_of_levelData M W hWcl L e h

/-- **The orientation datum of the situation for an ambient collapse end**: the producer *exhibits*
the bounding level set `W` (in the source construction: the zero set of the ambient field `v`), its
closedness, its local level-set data `L` and the identification of its boundary part with the collapse
end, **and** the orientation datum of the canonical model of `(W, L)`.

**Why the level set is part of the datum.**  An earlier revision quantified over *every* closed `W`
carrying local level-set data and with `W ∩ ∂M = D.S ∩ {v = 0}`.  That is not provable — and not true:
a non-orientable `9`-manifold `W` (e.g. `N × {0} ⊆ N × D¹` for a closed non-orientable `N`, with the
end empty) satisfies both hypotheses, and then `LevelOrientationData` fails because a non-orientable
model carries no orientation family.  The geometry orients *the* null-bordism it produces (the normal
bundle of the zero set of a section of the trivialised plane bundle `im P` is trivial, so the ambient
orientation orients it), not an arbitrary `W` with the same boundary.  Hence the datum exhibits `W`. -/
def AmbientOrientationData {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (D : AmbientCollapseEnd n k ι Fam) : Prop :=
  ∃ (W : Set D.M) (hW : IsClosed W) (L : LocalLevelData k D.M W)
    (hset : W ∩ (𝓡∂ ((8 + k) + 1)).boundary D.M = D.S ∩ {x : D.M | D.v x = 0}),
    LevelOrientationData W hW L Fam ((Homeomorph.setCongr hset).trans D.endHomeo)

/-- **The endgame for the ambient collapse-end data**: the ambient data, together with the exhibited
oriented null-bordism (`AmbientOrientationData`), give a null-bordism of the pieces. -/
theorem exists_nullBordismFamily_of_ambientCollapseEnd {n k : ℕ} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} (D : AmbientCollapseEnd n k ι Fam) (h : AmbientOrientationData D) :
    Nonempty (NullBordismFamily ι Fam) := by
  obtain ⟨W, hWcl, L, hset, hdat⟩ := h
  exact exists_nullBordismFamily_of_levelData' D.M W hWcl L
    ((Homeomorph.setCongr hset).trans D.endHomeo) hdat

/-- **The geometric realisation in the ambient form.**

As `Work.PTGeometric.GenuineRealisation` (`GenuineTransversality.lean`), but producing the ambient
collapse-end data of `LastMile.lean` (on a source on which the null-homotopy of the collapse map avoids
the basepoint of the Thom space), together with the orientation datum of the situation, for a positive
multiple of the family.  This is the form in which the geometric construction — the regular
neighbourhood of the preimage of the core, G2 with the values prescribed on the collapse end, G3, the
identification of the ends and G5 — is to be carried out. -/
structure AmbientRealisation (n k : ℕ) (D : ThomTarget k) where
  /-- the geometric realisation of a null-homotopy of a positive multiple of the genuine collapse
  class, in ambient coordinates, with the orientation datum of the situation -/
  collapse : ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8)
      (Nd : ∀ i, NormalBundlData (Fam i))
      (r : ∀ i, Work.Tubular.TubeThomRep k D (Fam i) (Nd i)) (m : ℕ),
    0 < m → (∏ i, tubeAlpha (r i)) ^ m = 1 →
      ∃ (m' : ℕ), 0 < m' ∧
        ∃ D' : AmbientCollapseEnd n k (Fin m' × ι) (fun x => Fam x.2),
          AmbientOrientationData D'

/-- **G6 from the ambient realisation.**  The ambient collapse-end data of a positive multiple of the
family, with the orientation datum of the situation, give a null-bordism of a positive multiple of the
family — i.e. `Work.PTGeometric.GenuineTransversality`. -/
theorem genuineTransversality_of_ambientRealisation {n k : ℕ} {D : ThomTarget k}
    (R : AmbientRealisation n k D) : GenuineTransversality k D := by
  intro ι _ Fam Nd r m hm hpow
  obtain ⟨m', hm', D', hD'⟩ := R.collapse ι Fam Nd r m hm hpow
  exact ⟨m', hm', exists_nullBordismFamily_of_ambientCollapseEnd D' hD'⟩

end

end Work.PTGeometric
