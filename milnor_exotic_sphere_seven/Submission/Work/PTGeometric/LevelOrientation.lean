import Submission.Work.PTGeometric.AmbientRealisation
import Submission.Work.PTGeometric.Orientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the orientation datum of the source, on the **canonical model**

`Work.PTGeometric.LevelOrientationData` (the datum consumed by
`Work.PTGeometric.exists_nullBordismFamily_of_levelData`) asks, on the canonical model of the level set
`W` (see `LevelModel.lean`), for a relative fundamental class `w` of `(W, ∂W)` which is a local
generator at every interior point and whose boundary is the sum of the pieces' fundamental classes.

This file provides the **splittable form** of that datum, in which the two geometric halves are
visible as separate pieces of *data* (not as separately quantified statements):

* `LevelOrientationDatum hOrient W hW L Fam e` —
  * an orientation family `γ` of the canonical model (`Work.Orient.IsHalfOrientationFamily`, the G5-(i)
    input: the ambient orientation combined with the normal trivialisation furnished by the local
    submersions), **and**
  * a relative fundamental class `w` whose local classes are *exactly* `γ` (the tie — this is what
    `Work.Orient.exists_relFundClass_of_halfOrientation` produces from `γ`), **and**
  * the boundary identity `hPairδ w = Σ_i [piece_i]` (the G5-(ii) sign computation).
* `Work.PTGeometric.levelOrientationData_of_datum` — the datum implies the interface
  (`w_fund` follows from `γ` being a family of generators and the tie).
* `Work.PTGeometric.AmbientOrientationDatum` / `…ambientOrientationData_of_datum` — the same at the
  level of an `AmbientCollapseEnd`, i.e. for the collapse end produced by the source construction.

## Why the datum is stated this way, and not as a pair of universally quantified statements

Two earlier formulations were *refuted by reviewers* / are not derivable from the geometry, and are
recorded here so that they are not re-introduced:

* quantifying over **every smooth model** `W' ≃ₜ ↥W` and asking each to carry an orientation family: a
  non-orientable manifold carries none, and a mere homeomorphism does not transport a smooth structure
  constructively, so this is a statement about arbitrary smooth structures on the space `W` — not
  provable from the level data.  (`LevelModel.lean` explains the canonical-model repair.)
* quantifying the *sign* over **every** orientation family `γ` (`∀ γ hγ, hPairδ w_γ = + Σ`): flipping
  `γ ↦ -γ` flips `w_γ ↦ -w_γ`, hence `hPairδ w_γ`, while the right-hand side
  `Σ_i [piece_i] ∈ H₈(∂W)` does not depend on `γ` and is non-zero as soon as one piece is non-empty —
  so the universally quantified form forces `Σ_i [piece_i] = 0`.  The sign must therefore be asserted
  for a *given* family, which is what the ∃-form below does (the family and the class together).

The remaining content — the construction of `γ` and the computation of the sign — is precisely the
geometric work of G5, and it is now a statement about **one explicit manifold** (the canonical model).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]

/-- **G5 of the situation, on the canonical model of the level set**: an orientation family of the
canonical model, a relative fundamental class whose local classes are exactly that family, and the
boundary identity (the class's boundary is the sum of the pieces' fundamental classes, along the
identification `e` of `W ∩ ∂M` with the pieces). -/
def LevelOrientationDatum (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    {ι : Type} [Fintype ι] (Fam : ι → Man8)
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt)) : Prop :=
  let S : Lvl.Setup k := levelSetup W hWcl L
  letI := Lvl.Setup.instChartedSpace S
  letI := Lvl.Setup.instIsManifold S
  letI := Lvl.Setup.instCompactSpace S
  ∃ (γ : ∀ x : S.Pre, x ∉ (𝓡∂ 9).boundary S.Pre → Work.Orient.LocH (TopCat.of S.Pre) 9 x)
    (_hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of S.Pre) γ)
    (bdryPreimage : ((𝓡∂ 9).boundary S.Pre) ≃ₜ
      ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M))
    (w : (Work.Cohomology.relChains (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre)).homology 9),
    (∀ (x : S.Pre) (hx : x ∉ (𝓡∂ 9).boundary S.Pre),
      HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre) x hx) 9 w
        = γ x hx) ∧
    (Work.Cohomology.hPairδ (TopCat.of S.Pre) ((𝓡∂ 9).boundary S.Pre) 8 w
      = ∑ i, HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (Fam i).X
            (TopCat.of ((𝓡∂ 9).boundary S.Pre))
            (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
              (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c)

/-- **The splittable datum implies the orientation interface `LevelOrientationData`.**

The only content beyond projection is the local-generator property of `w`: it follows from the tie
`w ↦ γ` and from `γ` being a family of generators of the local homology
(`IsHalfOrientationFamily`'s first clause). -/
theorem levelOrientationData_of_datum (W : Set M) (hWcl : IsClosed W) (L : LocalLevelData k M W)
    {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (e : ↥(W ∩ (𝓡∂ ((8 + k) + 1)).boundary M) ≃ₜ (Σ i : ι, (Fam i).pt))
    (h : LevelOrientationDatum W hWcl L Fam e) :
    LevelOrientationData W hWcl L Fam e := by
  let S : Lvl.Setup k := levelSetup W hWcl L
  letI := Lvl.Setup.instChartedSpace S
  letI := Lvl.Setup.instIsManifold S
  letI := Lvl.Setup.instCompactSpace S
  obtain ⟨γ, hγ, bdryPreimage, w, htie, hsign⟩ := h
  refine ⟨bdryPreimage, w, fun x hx => ?_, hsign⟩
  rw [htie x hx]
  exact hγ.1 x hx

end

end Work.PTGeometric

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}

/-- **G5 of the situation for the ambient collapse end**: the producer exhibits the bounding level set
`W` (the zero set of the ambient field), its local level-set data and the boundary identification, and
carries the splittable orientation datum (`LevelOrientationDatum`) on the canonical model of `(W, L)`.

See `Work.PTGeometric.AmbientOrientationData` for why `W` is part of the datum (quantifying over every
closed `W` with the same boundary part is *false*: a non-orientable such `W` carries no orientation
family).  The strong form below (with the explicit orientation family and the tie to the class, rather
than only the class) is what a geometric producer targets;
`Work.PTGeometric.ambientOrientationData_of_datum` recovers the interface from it. -/
def AmbientOrientationDatum (D : AmbientCollapseEnd n k ι Fam) : Prop :=
  ∃ (W : Set D.M) (hW : IsClosed W) (L : LocalLevelData k D.M W)
    (hset : W ∩ (𝓡∂ ((8 + k) + 1)).boundary D.M = D.S ∩ {x : D.M | D.v x = 0}),
    LevelOrientationDatum W hW L Fam ((Homeomorph.setCongr hset).trans D.endHomeo)

/-- **The orientation datum of the last mile from its splittable form.** -/
theorem ambientOrientationData_of_datum (D : AmbientCollapseEnd n k ι Fam)
    (h : AmbientOrientationDatum D) : AmbientOrientationData D := by
  obtain ⟨W, hW, L, hset, hd⟩ := h
  exact ⟨W, hW, L, hset, levelOrientationData_of_datum W hW L _ hd⟩

end

end Work.PTGeometric
