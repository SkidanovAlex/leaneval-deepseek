import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSSK.edgePieceToPullback
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.pieceBdryHornIso
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `cruxCapEqFIncl`

The cap chain `cruxCap` is the push-forward to `E` of the cap `thetaTop ⌢ iota_σ z`.  The hypothesis
`hz'` identifies that cap, inside the total pullback `T_σ`, with the image of a cycle `z'` of the
part `T_{σ|_{last vertex}}` of `T_σ` over the last vertex, under the fibre inclusion
`fibreInc p σ`.  The conclusion rewrites the push-forward as the composite of the two structure
maps of the vertex part: first the identification `vertexIso` of `T_{σ|last}` with the singular
simplicial set of the fibre of `p` over `σ(last vertex)`, and then the map induced by the inclusion
of that fibre into `E`.

Everything is a formal consequence of two pullback identities:

* `fibreInc p σ ≫ pullback.snd σ (Sing p) = pullback.snd (lastV s ≫ σ) (Sing p)`
  (`pullback.lift_snd`);
* `(vertexIso p σ').hom ≫ Sing (fibreIncl p (sigmaVert σ')) = pullback.snd σ' (Sing p)`,
  which is `phiAlong_snd` read backwards, since `vertexIso p σ' = (asIso (phiAlong p σ')).symm`
  and `phiAlong p σ'` is the inverse of `vertexIso p σ'`.

Both identities are then transported along the functoriality of the singular chain complex
(`sCCMap_comp'`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSS

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Functoriality of the singular chain complex, in applied form: the composition
`C(g) ≫ C(k)` of two chain maps, evaluated on an element, is `C(g ≫ k)`. -/
lemma sCCMap_comp_apply_hom {R : Type} [CommRing R] [Nontrivial R] {X Y Z : SSet.{0}}
    (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ} (x : (Work.SSSR.sCC R X).X n) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R k).f n))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R g).f n)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (g ≫ k)).f n)) x := by
  rw [Work.SSSR.sCCMap_comp', HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The fibre inclusion over the last vertex, followed by the second projection of `T_σ`, is the
second projection of `T_{σ|_{last vertex}}`. -/
lemma fibreInc_snd_lastV (p : C(E, B)) (s : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.fibreInc p σ ≫ pullback.snd σ (Work.SSSR.sSingP p)
      = pullback.snd (Work.Pi6.MSSK.lastV s ≫ σ) (Work.SSSR.sSingP p) := by
  rw [Work.Pi6.MSSK.fibreInc]
  exact pullback.lift_snd _ _ _

/-- The vertex identification of `T_{σ'}` with the singular simplicial set of the fibre, followed by
the map induced by the fibre inclusion, is the second projection of `T_{σ'}`. -/
lemma vertexIso_snd_lastV (p : C(E, B))
    (σ' : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (Work.Pi6.MSSK.vertexIso p σ').hom ≫
        Work.SSSR.sSingP (Work.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ'))
      = pullback.snd σ' (Work.SSSR.sSingP p) := by
  haveI : IsIso (Work.SSSR.phiAlong p σ') := Work.SSSR.phiAlong_isIso p σ'
  have hφ : (Work.Pi6.MSSK.vertexIso p σ').inv ≫ pullback.snd σ' (Work.SSSR.sSingP p)
      = Work.SSSR.sSingP (Work.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ')) := by
    rw [show (Work.Pi6.MSSK.vertexIso p σ').inv = Work.SSSR.phiAlong p σ' from by
      rw [Work.Pi6.MSSK.vertexIso, Work.SSSR.pullAlongVertexIsoIso, CategoryTheory.Iso.symm_inv]
      exact CategoryTheory.asIso_hom _]
    exact Work.SSSR.phiAlong_snd p σ'
  rw [← hφ, ← Category.assoc, CategoryTheory.Iso.hom_inv_id, Category.id_comp]

theorem cruxCapEqFIncl {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (z' : (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).cycles q)
    (hz' : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ)).f q))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).iCycles q)) z')
            = Work.Cohomology.cap 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
                (Work.Pi6.MSSK.thetaTop 𝕜 p σ) q (Work.Pi6.MSS.cruxIota 𝕜 p hfib s q σ z)) :
    Work.Pi6.MSS.cruxCap 𝕜 p hfib s q σ z
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sSingP (Work.StemsB.fibreIncl p
            (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastV s) σ))))).f q))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom).f q))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).iCycles q)) z')) := by
  -- the element of the chain complex of `T_{σ|last}` on which everything is evaluated
  let x : (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).X q :=
    (ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).iCycles q)) z'
  -- `hz'` identifies the cap with the image of `x` under `fibreInc p σ`
  have hcap : Work.Cohomology.cap 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop 𝕜 p σ) q (Work.Pi6.MSS.cruxIota 𝕜 p hfib s q σ z)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ)).f q)) x :=
    hz'.symm
  -- functoriality of the chain complex, for `fibreInc p σ`
  have hcomp : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ)).f q)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ ≫
          pullback.snd σ (Work.SSSR.sSingP p))).f q)) x :=
    sCCMap_comp_apply_hom (R := 𝕜) (g := Work.Pi6.MSSK.fibreInc p σ)
      (k := pullback.snd σ (Work.SSSR.sSingP p)) (n := q) (x := x)
  -- the first pullback identity
  have hstep : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ ≫
          pullback.snd σ (Work.SSSR.sSingP p))).f q)) x
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd (Work.Pi6.MSSK.lastV s ≫ σ)
          (Work.SSSR.sSingP p))).f q)) x :=
    congrArg (fun (m : Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ) ⟶ Work.SSSR.sSing E) =>
        (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 m).f q)) x) (fibreInc_snd_lastV p s σ)
  have hL : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ)).f q)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd (Work.Pi6.MSSK.lastV s ≫ σ)
          (Work.SSSR.sSingP p))).f q)) x := hcomp.trans hstep
  -- functoriality of the chain complex, for the vertex identification
  have hcompR : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sSingP
          (Work.StemsB.fibreIncl p (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV s ≫ σ))))).f q))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p
          (Work.Pi6.MSSK.lastV s ≫ σ)).hom).f q)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 ((Work.Pi6.MSSK.vertexIso p
          (Work.Pi6.MSSK.lastV s ≫ σ)).hom ≫ Work.SSSR.sSingP (Work.StemsB.fibreIncl p
          (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV s ≫ σ))))).f q)) x :=
    sCCMap_comp_apply_hom (R := 𝕜)
      (g := (Work.Pi6.MSSK.vertexIso p (Work.Pi6.MSSK.lastV s ≫ σ)).hom)
      (k := Work.SSSR.sSingP (Work.StemsB.fibreIncl p
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV s ≫ σ)))) (n := q) (x := x)
  -- the second pullback identity
  have hstepR : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 ((Work.Pi6.MSSK.vertexIso p
          (Work.Pi6.MSSK.lastV s ≫ σ)).hom ≫ Work.SSSR.sSingP (Work.StemsB.fibreIncl p
          (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV s ≫ σ))))).f q)) x
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd (Work.Pi6.MSSK.lastV s ≫ σ)
          (Work.SSSR.sSingP p))).f q)) x :=
    congrArg (fun (m : Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ) ⟶ Work.SSSR.sSing E) =>
        (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 m).f q)) x)
      (vertexIso_snd_lastV p (Work.Pi6.MSSK.lastV s ≫ σ))
  have hR : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sSingP (Work.StemsB.fibreIncl p
            (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))))).f q))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom).f q)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd (Work.Pi6.MSSK.lastV s ≫ σ)
          (Work.SSSR.sSingP p))).f q)) x := hcompR.trans hstepR
  -- push `hcap` forward along the second projection
  have e1 : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
        (Work.Cohomology.cap 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop 𝕜 p σ) q (Work.Pi6.MSS.cruxIota 𝕜 p hfib s q σ z))
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ)).f q)) x) :=
    congrArg (fun t => (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
      (pullback.snd σ (Work.SSSR.sSingP p))).f q)) t) hcap
  rw [Work.Pi6.MSS.cruxCap]
  exact e1.trans (hL.trans hR.symm)

end Work.Pi6.MSS
