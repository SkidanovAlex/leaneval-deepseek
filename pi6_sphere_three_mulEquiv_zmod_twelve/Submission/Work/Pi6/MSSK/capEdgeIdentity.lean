import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.cochainDiff_lastFaceTop
import Submission.Work.Pi6.MSSK.capLastFaceTopHornZero
import Submission.Work.Pi6.MSSK.capLastFaceTopLastFaceMap
import Submission.Work.Cohomology.cap_d
import Submission.Work.Cohomology.pd_crux
import Submission.Work.SSSR.serreE1PieceIotaDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

namespace Work.Pi6.MSSK

noncomputable section

/-!
# The edge identity of the cap–transport computation

`capEdgeIdentity` is the final assembly step of the cap/transport lemma
(`REFS/NOTES_LEAD_MSSK.md`, §1, step (d)): the boundary formula for the cap product with the
*last-face top cochain* `lastFaceTop`, together with

* the vanishing `capLastFaceTopHornZero` of `lastFaceTop` on the horn,
* the naturality `capLastFaceTopLastFaceMap` of the cap product along the last-face pasting map,
* the coboundary computation `cochainDiff_lastFaceTop` (`δ lastFaceTop = (-1)^(t+1) • thetaTop`),

identifies the difference `thetaTop ⌢ c - (lastFaceMap)_*(thetaTop' ⌢ w')` with
`∂(lastFaceTop ⌢ c)`.  This is exactly Hatcher's cap boundary formula, shifted by the peeling
datum `hpeel` which decomposes `∂c` into its last-face and horn parts.
-/

/-- **The shifted boundary formula for the cap product.**  If the coboundary of a degree-`t`
cochain `b` is `(-1)^(t+1)` times a degree-`(t+1)` cochain `a`, then for every chain `c` of degree
`t + (K+1)` the boundary of `b ⌢ c` is `a ⌢ c + (-1)^t • (b ⌢ ∂c)` (with the degree transport
`t + (K+1) = (t+1) + K` made explicit).  This is the `cap_d` boundary formula with the
`δb`-term rewritten. -/
lemma capDShift (R : Type) [CommRing R] [Nontrivial R] (X : SSet) {t K : ℕ}
    (a : Work.Cohomology.Cochain R X (t+1)) (b : Work.Cohomology.Cochain R X t)
    (hb : Work.Cohomology.cochainDiff R X b = (-1:R)^(t+1) • a)
    (c : (Work.SSSR.sCC R X).X (t+(K+1))) :
    ((Work.SSSR.sCC R X).d (K+1) K).hom (Work.Cohomology.cap R X b (K+1) c)
      = Work.Cohomology.cap R X a K (Work.SSSR.castElem (Work.SSSR.sCC R X) (by omega) c)
        + (-1:R)^t • Work.Cohomology.cap R X b K
            (((Work.SSSR.sCC R X).d (t+(K+1)) (t+K)).hom c) := by
  have hcast : ((Work.Cohomology.capIdx t K) ▸ c : (Work.SSSR.sCC R X).X ((t+1)+K))
      = Work.SSSR.castElem (Work.SSSR.sCC R X) (by omega) c := by
    unfold Work.SSSR.castElem
    rw [Subsingleton.elim (Work.Cohomology.capIdx t K) (by omega : t + (K+1) = (t+1)+K)]
  have hone : (-1:R)^t * (-1:R)^(t+1) = -1 := by
    have h := Work.Cohomology.capd_neg_one_pow_mul_pow_add (R := R) t 1
    simpa using h
  rw [Work.Cohomology.cap_d R X (n := t) (m := K) b c, hb, Work.Cohomology.cap_smul', hcast]
  simp only [LinearMap.smul_apply]
  rw [smul_sub, smul_smul, hone, neg_one_smul]
  abel

/-- **`lastFaceChain ≫ (boundary inclusion)` is the chain map of the last-face pasting map.**
The explicit last-face chain map `Work.SSSR.lastFaceChain` lands in the boundary subcomplex
`∂T_σ`; regarded in the ambient `T_σ` it is the push-forward along the pasting map
`lastFaceMap`. -/
lemma lastFaceChain_comp_inc {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ ≫
        Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι
      = Work.SSSR.sCCMap R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ) := by
  simp only [Work.SSSR.lastFaceChain]
  rw [Category.assoc, ← Work.SSSR.sCCMap_comp', ← Work.SSSR.sCCMap_comp']
  rw [Subfunctor.homOfLe_ι, SSet.Subcomplex.toRange_ι, Work.SSSR.lastFaceMap_eq_pullFaceIncl]

theorem capEdgeIdentity (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {t K : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (t + (K+1)))
    (w' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).X (t + K))
    (hpeel : ∃ yy : (Work.SSSR.sCC R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).X (t + K),
        ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (t + (K+1)) (t + K)).hom c
          = (-1 : R)^(t+1) • ((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (t + K)
              ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f (t + K) w'))
            + (Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f (t + K) yy) :
    Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) K
        (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
          (by omega : t + (K+1) = (t+1) + K) c)
      - ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.lastFaceMapAlong p σ)).f K
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
            (Work.Pi6.MSSK.thetaTop R p (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) K w'))
      = ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (K+1) K).hom
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.lastFaceTop R p σ) (K+1) c) := by
  obtain ⟨yy, hyy⟩ := hpeel
  -- unfold the last-face pasting map, so that everything is stated with `lastFaceMap`
  simp only [Work.Pi6.MSSK.lastFaceMapAlong]
  -- ## The value of `thetaTop ⌢ ∂c`
  have h2 : (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.lastFaceTop R p σ) K
        (((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (t+(K+1)) (t+K)).hom c))
      = (-1:R)^(t+1) • ((Work.SSSR.sCCMap R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)).f K
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
            (Work.Pi6.MSSK.thetaTop R p (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) K w')) := by
    -- peel `∂c` into its last-face and horn parts
    rw [hyy]
    simp only [map_add, map_smul]
    -- `lastFaceTop` kills the horn part
    rw [Work.Pi6.MSSK.capLastFaceTopHornZero R p σ yy, add_zero]
    -- the composite `lastFaceChain ≫ (∂T_σ ⊆ T_σ)` is the pasting map
    have hcomp : Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ ≫
        Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι
        = Work.SSSR.sCCMap R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ) :=
      lastFaceChain_comp_inc R p σ
    have hf := congrArg (fun (φ : Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) ⟶
          Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) => φ.f (t+K)) hcomp
    have h2' : (CategoryTheory.ConcreteCategory.hom ((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (t+K)))
          ((CategoryTheory.ConcreteCategory.hom ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f (t+K))) w')
        = (CategoryTheory.ConcreteCategory.hom ((Work.SSSR.sCCMap R (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ)).f (t+K))) w' := by
      have h2'' := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).X (t+K) ⟶
            (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (t+K)) => g.hom w') hf
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2''
      exact h2''
    rw [h2', Work.Pi6.MSSK.capLastFaceTopLastFaceMap R p σ w']
  -- ## The boundary formula for `lastFaceTop ⌢ c`
  have h1 := capDShift R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (Work.Pi6.MSSK.thetaTop R p σ) (Work.Pi6.MSSK.lastFaceTop R p σ)
      (Work.Pi6.MSSK.cochainDiff_lastFaceTop R p σ) c
  rw [h1, h2]
  rw [smul_smul, show ((-1:R)^t * (-1:R)^(t+1)) = -1 from by
    have h := Work.Cohomology.capd_neg_one_pow_mul_pow_add (R := R) t 1
    simpa using h, neg_one_smul]
  abel

end

end Work.Pi6.MSSK
