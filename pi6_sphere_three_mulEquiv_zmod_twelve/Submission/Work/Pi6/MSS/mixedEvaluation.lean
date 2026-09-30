import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSS.evalInclEqOfF2
import Submission.Work.Pi6.MSS.transportChainTriv
import Submission.Work.Pi6.MSS.cruxCapEqFIncl
import Submission.Work.Pi6.MSS.cruxRel
import Submission.Work.Pi6.MSSK.capLiftTriv
import Submission.Work.Pi6.MSS.exists_edge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

lemma cruxU_cycle (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z' : ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).cycles q) :
    ((Work.SSSR.sCC 𝕜 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))))).d q ((ComplexShape.down ℕ).next q) (cruxU 𝕜 p hfib s q σ z') = 0 := by
  have hz : (ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).d q ((ComplexShape.down ℕ).next q)))
      ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).iCycles q)) z') = 0 := by
    have h := congrArg (fun (g : ( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).cycles q ⟶ ( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).X ((ComplexShape.down ℕ).next q)) =>
      (ModuleCat.Hom.hom g) z')
      (HomologicalComplex.iCycles_d (K := (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))) q ((ComplexShape.down ℕ).next q))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have h1 := Work.SSSR.sCCMap_d_applyA (R := 𝕜) (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom q
    ((ComplexShape.down ℕ).next q)
    ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).iCycles q)) z')
  rw [cruxU, h1]
  exact (congrArg (fun x => (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom).f
      ((ComplexShape.down ℕ).next q))) x) hz).trans (map_zero _)

lemma cruxChain_eq_cruxIota (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) :
    cruxChain 𝕜 p hfib s q σ z
      = ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f (s + q)).hom
          (cruxIota 𝕜 p hfib s q σ z) := rfl

lemma dualMap_snd_pbC (p : C(E, B)) (s : ℕ)
    (β : Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing B) s)
    (hβ : ∀ τ ∈ (Work.SSSR.sSing B).degenerate s,
      Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β τ = 0)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f s)).dualMap
        (pbC 𝕜 p s β)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) •
          Work.Pi6.MSSK.thetaTop 𝕜 p σ := by
  apply Work.Cohomology.genEval_ext
  intro w
  have hA1 : Work.Cohomology.genEval 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f s)).dualMap
        (pbC 𝕜 p s β)) w
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p s β)
          ((pullback.snd σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) w) :=
    Work.Cohomology.genEval_dualMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p)) (pbC 𝕜 p s β) w
  have hA2 : Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p s β)
          ((pullback.snd σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) w)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
          ((Work.SSSR.sSingP p).app (op (SimplexCategory.mk s))
            ((pullback.snd σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) w)) :=
    genEval_pbC_SSSR 𝕜 p β _
  have hA3 : Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
          ((Work.SSSR.sSingP p).app (op (SimplexCategory.mk s))
            ((pullback.snd σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) w))
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
          (((pullback.fst σ (Work.SSSR.sSingP p) ≫ σ).app (op (SimplexCategory.mk s))) w) := by
    rw [sSingP_app_snd_eq p s σ w]
  have hB : Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
          (((pullback.fst σ (Work.SSSR.sSingP p) ≫ σ).app (op (SimplexCategory.mk s))) w)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) *
          Work.Pi6.MSSK.thetaVal 𝕜 p σ w :=
    Work.Pi6.MSS.normalizedPullback 𝕜 p β hβ σ w
  have hC : Work.Cohomology.genEval 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
      (Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) •
        Work.Pi6.MSSK.thetaTop 𝕜 p σ) w
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) *
          Work.Pi6.MSSK.thetaVal 𝕜 p σ w := by
    have h1 : Work.Cohomology.genEval 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        ((Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) : 𝕜) •
          (Work.Pi6.MSSK.thetaTop 𝕜 p σ :
            Work.Cohomology.Cochain 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s)) w
        = (Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) •
          Work.Cohomology.genEval 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop 𝕜 p σ) w :=
      Work.Cohomology.genEval_smul _ _ w
    rw [h1, genEval_thetaTop' 𝕜 p s σ w]
    exact smul_eq_mul _ _
  exact (hA1.trans (hA2.trans (hA3.trans hB))).trans hC.symm

/-- **The front-end of the mixed evaluation.** -/
theorem eval_cup_pbC_crux (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (β : Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing B) s) (hβ : β ∈ ZB 𝕜 B s)
    (y1 : Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q) :
    (Work.Cohomology.cup 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p s β) y1)
        (cruxChain 𝕜 p hfib s q σ z)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) *
          y1 (cruxCap 𝕜 p hfib s q σ z) := by
  have hβn : ∀ τ ∈ (Work.SSSR.sSing B).degenerate s,
      Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β τ = 0 := by
    intro τ hτ
    exact (Work.Pi6.MSS.mem_ZB (𝕜 := 𝕜) (B := B) (s := s) (c := β)).mp hβ |>.2 τ (Work.Pi6.MSS.ess_lt_of_mem_degenerate hτ)
  have h1 : (Work.Cohomology.cup 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p s β) y1)
        (cruxChain 𝕜 p hfib s q σ z)
      = ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f (s+q))).dualMap
          (Work.Cohomology.cup 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p s β) y1))
          (cruxIota 𝕜 p hfib s q σ z) := rfl
  have h2 : ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f (s+q))).dualMap
          (Work.Cohomology.cup 𝕜 (Work.SSSR.sSing E) (pbC 𝕜 p s β) y1))
          (cruxIota 𝕜 p hfib s q σ z)
      = (Work.Cohomology.cup 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f s)).dualMap (pbC 𝕜 p s β))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1))
          (cruxIota 𝕜 p hfib s q σ z) :=
    congrArg (fun (g : Work.Cohomology.Cochain 𝕜
          (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) (s+q)) =>
        g (cruxIota 𝕜 p hfib s q σ z))
      (Work.Cohomology.cupNatural 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))
        (pbC 𝕜 p s β) y1).symm
  have h3 : (Work.Cohomology.cup 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f s)).dualMap (pbC 𝕜 p s β))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1))
          (cruxIota 𝕜 p hfib s q σ z)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
            (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) *
          y1 (cruxCap 𝕜 p hfib s q σ z) := by
    have hA : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f s)).dualMap (pbC 𝕜 p s β)
        = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
              (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) •
            Work.Pi6.MSSK.thetaTop 𝕜 p σ :=
      dualMap_snd_pbC 𝕜 p s β hβn σ
    have hsc : (Work.Cohomology.cup 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
              (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)) •
            Work.Pi6.MSSK.thetaTop 𝕜 p σ)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1))
          (cruxIota 𝕜 p hfib s q σ z)
        = (Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
              (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) *
          ((Work.Cohomology.cup 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop 𝕜 p σ)
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1))
          (cruxIota 𝕜 p hfib s q σ z)) := by
      have h := (Work.Cohomology.cupBilinear 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        s q).2.1
        (Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
          (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)))
        (Work.Pi6.MSSK.thetaTop 𝕜 p σ)
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1)
      rw [h, LinearMap.smul_apply, smul_eq_mul]
    rw [hA, hsc]
    have hkr : (Work.Cohomology.cup 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop 𝕜 p σ)
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1))
            (cruxIota 𝕜 p hfib s q σ z)
        = ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
              (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1)
            (Work.Cohomology.cap 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
              (Work.Pi6.MSSK.thetaTop 𝕜 p σ) q (cruxIota 𝕜 p hfib s q σ z)) :=
      (Work.Cohomology.kronecker_cap_cup 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop 𝕜 p σ)
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (pullback.snd σ (Work.SSSR.sSingP p))).f q)).dualMap y1)
        (cruxIota 𝕜 p hfib s q σ z)).symm
    rw [hkr]
    rfl
  exact h1.trans (h2.trans h3)


/-- **The fibre half of the mixed evaluation.** -/
theorem evalFibre (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q))
    (b : B) (u : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p b).X q)
    (hu : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fibCC 𝕜 p b).d q
        ((ComplexShape.down ℕ).next q))) u = 0)
    (v : Work.SSSR.coefM (R := 𝕜) p e₀ q)
    (htriv : (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q b).hom.hom
        ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p b).homologyπ q))
          ((Work.SSSR.fibreCC (R := 𝕜) p b).cyclesMk u ((ComplexShape.down ℕ).next q) rfl hu))
      = Work.Pi6.MSS.cruxEps 𝕜 s •
        (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom v) :
    (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (b)).f q)) u)
      = Work.Pi6.MSS.cruxEps 𝕜 s *
        (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
          (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
              (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
          v) := by
  obtain ⟨e, he0, he1⟩ := Work.Pi6.MSS.exists_edge p e₀ hconn b
  cases he0
  obtain ⟨w, hw, c, hc, hrel, htr⟩ := Work.Pi6.MSS.transportChainTriv p e₀ hfib hconn q e u hu
  generalize hL : Work.Pi6.MSS.E2cfk.lastVert e = L at he1 w hw hrel htr
  cases he1
  -- ### step 1: the evaluation is invariant under the (simplicial) transport
  have hα : (Work.Pi6.MSS.serreCF 𝕜 E B p).d q
      (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
      ∈ (Work.Pi6.MSS.serreCF 𝕜 E B p).F 2 (q + 1) := y.2.2
  have h1 : (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert e)).f q)) u)
      = (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q)) w) :=
    Work.Pi6.MSS.evalInclEqOfF2 p e₀ q (Work.SSSR.sigmaVert e)
      (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1) hα u w c hc hrel
  -- ### step 2: the Kronecker pairing on the fibre over `p e₀`
  have h2 : (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q)) w)
      = Work.Cohomology.kronH 𝕜 (Work.SSSR.sSing (Work.StemsB.fibre p (p e₀))) q
          (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
              (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w
              ((ComplexShape.down ℕ).next q) rfl hw)) := by
    have hkron := Work.Cohomology.kronH_apply 𝕜 (Work.SSSR.sSing (Work.StemsB.fibre p (p e₀)))
      (Work.Pi6.MSS.resCochain 𝕜 E B p e₀ q y.1)
      (Work.Pi6.MSS.resCochain_cyc 𝕜 E B p e₀ q y)
      ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w
        ((ComplexShape.down ℕ).next q) rfl hw)
    have hicy : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).iCycles q))
        ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w ((ComplexShape.down ℕ).next q) rfl hw) = w :=
      HomologicalComplex.i_cyclesMk (K := Work.SSSR.fibreCC (R := 𝕜) p (p e₀)) w
        ((ComplexShape.down ℕ).next q) rfl hw
    have hstep1 : (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q)) w)
        = (Work.Pi6.MSS.resCochain 𝕜 E B p e₀ q y.1)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).iCycles q))
              ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w
                ((ComplexShape.down ℕ).next q) rfl hw)) := by
      rw [hicy]
      rfl
    have hstep2 : (Work.Pi6.MSS.resCochain 𝕜 E B p e₀ q y.1)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).iCycles q))
              ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w
                ((ComplexShape.down ℕ).next q) rfl hw))
        = Work.Cohomology.kronH 𝕜 (Work.SSSR.sSing (Work.StemsB.fibre p (p e₀))) q
            (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
              (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
                (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w
                ((ComplexShape.down ℕ).next q) rfl hw)) := by
      rw [Work.Pi6.MSS.rho_mkQ 𝕜 E B p e₀ q y]
      exact hkron.symm
    exact hstep1.trans hstep2
  -- ### step 3: the class of `w` is the transported class
  have h3 : ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).homologyπ q))
        ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w ((ComplexShape.down ℕ).next q) rfl hw))
      = Work.Pi6.MSS.cruxEps 𝕜 s • v := by
    have hinj : Function.Injective (fun x : Work.SSSR.PiS.HZ 𝕜 (Work.SSSR.StemsB.fibre p (p e₀)) q =>
        (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom) x) := by
      intro a bl hab
      have h1 : (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv)
          ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom) a) = a := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
          LinearMap.id_apply]
          using congrArg (fun (g : Work.SSSR.PiS.HZ 𝕜 (Work.SSSR.StemsB.fibre p (p e₀)) q ⟶ Work.SSSR.PiS.HZ 𝕜 (Work.SSSR.StemsB.fibre p (p e₀)) q) => (ModuleCat.Hom.hom g) a)
            (Iso.hom_inv_id (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)))
      have h2 : (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv)
          ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom) bl) = bl := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
          LinearMap.id_apply]
          using congrArg (fun (g : Work.SSSR.PiS.HZ 𝕜 (Work.SSSR.StemsB.fibre p (p e₀)) q ⟶ Work.SSSR.PiS.HZ 𝕜 (Work.SSSR.StemsB.fibre p (p e₀)) q) => (ModuleCat.Hom.hom g) bl)
            (Iso.hom_inv_id (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)))
      have h4 := congrArg (fun x => (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv) x) hab
      rw [h1, h2] at h4
      exact h4
    apply hinj
    have hkey : (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom)
        ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).homologyπ q))
          ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w ((ComplexShape.down ℕ).next q) rfl hw))
        = (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom) (Work.Pi6.MSS.cruxEps 𝕜 s • v) :=
      htr.symm.trans (htriv.trans (map_smul
        (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom) (Work.Pi6.MSS.cruxEps 𝕜 s) v).symm)
    exact hkey
  calc (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSS.sigmaVert e)).f q)) u)
      = (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (p e₀)).f q)) w) := h1
    _ = Work.Cohomology.kronH 𝕜 (Work.SSSR.sSing (Work.StemsB.fibre p (p e₀))) q
          (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
              (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (p e₀)).cyclesMk w
              ((ComplexShape.down ℕ).next q) rfl hw)) := h2
    _ = Work.Pi6.MSS.cruxEps 𝕜 s *
        (Work.Cohomology.kronH 𝕜 (Work.SSSR.sSing (Work.StemsB.fibre p (p e₀))) q
          (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
              (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
          v) := by
      rw [h3]
      exact (map_smul _ _ _).trans (smul_eq_mul _ _)

/-- The class of `cruxU` is the image of the class of `z'` under the vertex identification. -/
lemma cruxU_class (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z' : ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).cycles q) :
    Work.Pi6.MSSK.chainClass 𝕜 (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) q (cruxU 𝕜 p hfib s q σ z')
        (cruxU_cycle 𝕜 p hfib s q σ z')
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom) q))
        ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).homologyπ q)) z') := by
  have hz : (ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).d q ((ComplexShape.down ℕ).next q)))
      ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).iCycles q)) z') = 0 := by
    have h := congrArg (fun (g : ( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).cycles q ⟶ ( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).X ((ComplexShape.down ℕ).next q)) =>
      (ModuleCat.Hom.hom g) z')
      (HomologicalComplex.iCycles_d (K := (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))) q ((ComplexShape.down ℕ).next q))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hy : (ModuleCat.Hom.hom (( (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).d q ((ComplexShape.down ℕ).next q)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom).f q))
        ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).iCycles q)) z')) = 0 := by
    rw [Work.SSSR.sCCMap_d_applyA (R := 𝕜) (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom q ((ComplexShape.down ℕ).next q)
      ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).iCycles q)) z')]
    rw [hz]
    exact map_zero _
  simp only [Work.Pi6.MSS.cruxU]
  rw [← Work.Pi6.MSSK.homologyMap_chainClass 𝕜 (Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom) q
      ((ModuleCat.Hom.hom (( (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)))).iCycles q)) z') hz hy,
    Work.Pi6.MSSK.chainClass_eq_homologypi (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) q z' hz]

theorem mixedEvaluation (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) :
    ∀ (s q : ℕ), ∃ (ε : 𝕜) (τ : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q ≃ₗ[𝕜]
        Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
      (ε = 1 ∨ ε = -1) ∧
      ∀ (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s)
        (hβ : β ∈ Work.Pi6.MSS.ZB 𝕜 B s)
        (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q))
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B)
        (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
        (hz : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
          ((ComplexShape.down ℕ).next q) z = 0),
        (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (Work.Pi6.MSS.pbC 𝕜 p s β) (y.1))
            (cruxChain 𝕜 p hfib s q σ z)
          = ε * (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β
                (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s)))
              * (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
                  (τ (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
                    (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
                      (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y)))
                  (cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz)) := by
  intro s q
  refine ⟨cruxEps 𝕜 s, LinearEquiv.refl 𝕜 _, ?_, ?_⟩
  · rcases Work.Pi6.MSSK.capSign_eq_one_or_neg_one (R := 𝕜) s with h | h <;>
      rcases Work.SSSR.iotaSign_or s with hi | hi <;>
      · rw [cruxEps, h, hi]
        norm_num
  · intro β hβ y σ z hz
    have h1 := Work.Pi6.MSS.eval_cup_pbC_crux 𝕜 p hfib s q β hβ
      (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1) σ z
    obtain ⟨z', hz'1, hz'2⟩ := Work.Pi6.MSSK.capLiftTriv p e₀ hfib hconn s q σ z hz
      (Work.Pi6.MSS.cruxRel p hfib s q σ z hz)
    have h3 : Work.Pi6.MSS.cruxCap 𝕜 p hfib s q σ z
        = (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p
            (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastV s) σ))).f q)) (Work.Pi6.MSS.cruxU 𝕜 p hfib s q σ z') := by
      refine (Work.Pi6.MSS.cruxCapEqFIncl p hfib s q σ z z' hz'1).trans ?_
      rfl
    have hcls : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) q))
        (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) (Work.Pi6.MSS.cruxU 𝕜 p hfib s q σ z')
          ((ComplexShape.down ℕ).next q) rfl (Work.Pi6.MSS.cruxU_cycle 𝕜 p hfib s q σ z'))
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)).hom) q))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) q)) z') :=
      Work.Pi6.MSS.cruxU_class 𝕜 p hfib s q σ z'
    have hcf : (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom)
        (Work.Pi6.MSS.cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz)
        = (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
            (Work.SSSR.sigmaVert σ)).hom)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) q))
            (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) z ((ComplexShape.down ℕ).next q) rfl hz)) := by
      simp only [Work.Pi6.MSS.cruxFibre, Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp,
        LinearMap.comp_apply, LinearMap.comp_assoc]
      show (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom)
          ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv)
            ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSSR.sigmaVert σ)).hom)
              ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) q))
                (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) z ((ComplexShape.down ℕ).next q) rfl hz))))
        = (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSSR.sigmaVert σ)).hom)
              ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) q))
                (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) z ((ComplexShape.down ℕ).next q) rfl hz))
      exact Iso.inv_hom_id_apply _ _
    have htriv : (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).hom.hom
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) q))
          (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))) (Work.Pi6.MSS.cruxU 𝕜 p hfib s q σ z')
            ((ComplexShape.down ℕ).next q) rfl (Work.Pi6.MSS.cruxU_cycle 𝕜 p hfib s q σ z')))
      = Work.Pi6.MSS.cruxEps 𝕜 s • (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom
          (Work.Pi6.MSS.cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz) := by
      rw [hcls, hz'2, hcf]
      rfl
    have h4 := Work.Pi6.MSS.evalFibre 𝕜 p e₀ hfib hconn s q y
      (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))
      (Work.Pi6.MSS.cruxU 𝕜 p hfib s q σ z') (Work.Pi6.MSS.cruxU_cycle 𝕜 p hfib s q σ z')
      (Work.Pi6.MSS.cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz) htriv
    have h4' : (show Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing E) q from y.1)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p
            (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastV s) σ))).f q)) (Work.Pi6.MSS.cruxU 𝕜 p hfib s q σ z'))
      = Work.Pi6.MSS.cruxEps 𝕜 s *
        (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
          (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
              (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
          (Work.Pi6.MSS.cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz)) := h4
    rw [h1, h3]
    -- The remaining goal is `genEval ... β ... * (cruxEps * K) = cruxEps * genEval ... β ... * K'`
    -- where `K` and `K'` are the same `kronH`-application written in the `SSS.sSing` and
    -- `SSSR.sSing` dialects; it closes by associativity/commutativity plus that definitional
    -- identification (`h4'` below is used):
    simp only [LinearEquiv.refl_apply]
    rw [h4']
    ring

end Work.Pi6.MSS
