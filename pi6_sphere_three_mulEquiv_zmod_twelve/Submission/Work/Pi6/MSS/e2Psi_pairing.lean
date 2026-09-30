import Mathlib
import Submission.Work.Pi6.MSS.e2PsiPairDefs
import Submission.Work.Pi6.MSS.evSaux
import Submission.Work.Pi6.MSS.cruxChain_mem_A
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-- **The mixed evaluation with the explicit sign and fibre isomorphism.**  This is the precise
form of `Work.Pi6.MSS.mixedEvaluation` in which the sign `ε` is the concrete scalar
`cruxEps 𝕜 s` and the fibre automorphism `τ` is the identity: the value of the Alexander–Whitney
cup product `pbC β ⌣ y.1` on the Eilenberg–Zilber chain `cruxChain σ z`. -/
theorem mixedEvaluation_cruxEps (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing B) s)
    (hβ : β ∈ Work.Pi6.MSS.ZB 𝕜 B s)
    (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (hz : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
      ((ComplexShape.down ℕ).next q) z = 0) :
    (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (Work.Pi6.MSS.pbC 𝕜 p s β) (y.1))
        (Work.Pi6.MSS.cruxChain 𝕜 p hfib s q σ z)
      = Work.Pi6.MSS.cruxEps 𝕜 s *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β
                (σ.app (op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) *
          (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
              (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
                (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).comap
                  (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q).subtype) y))
              (Work.Pi6.MSS.cruxFibre 𝕜 p e₀ hfib hconn s q σ z hz)) := by
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
  rw [h4']
  ring

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

set_option backward.isDefEq.respectTransparency false in
/-- The lift of the Eilenberg–Zilber chain in the `(k+2)`-nd Serre subcomplex whose class in
`Kg (k+1)` is the generator cycle `pairW`. -/
abbrev pairLift (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (k q : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q) :
    (Cc 𝕜 p (k + 2)).X ((k + 1) + q) :=
  (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
    (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k + 1) + q)))
    (cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z)

set_option backward.isDefEq.respectTransparency false in
theorem pairW_val (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (k q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    (pairW 𝕜 p hfib k q σ z hz).1
      = (ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q))) (pairLift 𝕜 p hfib k q σ z) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `inclL`-image of the lift is the Eilenberg–Zilber chain `cruxChain` of the mixed
evaluation. -/
theorem inclL_pairLift (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (k q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q) :
    (ModuleCat.Hom.hom ((inclL 𝕜 p (k + 2)).f ((k + 1) + q))) (pairLift 𝕜 p hfib k q σ z)
      = cruxChain 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z := by
  change (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (sserInc (p := p) (k + 1 + 1))).f ((k + 1) + q)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
        (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k + 1) + q)))
        (cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z))
    = cruxChain 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z
  rw [Work.Pi6.MSS.sCCMap_apply_comp, Work.SSSR.sndToR_ι]
  rfl



set_option backward.isDefEq.respectTransparency false in
/-- The element of `F^{k+1}` underlying `pairElemOne`. -/
lemma pairElemOne_mem_F (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (β : ↥(ZB 𝕜 B s)) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q)) :
    (pairElemOne 𝕜 p s q β y).1 ∈ coFilt 𝕜 (sF p) s (s + q) := by
  have h1 : (pairElemOne 𝕜 p s q β y).1 ∈ (Wc 𝕜 p).F s (s + q) :=
    ((mem_pZ_one (Wc 𝕜 p) s (s + q) _).mp (pairElemOne 𝕜 p s q β y).2).1
  simpa only [Wc, serreCF_F] using h1

set_option backward.isDefEq.respectTransparency false in
/-- `pairElemOne` is the Alexander–Whitney cup product of the pullback of `β` with `y`. -/
lemma pairElemOne_val (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (β : ↥(ZB 𝕜 B s)) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q)) :
    (pairElemOne 𝕜 p s q β y).1
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p s β.1) y.1 := by
  change (Wc 𝕜 p).mul (s + 0) q (pbC 𝕜 p s β.1) y.1
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p s β.1) y.1
  change serreCup 𝕜 p (s + 0) q (pbC 𝕜 p s β.1) y.1
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p s β.1) y.1
  rw [serreCup_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The `grSecX`-lift of the class `pairW` can be replaced by the canonical lift `pairLift`: the
difference is killed by any cochain of `F^{k+1}`. -/
lemma cochainFun_grSecX_pairW (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (k q : ℕ) (β : ↥(ZB 𝕜 B (k + 1)))
    (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    cochainFun 𝕜 p ((k + 1) + q) (pairElemOne 𝕜 p (k + 1) q β y).1
        ((inclL 𝕜 p (k + 2)).f ((k + 1) + q)
          (grSecX 𝕜 p (k + 1) ((k + 1) + q) (pairW 𝕜 p hfib k q σ z hz).1))
      = cochainFun 𝕜 p ((k + 1) + q) (pairElemOne 𝕜 p (k + 1) q β y).1
        ((inclL 𝕜 p (k + 2)).f ((k + 1) + q) (pairLift 𝕜 p hfib k q σ z)) := by
  rw [pairW_val 𝕜 p hfib k q σ z hz]
  have hCπ : ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)).hom
      (grSecX 𝕜 p (k + 1) ((k + 1) + q)
          ((ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
            (pairLift 𝕜 p hfib k q σ z))
        - pairLift 𝕜 p hfib k q σ z) = 0 := by
    simp only [map_sub, Kgπ_grSecX_apply, sub_self]
  have h0 := ker_Kgπ_inclL_eq_zero 𝕜 p (k + 1) ((k + 1) + q) (coFiltAnn 𝕜 (sF p))
    (cochainFun 𝕜 p ((k + 1) + q) (pairElemOne 𝕜 p (k + 1) q β y).1)
    (pairElemOne_mem_F 𝕜 p (k + 1) q β y)
    (grSecX 𝕜 p (k + 1) ((k + 1) + q)
        ((ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
          (pairLift 𝕜 p hfib k q σ z))
      - pairLift 𝕜 p hfib k q σ z) hCπ
  have hsum : grSecX 𝕜 p (k + 1) ((k + 1) + q)
        ((ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
          (pairLift 𝕜 p hfib k q σ z))
      = (grSecX 𝕜 p (k + 1) ((k + 1) + q)
            ((ModuleCat.Hom.hom ((Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
              (pairLift 𝕜 p hfib k q σ z))
          - pairLift 𝕜 p hfib k q σ z) + pairLift 𝕜 p hfib k q σ z := by abel
  rw [hsum, map_add, map_add, h0, zero_add]

theorem e2Psi_pairing (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (k q : ℕ)
    (β : ↥(ZB 𝕜 B (k + 1))) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSS.sigmaVert (Work.SSSR.sigHat σ))).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    evZ 𝕜 p (k + 1) ((k + 1) + q) (coFiltAnn 𝕜 (sF p))
        (pairElemOne 𝕜 p (k + 1) q β y)
        ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (k + 1)) ((k + 1) + q)).mkQ
          (pairW 𝕜 p hfib k q σ z hz))
      = pairRHS 𝕜 p e₀ hfib hconn k q β y σ z hz := by
  have h1 := evZ_apply 𝕜 p (k + 1) ((k + 1) + q) (coFiltAnn 𝕜 (sF p))
    (pairElemOne 𝕜 p (k + 1) q β y) (pairW 𝕜 p hfib k q σ z hz)
  rw [h1, cochainFun_grSecX_pairW 𝕜 p hfib k q β y σ z hz]
  rw [inclL_pairLift 𝕜 p hfib k q σ z]
  have hmain : cochainFun 𝕜 p ((k + 1) + q) (pairElemOne 𝕜 p (k + 1) q β y).1
        (cruxChain 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z)
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p (k + 1) β.1) y.1
        (cruxChain 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat σ) z) := by
    rw [pairElemOne_val]
    rfl
  rw [hmain, pairRHS]
  exact mixedEvaluation_cruxEps 𝕜 E B p e₀ hfib hconn (k + 1) q β.1 β.2 y
    (Work.SSSR.sigHat σ) z hz

end

end Work.Pi6.MSS
