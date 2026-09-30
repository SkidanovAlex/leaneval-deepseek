import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.Pi6.MSS.E2cfkHorn
import Submission.Work.Pi6.MSS.pieceHorn_lift
import Submission.Work.Pi6.MSS.transport_chain
import Submission.Work.Pi6.MSS.horn_to_fibre
import Submission.Work.Pi6.MSS.fibre_to_pullback
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.Pi6.MSSK.lastPathExists
import Submission.Work.Pi6.MSSK.edgePieceToPullback
import Submission.Work.SSSR.transportIsoPathChain
import Submission.Work.SSSR.singPullbackIso_exists
import Submission.Work.Pi6.MSSK.VertexBridges
import Submission.Work.Pi6.MSSK.TransportAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section


/-! ## Auxiliary spelling lemmas for the degenerate case `t = 0` -/

lemma stdSimplex_map_id (n : SimplexCategory) :
    SSet.stdSimplex.map (𝟙 n) = 𝟙 (SSet.stdSimplex.obj n) := by
  simp

lemma lastEdgeHom_zero : Work.Pi6.MSSK.lastEdgeHom 0 = 𝟙 (SimplexCategory.mk 1) := by
  ext i
  fin_cases i <;> rfl

lemma lastEdge_zero : Work.Pi6.MSSK.lastEdge 0 =
    𝟙 ((SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0})) := by
  rw [Work.Pi6.MSSK.lastEdge, lastEdgeHom_zero, stdSimplex_map_id]

lemma lastV_zero : Work.Pi6.MSSK.lastV 0 =
    𝟙 ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})) := by
  rw [Work.Pi6.MSSK.lastV]
  rw [show (Fin.last 0 : Fin 1) = 0 from rfl, SimplexCategory.const_eq_id]
  simp

lemma lastV_one_eq_delta : Work.Pi6.MSSK.lastV 1 = SSet.stdSimplex.δ (n := 0) (0 : Fin 2) := by
  rw [Work.Pi6.MSSK.lastV]
  rw [show (Fin.last 1 : Fin 2) = 1 from rfl]
  rw [show SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)
      = SSet.stdSimplex.δ (n := 0) (0 : Fin 2) from by
    rw [← SimplexCategory.δ_zero_eq_const]; rfl]

lemma lastVertMap_eq_lastV : Work.Pi6.MSS.lastVertMap = Work.Pi6.MSSK.lastV 1 :=
  lastV_one_eq_delta.symm

lemma lastVertMap_eq_const : Work.Pi6.MSS.lastVertMap = SSet.const Work.SSSR.vtx1S1 := by
  rw [lastVertMap_eq_lastV, Work.Pi6.MSSK.lastV_one_eq_const]

lemma lastVertMap_comp_vertLiftI : Work.Pi6.MSS.lastVertMap ≫ Work.SSSR.vertLiftI
    = SSet.const (TopCat.toSSetObj₀Equiv.symm (1 : unitInterval)) := by
  rw [lastVertMap_eq_lastV, Work.Pi6.MSSK.lastV_comp_vertLiftI]

lemma ssetVertex_one : Work.SSSR.ssetVertex 1 = Work.SSSR.vtx0S1 := by
  rw [Work.Pi6.MSSK.vtx0S1_eq_obj]

lemma vertLiftI_app_ssetVertex_one :
    (ConcreteCategory.hom (Work.SSSR.vertLiftI.app (Opposite.op (SimplexCategory.mk 0))))
        (Work.SSSR.ssetVertex 1)
      = TopCat.toSSetObj₀Equiv.symm (0 : unitInterval) := by
  rw [ssetVertex_one, Equiv.eq_symm_apply, Work.SSSR.toSSetObj₀Equiv_vertLiftI_vtx0]

lemma const_ssetVertex_comp_vertLiftI (X : SSet.{0}) :
    (SSet.const (Work.SSSR.ssetVertex 1) :
        X ⟶ (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0})) ≫ Work.SSSR.vertLiftI
      = (SSet.const (TopCat.toSSetObj₀Equiv.symm (0 : unitInterval)) :
          X ⟶ Work.SSSR.sSing unitInterval) := by
  rw [SSet.const_comp, vertLiftI_app_ssetVertex_one]

/-! ## The inclusion of the fibre over the first vertex into the pullback `T_σ` -/

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The inclusion of the fibre over the first vertex of `σ` into the pullback `T_σ`**, with its
two projections (in the `SSSR` spelling of the two singular simplicial sets). -/
theorem kappa_exists (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ∃ κ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)) ⟶
        Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ,
      (κ ≫ pullback.fst σ (Work.SSSR.sSingP p) = SSet.const (Work.SSSR.ssetVertex 1)) ∧
      (κ ≫ pullback.snd σ (Work.SSSR.sSingP p)
        = Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))) := by
  have hcond : SSet.const (Work.SSSR.ssetVertex 1) ≫ σ
      = Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))
        ≫ Work.SSSR.sSingP p := by
    have h1 : σ.app (Opposite.op (SimplexCategory.mk 0)) (Work.SSSR.ssetVertex 1)
        = TopCat.toSSetObj₀Equiv.symm (Work.SSSR.sigmaVert σ) := by
      rw [Equiv.eq_symm_apply]
      exact Work.SSSR.sigmaVert_app_ssetVertex σ
    rw [SSet.const_comp, Work.SSSR.sSingP_fibreIncl_comp, h1]
  exact ⟨pullback.lift (SSet.const (Work.SSSR.ssetVertex 1))
    (Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))) hcond,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-! ## The path realising a `1`-simplex -/

theorem exists_path_sigmaVert_lastVert {B : Type} [TopologicalSpace B]
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    ∃ γ : Path (Work.SSSR.sigmaVert σ) (Work.Pi6.MSS.E2cfk.lastVert σ),
      (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = SSet.yonedaEquiv σ := by
  obtain ⟨γ, hγ⟩ := Work.Pi6.MSSK.lastPathExists (B := B) 0 σ
  have hsrc : Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 0
        ≫ SSet.stdSimplex.δ (n := 0) (Fin.last (0 + 1)) ≫ σ) = Work.SSSR.sigmaVert σ := by
    rw [lastV_zero, Category.id_comp]
    exact Work.SSSR.sigmaVert_face (Fin.last (0 + 1)) (by decide) σ
  have htgt : Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV (0 + 1) ≫ σ)
      = Work.Pi6.MSS.E2cfk.lastVert σ := by
    rw [lastV_one_eq_delta]
    change Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := 0) 0 ≫ σ)
      = Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := 0) 0 ≫ σ)
    unfold Work.SSSR.sigmaVert Work.SSS.sigmaVert
    rfl
  have hγ' : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = SSet.yonedaEquiv σ := by
    rw [hγ, Work.Pi6.MSSK.lastEdgeSimplex, Work.Pi6.MSSK.lastEdge, lastEdgeHom_zero,
      stdSimplex_map_id, Category.id_comp]
  exact ⟨⟨γ.toContinuousMap, γ.source'.trans hsrc, γ.target'.trans htgt⟩, hγ'⟩

theorem vertLiftI_comp_sSingP {B : Type} [TopologicalSpace B]
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert σ) (Work.Pi6.MSS.E2cfk.lastVert σ))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = SSet.yonedaEquiv σ) :
    Work.SSSR.vertLiftI ≫ Work.SSSR.sSingP γ.toContinuousMap = σ := by
  refine Equiv.injective SSet.yonedaEquiv ?_
  rw [SSet.yonedaEquiv_comp]
  rw [show SSet.yonedaEquiv Work.SSSR.vertLiftI = Work.SSSR.lambda1 from
    Equiv.apply_symm_apply SSet.yonedaEquiv Work.SSSR.lambda1]
  rw [hγ]

end

theorem transportChainTriv {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.SSSR.sigmaVert σ)).X q)
    (hz : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fibCC 𝕜 p
        (Work.SSSR.sigmaVert σ)).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    ∃ (w : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).X q)
      (hw : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fibCC 𝕜 p
          (Work.Pi6.MSS.E2cfk.lastVert σ)).d q ((ComplexShape.down ℕ).next q))) w = 0)
      (c : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).X (q + 1)),
      (∃ c' : (((Work.Pi6.MSS.E2cfk.sser p 2).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜)).X (q + 1),
        (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.sserInc 𝕜 p 2).f (q + 1))) c' = c)
      ∧ (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert σ)).f q)) z
          - (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).f q)) w
          = (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.ECC 𝕜 E).d (q + 1) q)) c
      ∧ (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSSR.sigmaVert σ)).hom.hom
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert σ)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert σ)).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz))
        = (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.Pi6.MSS.E2cfk.lastVert σ)).hom.hom
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.Pi6.MSS.E2cfk.lastVert σ)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (Work.Pi6.MSS.E2cfk.lastVert σ)).cyclesMk w
              ((ComplexShape.down ℕ).next q) rfl hw)) := by
  classical
  -- `hz` written with the predecessor index
  have hzq : (ModuleCat.Hom.hom ((Work.SSSR.sChains 𝕜
      (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).d q (q - 1))) z = 0 := by
    rw [← Work.Pi6.MSSK.nextDownEq q]
    exact hz
  -- the path realising `σ`
  obtain ⟨γ, hγ⟩ := exists_path_sigmaVert_lastVert (B := B) σ
  have hγσ : Work.SSSR.vertLiftI ≫ Work.SSSR.sSingP γ.toContinuousMap = σ :=
    vertLiftI_comp_sSingP σ γ hγ
  -- the inclusion of the fibre over the first vertex into `T_σ`
  obtain ⟨κ, hκfst, hκsnd⟩ := kappa_exists p σ
  -- the push-forward of `z` into the pullback `T_σ`
  set z₁ : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q :=
    ((Work.SSSR.sChainMap 𝕜 κ).f q).hom z with hz₁def
  have hz₁ : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d q (q - 1) z₁ = 0 := by
    rw [hz₁def, Work.Pi6.MSS.chainMap_d_apply (Work.SSSR.sChainMap 𝕜 κ) q (q - 1) z, hzq]
    exact map_zero _
  -- the horn replacement of the cycle `z₁`
  obtain ⟨z', c1, hz'cyc, hsplit⟩ :=
    Work.Pi6.MSS.pieceHorn_lift_cycle 𝕜 E B p hfib q σ z₁ hz₁
  -- the horn-to-fibre isomorphism
  obtain ⟨ψ, hψiso, hψ⟩ := Work.Pi6.MSS.horn_to_fibre p σ
  -- `hz'cyc` rewritten in the spelling in which the horn is the domain of `ψ`
  have hz'cyc' : (Work.SSSR.sChains 𝕜
        ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).toSSet)).d q (q - 1) z' = 0 := hz'cyc
  -- the transported cycle
  set w : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).X q :=
    ((Work.SSSR.sChainMap 𝕜 ψ).f q).hom z' with hwdef
  have hwq : (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).d q (q - 1) w = 0 := by
    rw [hwdef, Work.Pi6.MSS.chainMap_d_apply (Work.SSSR.sChainMap 𝕜 ψ) q (q - 1) z', hz'cyc']
    exact map_zero _
  have hw : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fibCC 𝕜 p
      (Work.Pi6.MSS.E2cfk.lastVert σ)).d q ((ComplexShape.down ℕ).next q))) w = 0 := by
    rw [Work.Pi6.MSSK.nextDownEq q]
    exact hwq
  -- ## the chain relation
  have hfInclBr : Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert σ)
      = Work.SSSR.sChainMap 𝕜 (Work.SSSR.sSingP
          (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ))) := rfl
  have hchain1 : Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert σ)
      = Work.SSSR.sChainMap 𝕜 κ
        ≫ Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p)) :=
    hfInclBr.trans ((congrArg (fun f => Work.SSSR.sChainMap 𝕜 f) hκsnd).symm.trans
      (Work.SSSR.sChainMap_comp 𝕜 κ (pullback.snd σ (Work.SSSR.sSingP p))).symm)
  have hA : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert σ)).f q)) z
      = (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q)) z₁ := by
    have h := congrArg (fun (φ : Work.Pi6.MSS.E2cfk.fibCC 𝕜 p (Work.SSSR.sigmaVert σ) ⟶
        Work.Pi6.MSS.E2cfk.ECC 𝕜 E) => (ModuleCat.Hom.hom (φ.f q)) z) hchain1
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [hz₁def]
    exact h
  have hψR : ψ ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p (Work.Pi6.MSS.E2cfk.lastVert σ))
      = (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι ≫ pullback.snd σ (Work.SSSR.sSingP p) := hψ
  have hchain2 : Work.SSSR.sChainMap 𝕜 ψ ≫ Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)
      = Work.SSSR.sChainMap 𝕜 ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ)).ι
        ≫ Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p)) := by
    have hiff : Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)
        = Work.SSSR.sChainMap 𝕜 (Work.SSS.sSingP
            (Work.StemsB.fibreIncl p (Work.Pi6.MSS.E2cfk.lastVert σ))) := rfl
    rw [hiff, Work.SSSR.sChainMap_comp, Work.SSSR.sChainMap_comp, hψR]
  have hB : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).f q)) w
      = (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
          ((ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜
            ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ)).ι).f q)) z') := by
    have h := congrArg (fun (φ : Work.SSSR.sChains 𝕜
        ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ)).toSSet ⟶
        Work.Pi6.MSS.E2cfk.ECC 𝕜 E) => (ModuleCat.Hom.hom (φ.f q)) z') hchain2
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [hwdef]
    exact h
  have hsub : z₁ - ((Work.SSSR.sChainMap 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q).hom z'
      = ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q).hom c1 :=
    (congrArg (fun x => x - ((Work.SSSR.sChainMap 𝕜
        ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q).hom z') hsplit).trans
      (add_sub_cancel_left _ _)
  set c : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).X (q + 1) :=
    ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f (q + 1)).hom c1 with hcdef
  have hrel : (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert σ)).f q)) z
        - (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).f q)) w
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.ECC 𝕜 E).d (q + 1) q)) c := by
    calc (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.SSSR.sigmaVert σ)).f q)) z
          - (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.fIncl 𝕜 p (Work.Pi6.MSS.E2cfk.lastVert σ)).f q)) w
        = (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q)) z₁
          - (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
              (((ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜
                ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ)).ι).f q)) z')) := by
          rw [hA, hB]
      _ = (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
            (z₁ - ((ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜
              ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q)) z')) := (map_sub _ _ _).symm
      _ = (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f q))
            (((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q).hom c1) := by
          rw [hsub]
      _ = (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.ECC 𝕜 E).d (q + 1) q)) c := by
          rw [hcdef]
          exact (Work.Pi6.MSS.chainMap_d_apply
            (Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))) (q + 1) q c1).symm
  have hF2 : ∃ c' : (((Work.Pi6.MSS.E2cfk.sser p 2).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜)).X (q + 1),
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.E2cfk.sserInc 𝕜 p 2).f (q + 1))) c' = c := by
    refine ⟨((Work.SSSR.sChainMap 𝕜 (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2
      (Work.Pi6.MSS.sndToSerre_lift p σ))).f (q + 1)).hom c1, ?_⟩
    have hcp : ((Work.SSSR.sChainMap 𝕜 (Work.Pi6.MSS.E2cfk.sser p 2).ι).f (q + 1)).hom
          (((Work.SSSR.sChainMap 𝕜 (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2
            (Work.Pi6.MSS.sndToSerre_lift p σ))).f (q + 1)).hom c1)
        = ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSS.sSingP p))).f (q + 1)).hom c1 :=
      Work.Pi6.MSS.chainMap_comp_apply (𝕜 := 𝕜)
        (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2 (Work.Pi6.MSS.sndToSerre_lift p σ))
        (Work.Pi6.MSS.E2cfk.sser p 2).ι (q + 1) c1
    have hcpR : ((Work.SSSR.sChainMap 𝕜 (Work.Pi6.MSS.E2cfk.sser p 2).ι).f (q + 1)).hom
          (((Work.SSSR.sChainMap 𝕜 (Work.SSS.sndToSerre (Work.SSS.sSingP p) σ 2
            (Work.Pi6.MSS.sndToSerre_lift p σ))).f (q + 1)).hom c1)
        = ((Work.SSSR.sChainMap 𝕜 (pullback.snd σ (Work.SSSR.sSingP p))).f (q + 1)).hom c1 := hcp
    have hsin : (Work.Pi6.MSS.E2cfk.sserInc 𝕜 p 2)
        = Work.SSSR.sChainMap 𝕜 (Work.Pi6.MSS.E2cfk.sser p 2).ι := Work.Pi6.MSS.sserInc_eq p 2
    rw [hsin]
    exact hcpR.trans hcdef.symm
  -- ## the comparison with the pullback along the path
  obtain ⟨e, he₁, he₂⟩ := Work.SSSR.singPullbackIso_exists p γ.toContinuousMap
  have hcompat : pullback.snd σ (Work.SSSR.sSingP p) ≫ Work.SSSR.sSingP p
      = (pullback.fst σ (Work.SSSR.sSingP p) ≫ Work.SSSR.vertLiftI)
        ≫ Work.SSSR.sSingP γ.toContinuousMap := by
    rw [Category.assoc, hγσ]
    exact pullback.condition.symm
  set L : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶
      pullback (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap) :=
    show pullback σ (Work.SSSR.sSingP p) ⟶
        pullback (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap) from
      pullback.lift (pullback.snd σ (Work.SSSR.sSingP p))
        (pullback.fst σ (Work.SSSR.sSingP p) ≫ Work.SSSR.vertLiftI) hcompat with hLdef
  set Φ : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶
      Work.SSSR.sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) :=
    show pullback σ (Work.SSSR.sSingP p) ⟶
        Work.SSSR.sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) from
      L ≫ e.inv with hΦdef
  have he₁' : e.inv ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackFst p γ.toContinuousMap)
      = pullback.fst (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap) := by
    rw [← he₁, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hP1 : Φ ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackFst p γ.toContinuousMap)
      = pullback.snd σ (Work.SSSR.sSingP p) := by
    rw [hΦdef, hLdef, Category.assoc, he₁', pullback.lift_fst]
  have hP2 : κ ≫ Φ = Work.SSSR.sSingP (Work.SSSR.inclSource p γ) := by
    refine (cancel_mono e.hom).mp ?_
    rw [hΦdef, hLdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hκsnd]
      rw [Category.assoc, he₁]
      simp only [Work.SSSR.sSingP]
      rw [← Functor.map_comp, Work.SSSR.inclSource_comp_pullbackFst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hκfst,
        const_ssetVertex_comp_vertLiftI (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))]
      rw [Category.assoc, he₂]
      simp only [Work.SSSR.sSingP]
      rw [← Functor.map_comp, Work.SSSR.inclSource_comp_pullbackSnd, TopCat.toSSet_map_const]
  have hψRR : ψ ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.Pi6.MSS.E2cfk.lastVert σ))
      = (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι ≫ pullback.snd σ (Work.SSSR.sSingP p) := hψ
  haveI : IsIso (Work.Pi6.MSS.hornLift (Work.SSS.sSingP p) σ) :=
    Work.Pi6.MSS.isIso_hornLift (Work.SSS.sSingP p) σ
  have hhorn : (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι
        ≫ pullback.fst σ (Work.SSS.sSingP p) ≫ Work.SSSR.vertLiftI
      = SSet.const (TopCat.toSSetObj₀Equiv.symm (1 : unitInterval)) := by
    refine (cancel_epi (Work.Pi6.MSS.hornLift (Work.SSS.sSingP p) σ)).mp ?_
    have h1 : Work.Pi6.MSS.hornLift (Work.SSS.sSingP p) σ
          ≫ ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι
              ≫ pullback.fst σ (Work.SSS.sSingP p) ≫ Work.SSSR.vertLiftI)
        = Work.Pi6.MSS.vertMap (Work.SSS.sSingP p) σ
          ≫ (pullback.fst σ (Work.SSS.sSingP p) ≫ Work.SSSR.vertLiftI) := by
      rw [← Category.assoc, Work.Pi6.MSS.hornLift_ι]
    rw [h1, ← Category.assoc, Work.Pi6.MSS.vertMap_fst]
    rw [Category.assoc, lastVertMap_comp_vertLiftI, SSet.comp_const]
    rw [SSet.comp_const]
  have hhornR : (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι
        ≫ pullback.fst σ (Work.SSSR.sSingP p) ≫ Work.SSSR.vertLiftI
      = SSet.const (TopCat.toSSetObj₀Equiv.symm (1 : unitInterval)) := hhorn
  have hP3 : (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι ≫ Φ
      = ψ ≫ Work.SSSR.sSingP (Work.SSSR.inclTarget p γ) := by
    refine (cancel_mono e.hom).mp ?_
    rw [hΦdef, hLdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← hψRR]
      rw [Category.assoc, Category.assoc, he₁]
      simp only [Work.SSSR.sSingP]
      rw [← Functor.map_comp, Work.SSSR.inclTarget_comp_pullbackFst]
    · rw [Category.assoc, pullback.lift_snd, hhornR]
      rw [Category.assoc, Category.assoc, he₂]
      simp only [Work.SSSR.sSingP]
      rw [← Functor.map_comp, Work.SSSR.inclTarget_comp_pullbackSnd, TopCat.toSSet_map_const,
        SSet.comp_const]
  -- ## the chain in the pullback along the path realising the transport
  set η : (Work.SSSR.Stems.hChain (R := 𝕜) (Work.SSSR.StemsB.Pullback p γ.toContinuousMap)).X (q + 1) :=
    ((Work.SSSR.sChainMap 𝕜 Φ).f (q + 1)).hom c1 with hηdef
  have hsubR : z₁ - ((Work.SSSR.sChainMap 𝕜
        ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q).hom z'
      = ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q).hom c1 :=
    hsub
  have hΦκ : Work.SSSR.sChainMap 𝕜 κ ≫ Work.SSSR.sChainMap 𝕜 Φ
      = Work.SSSR.sourceChainMap (R := 𝕜) p γ :=
    (Work.SSSR.sChainMap_comp 𝕜 κ Φ).trans
      ((congrArg (fun f => Work.SSSR.sChainMap 𝕜 f) hP2).trans rfl)
  have hΦι : Work.SSSR.sChainMap 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι
        ≫ Work.SSSR.sChainMap 𝕜 Φ
      = Work.SSSR.sChainMap 𝕜 ψ ≫ Work.SSSR.targetChainMap (R := 𝕜) p γ :=
    (Work.SSSR.sChainMap_comp 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι Φ).trans
      ((congrArg (fun f => Work.SSSR.sChainMap 𝕜 f) hP3).trans
        (Work.SSSR.sChainMap_comp 𝕜 ψ
          (Work.SSSR.sSingP (Work.SSSR.inclTarget p γ))).symm)
  have hη : (ModuleCat.Hom.hom ((Work.SSSR.Stems.hChain (R := 𝕜)
        (Work.SSSR.StemsB.Pullback p γ.toContinuousMap)).d (q + 1) q)) η
      = (ModuleCat.Hom.hom ((Work.SSSR.sourceChainMap (R := 𝕜) p γ).f q)) z
        - (ModuleCat.Hom.hom ((Work.SSSR.targetChainMap (R := 𝕜) p γ).f q)) w := by
    rw [hηdef, Work.Pi6.MSS.chainMap_d_apply (Work.SSSR.sChainMap 𝕜 Φ) (q + 1) q c1, ← hsubR,
      map_sub]
    congr 1
    · have h := congrArg (fun (φ : Work.SSSR.Stems.hChain (R := 𝕜)
          (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)) ⟶
          Work.SSSR.Stems.hChain (R := 𝕜) (Work.SSSR.StemsB.Pullback p γ.toContinuousMap)) =>
            (ModuleCat.Hom.hom (φ.f q)) z) hΦκ
      rw [hz₁def]
      exact h
    · have h := congrArg (fun (φ : Work.SSSR.sChains 𝕜
          ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).toSSet ⟶
          Work.SSSR.Stems.hChain (R := 𝕜) (Work.SSSR.StemsB.Pullback p γ.toContinuousMap)) =>
            (ModuleCat.Hom.hom (φ.f q)) z') hΦι
      rw [hwdef]
      exact h
  -- ## the transport relation and the trivialisation
  have hT := Work.SSSR.transportIsoPathChain (R := 𝕜) p hfib γ q z hz w hw η hη
  have htriv := Work.SSSR.triv_transport (R := 𝕜) p e₀ hfib hconn q γ
  have htriv_el : (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
        (Work.Pi6.MSS.E2cfk.lastVert σ)).hom)
        ((ModuleCat.Hom.hom (Work.SSSR.transportIsoPath p hfib γ q).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert σ)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert σ)).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz)))
      = (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert σ)).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert σ)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert σ)).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz)) := by
    have h := congrArg (fun (f : Work.SSSR.PiS.HZ 𝕜 (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)) q ≅
        Work.SSSR.coefM p e₀ q) =>
          f.hom.hom ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert σ)).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert σ)).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz))) htriv
    simpa only [Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply] using h
  refine ⟨w, hw, c, hF2, hrel, ?_⟩
  have hstep := congrArg (fun (y : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.Pi6.MSS.E2cfk.lastVert σ)).homology q) =>
      (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.Pi6.MSS.E2cfk.lastVert σ)).hom.hom y) hT
  exact htriv_el.symm.trans hstep


end Work.Pi6.MSS
