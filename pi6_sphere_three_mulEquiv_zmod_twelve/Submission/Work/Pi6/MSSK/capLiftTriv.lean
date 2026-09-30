import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSSK.capPieceTransport
import Submission.Work.SSSR.iotaF_iota_comp_pieceIso
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `capLiftTriv` — the cap/transport lemma in the shape used by the MSS assembly

Given the cap/transport induction statement `Work.Pi6.MSSK.Aux` (proved for all `s` as
`Work.Pi6.MSSK.capAux_all`), this is its specialisation to the Eilenberg–Zilber chain
`cruxIota = ι_σ z` of a fibre cycle `z`:

the cap `θ_σ ⌢ ι_σ z` is the `fibreInc`-image of a cycle `z'` over the last vertex of `σ`,
whose trivialised class equals `capSign 𝕜 s · iotaSign s` times the trivialised class of `z`.

The sign `iotaSign s` comes from `Work.SSSR.chainStatement_zero`/`chainStatement_succ`
(the exact-sign form of the tower comparison `ι_σ`), which is applied at the proof of the
sign-carrying induction statement `Work.SSSR.ChainStatement`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Pi6.MSSK

/-- **The cap/transport lemma for the Eilenberg–Zilber chain.** -/
theorem capLiftTriv {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (s q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).d q
        ((ComplexShape.down ℕ).next q))) z = 0)
    (hcrel : Work.Pi6.MSS.CruxRel 𝕜 p hfib s q σ z) :
    ∃ z' : (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).cycles q,
      (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.fibreInc p σ)).f q)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).iCycles q)) z'))
        = Work.Cohomology.cap 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop 𝕜 p σ) q (Work.Pi6.MSS.cruxIota 𝕜 p hfib s q σ z)
      ∧
      (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastV s) σ))).hom.hom
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.SSSR.sCCMap 𝕜 (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastV s) σ)).hom) q))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ))).homologyπ q)) z'))
        = ((Work.Pi6.MSSK.capSign 𝕜 s) * ((Work.SSSR.iotaSign s : ℤ) : 𝕜)) •
          (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSS.sigmaVert σ)).hom.hom
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSS.sigmaVert σ)).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)).cyclesMk z
                ((ComplexShape.down ℕ).next q) rfl hz)) := by
  -- The cap/transport statement `Aux`, applied to the Eilenberg–Zilber chain `ι_σ z`.
  have haux := Work.Pi6.MSSK.capAux_all (R := 𝕜) p e₀ hfib hconn s q σ
    (Work.Pi6.MSS.cruxIota 𝕜 p hfib s q σ z) hcrel
  obtain ⟨z', hz'1, hz'2⟩ := haux
  refine ⟨z', hz'1, ?_⟩
  rw [hz'2]
  -- The exact-sign tower comparison: `ε_σ (class of ι_σ z) = iotaSign s · (class of z)`.
  have hall : ∀ s, Work.SSSR.ChainStatement (R := 𝕜) p hfib s (Work.SSSR.iotaSign s) := by
    intro s
    induction s with
    | zero => exact Work.SSSR.chainStatement_zero p hfib
    | succ k ih =>
      rw [Work.SSSR.iotaSign_succ]
      exact Work.SSSR.chainStatement_succ p hfib k (Work.SSSR.iotaSign k) ih
  have hcs := hall s (Work.SSSR.sigmaVert σ) σ rfl q z hz hcrel
  rw [Work.SSSR.fibreConj_rfl (R := 𝕜) p (Work.SSSR.sigmaVert σ) q] at hcs
  -- Rewrite the `serreE1PieceIso`-image of the piece class, and convert the `ℤ`-scalar
  -- into the `𝕜`-scalar of the statement.
  have hkey : (ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib s q σ).hom)
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) σ) (s + q)))
        (HomologicalComplex.cyclesMk (Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) σ)
          ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
                (Work.SSSR.sCCMap 𝕜 (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s + q)))
            (Work.Pi6.MSS.cruxIota 𝕜 p hfib s q σ z))
          ((ComplexShape.down ℕ).next (s + q)) rfl hcrel))
    = (((Work.SSSR.iotaSign s : ℤ) : 𝕜)) •
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC p (Work.SSS.sigmaVert σ)) q))
        (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC p (Work.SSS.sigmaVert σ)) z ((ComplexShape.down ℕ).next q) rfl hz)) := by
    rw [Int.cast_smul_eq_zsmul]
    exact hcs
  rw [hkey]
  exact (congrArg (fun u => Work.Pi6.MSSK.capSign 𝕜 s • u)
      (map_smul (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSS.sigmaVert σ)).hom) (((Work.SSSR.iotaSign s : ℤ) : 𝕜))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) q))
          (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) z ((ComplexShape.down ℕ).next q) rfl hz)))).trans
    (smul_smul (Work.Pi6.MSSK.capSign 𝕜 s) (((Work.SSSR.iotaSign s : ℤ) : 𝕜))
      ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (Work.SSS.sigmaVert σ)).hom)
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) q))
          (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSS.sigmaVert σ)) z ((ComplexShape.down ℕ).next q) rfl hz))))

end Work.Pi6.MSSK
