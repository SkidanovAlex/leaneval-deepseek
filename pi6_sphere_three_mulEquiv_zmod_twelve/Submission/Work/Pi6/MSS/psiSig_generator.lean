import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.SSSR.serreE1Main
import Submission.Work.SSSR.serreE1Chain
import Submission.Work.SSSR.kF_psiCoef_gen
import Submission.Work.SSSR.faceB_grFi_nondeg
import Submission.Work.SSSR.iotaT_eq_iotaTLin
import Submission.Work.SSSR.iotaF_iota_comp_pieceIso
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- For an isomorphism `e : M ≅ N` of `R`-modules, `e⁻¹ ∘ e = id` on elements. -/
private lemma iso_inv_hom_apply {𝕜 : Type} [Ring 𝕜] {M N : ModuleCat 𝕜} (e : M ≅ N) (y : M) :
    (ModuleCat.Hom.hom e.inv) ((ModuleCat.Hom.hom e.hom) y) = y := by
  have h := Iso.hom_inv_id e
  have h2 := congrArg (fun (f : M ⟶ M) => (ModuleCat.Hom.hom f) y) h
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h2

/-- **The `σ`-component of the first-page comparison map on the canonical generators.**

For a Serre fibration `p : E → B` with simply connected base, there is a sign family `c n = ±1` such
that, for every nondegenerate `(k+1)`-simplex `σ` of the base and every cycle `z` of the fibre over
the first vertex of `σ`, the `σ`-component of `PsiSig` sends the class of `z` (trivialised along
`triv`) to `c (k+1)` times the class of the Eilenberg–Zilber chain `ι_σ z` pushed to the associated
graded piece of the Serre filtration.

Route: `Sigma_ι_comp_PsiSig` computes the `σ`-component of `PsiSig` as
`PsiCoef σ ≫ H(mapPhiY σ)`.  `PsiCoef σ = triv.symm ≪≫ pieceIso.symm`, so on `triv.hom` of a fibre
class it is `(serreE1PieceIso σ).inv`, and `pieceInv_of_pieceAlpha` (the inverse form of the sign
spec `PieceAlpha`, available from `exists_pieceAlpha`) evaluates this as `c (k+1) • [ι_σ z]`.
Finally `H(mapPhiY σ)` of the piece class of `ι_σ z` is the class of the chain-level image
`grFι 𝕜 (sCCMap 𝕜 (sndToR σ)) (ι_σ z)`, which is `thetaPhi_mapPhiY_apply_f` combined with
`homologyMap_cyclesMk`. -/
theorem psiSig_generator (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) :
    ∃ c : ℕ → ℤ, (∀ n : ℕ, c n = 1 ∨ c n = -1) ∧
      ∀ (k q : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1))
        (z : (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X q)
        (hz : (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d q
          ((ComplexShape.down ℕ).next q) z = 0)
        (hcyc : (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k+1)).d ((k+1)+q)
          ((ComplexShape.down ℕ).next ((k+1)+q))
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k+1)).f ((k+1)+q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
                (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k+1)+q)))
                (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k+1) q (Work.SSSR.sigHat σ) z))) = 0),
        (ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
          ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) σ)
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                  ((ComplexShape.down ℕ).next q) rfl hz))))
        = c (k+1) • (ModuleCat.Hom.hom
            ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k+1)).homologyπ ((k+1)+q))
            ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k+1)).cyclesMk
              ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k+1)).f ((k+1)+q)))
                ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
                  (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k+1)+q)))
                  (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k+1) q (Work.SSSR.sigHat σ) z)))
              ((ComplexShape.down ℕ).next ((k+1)+q)) rfl hcyc)) := by
  obtain ⟨c, hc1, hal⟩ := Work.SSSR.exists_pieceAlpha (R := 𝕜) p hfib
  refine ⟨c, hc1, ?_⟩
  intro k q σ z hz hcyc
  -- the piece cyclicity of the Eilenberg–Zilber chain
  have hy := Work.SSSR.IotaChain.iotaF_cycle (R := 𝕜) p hfib (k+1) q
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z hz
  -- the inverse form of the sign spec at `(k+1, q)`
  have hpinv := Work.SSSR.pieceInv_of_pieceAlpha (R := 𝕜) p hfib c hc1 hal (k+1) q
      (Work.SSSR.sigHat σ) z hz hy
  -- the chain-level description of `mapPhiY σ (iotaF σ z)`
  have hchain : (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k+1) σ).f ((k+1)+q)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
          (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl q)) z)
      = (ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k+1)).f ((k+1)+q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k+1)+q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k+1) q (Work.SSSR.sigHat σ) z)) := by
    have h1 : (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (Work.SSSR.sigHat σ) rfl q)) z
      = (ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) (k+1) σ).f ((k+1)+q)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
            (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl q)) z) := rfl
    rw [h1]
    exact Work.SSSR.thetaPhi_mapPhiY_apply_f_elem (Work.SSSR.sSingP p) (k+1) ((k+1)+q) σ _
  -- the cycle condition for `mapPhiY σ (iotaF σ z)`
  have hx' : (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k+1)).d ((k+1)+q)
        ((ComplexShape.down ℕ).next ((k+1)+q))
        ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k+1) σ).f ((k+1)+q)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
            (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl q)) z)) = 0 := by
    rw [hchain]
    exact hcyc
  -- `H(mapPhiY σ)` of the piece class of `ι_σ z`
  have hmap : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k+1) σ) ((k+1)+q)))
        ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).homologyπ ((k+1)+q)
          ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).cyclesMk
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
              (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl q)) z)
            ((ComplexShape.down ℕ).next ((k+1)+q)) rfl hy))
      = (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k+1)).homologyπ ((k+1)+q)
          ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k+1)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) (k+1)).f ((k+1)+q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
                (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((k+1)+q)))
                (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k+1) q (Work.SSSR.sigHat σ) z)))
            ((ComplexShape.down ℕ).next ((k+1)+q)) rfl hcyc) :=
    ((Work.SSSR.homologyMap_cyclesMk
        (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k+1) σ) (hj := rfl)
        (x := (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
          (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl q)) z)
        hy hx').symm).trans
      (Work.SSSR.homologyπ_cyclesMk_eq (hj := rfl) hchain hx' hcyc)
  -- `PsiCoef σ` on `triv.hom` of a fibre class is `c (k+1)` times the piece class of `ι_σ z`
  have hpsi : (ModuleCat.Hom.hom (Work.SSSR.PsiCoef (R := 𝕜) p e₀ hfib hconn q (k+1) σ).hom)
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz)))
      = c (k+1) • (Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).homologyπ ((k+1)+q)
          ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.sigHat σ)).cyclesMk
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
              (k+1) (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl q)) z)
            ((ComplexShape.down ℕ).next ((k+1)+q)) rfl hy) := by
    have hcoe : (ModuleCat.Hom.hom (Work.SSSR.PsiCoef (R := 𝕜) p e₀ hfib hconn q (k+1) σ).hom)
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz)))
        = (ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib (k+1) q (Work.SSSR.sigHat σ)).inv)
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).inv)
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
                ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ q))
                  ((Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
                    ((ComplexShape.down ℕ).next q) rfl hz)))) := rfl
    rw [hcoe, iso_inv_hom_apply]
    exact hpinv
  -- assembly
  rw [← ModuleCat.comp_apply (CategoryTheory.Limits.Sigma.ι
        (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) => Work.SSSR.coefM (R := 𝕜) p e₀ q) σ)
        (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)) _]
  rw [Work.SSSR.Sigma_ι_comp_PsiSig (R := 𝕜) p e₀ hfib hconn q (k+1) σ]
  rw [ModuleCat.comp_apply]
  rw [hpsi, map_zsmul, hmap]

end Work.Pi6.MSS
