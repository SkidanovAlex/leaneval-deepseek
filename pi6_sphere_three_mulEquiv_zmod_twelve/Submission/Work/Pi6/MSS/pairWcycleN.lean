import Mathlib
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.Kgpi_d_cruxIota_sndToR
import Submission.Work.SSSR.d_sndToR_iotaTLin
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-- The `next` of the complex shape `down ℕ` is `i - 1`. -/
lemma downNext_eq_sub_one (i : ℕ) : (ComplexShape.down ℕ).next i = i - 1 := by
  cases i with
  | zero => simp [ComplexShape.next, ComplexShape.down, ComplexShape.down']
  | succ k =>
      rw [ComplexShape.next_eq' (c := ComplexShape.down ℕ) (i := k + 1) (j := k)
        (by simp [ComplexShape.down, ComplexShape.down'])]
      simp

/-- **The Eilenberg–Zilber chain over `σ`, pushed to the graded piece `Kg n`, is a cycle.**

Degree-general form of `Work.Pi6.MSS.Kgpi_d_cruxIota_sndToR` (which covers the case `n = k + 1`):
for every `n`, the image of `cruxIota 𝕜 p hfib n q σ z` under
`sCCMap 𝕜 (sndToR (sSingP p) σ) ≫ Kgπ 𝕜 p n` is a cycle of the graded piece `Kg 𝕜 p n = grF n`.

Route: `thetaPhi_mapPhiY_apply_f` identifies `Kgπ ∘ sCCMap (sndToR ·)` with
`mapPhiY ∘ pieceπ` in every degree, so the chain is `mapPhiY` applied to the class of `cruxIota`
in the σ-piece; `mapPhiY` is a chain map, and the σ-piece class of `cruxIota` is a cycle by
`Work.Pi6.MSS.cruxRel`. -/
theorem pairWcycleN_next (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p n).d (n + q)
        ((ComplexShape.down ℕ).next (n + q))))
      (Work.Pi6.MSS.pairWchainN 𝕜 p hfib n q σ z) = 0 := by
  have hstep1 :
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p n).f (n + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))
    = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)) := by
    have h := congrArg (fun (g : (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X (n + q) ⟶
          (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).X (n + q)) =>
        (ModuleCat.Hom.hom g)
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))
      (Work.SSSR.thetaPhi_mapPhiY_apply_f (R := 𝕜) (Work.SSSR.sSingP p) n (n + q) σ)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.symm
  have hstep2 :
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p n).d (n + q)
          ((ComplexShape.down ℕ).next (n + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
            (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
              (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)))
    = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ).f
        ((ComplexShape.down ℕ).next (n + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p)
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).d (n + q)
          ((ComplexShape.down ℕ).next (n + q))))
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
            (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
              (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))) :=
    Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ)
      (i := n + q) (j := (ComplexShape.down ℕ).next (n + q))
      ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
        (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))
  have hstep3 :
      (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p)
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).d (n + q)
          ((ComplexShape.down ℕ).next (n + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) n σ).f (n + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)) = 0 :=
    Work.Pi6.MSS.cruxRel (𝕜 := 𝕜) (p := p) hfib n q
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z hz
  dsimp only [Work.Pi6.MSS.pairWchainN]
  rw [hstep1, hstep2, hstep3]
  exact map_zero _

theorem pairWcycleN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (Work.Pi6.MSS.pairWchainN 𝕜 p hfib n q σ z) = 0 := by
  rw [← downNext_eq_sub_one (n + q)]
  exact pairWcycleN_next 𝕜 E B p hfib n q σ z hz

end Work.Pi6.MSS
