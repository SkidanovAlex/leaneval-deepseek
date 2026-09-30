import Mathlib
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.cruxRel
import Submission.Work.SSSR.d_sndToR_iotaTLin
import Submission.Work.SSSR.iotaT_eq_iotaTLin
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

set_option maxHeartbeats 2000000

/-- **The graded piece class of the `sndToR`-lift of the Eilenberg–Zilber chain is a cycle.**

For a nondegenerate `(k+1)`-simplex `y` of `Sing B`, the chain
`C := (sCCMap 𝕜 (sndToR (sSingP p) y)).f ((k+1)+q) (cruxIota 𝕜 p hfib (k+1) q (sigHat y) z)` of the
`(k+2)`-nd Serre subcomplex `C_*(A_{k+2})` (it is the canonical lift of `cruxChain`), pushed to the
graded piece `Kg 𝕜 p (k+1) = grF (serF 𝕜 (sSingP p)) (k+1)` by `Kgπ`, is a cycle.

Route: `Kgπ` is a chain map, so `d (Kgπ C) = Kgπ (d C)`; `CruxDefs`'s `cruxIota` is `iotaT` on `z`,
which is `iotaTLin p hfib k q b (sigHat y) rfl z` by `Work.SSSR.iotaT_eq_iotaTLin`; and
`Work.SSSR.d_sndToR_iotaTLin` computes
`d C = (incF (Fc p) k).f (k+q) (faceSum p hfib k q b (sigHat y) rfl z)`; finally
`incF (serF 𝕜 (sSingP p)) k ≫ grFι 𝕜 (sSingP p) (k+1) = 0`
(`Work.SSSR.incF_comp_grFι`, with `Kgπ 𝕜 p (k+1) = grFι 𝕜 (sSingP p) (k+1)` by `Work.SSSR.grFι_succ`).
The degree cast `(ComplexShape.down ℕ).next ((k+1)+q) = k+q` is needed to align the indices
(`Work.SSSR.down_next_eq`). -/
theorem Kgpi_d_cruxIota_sndToR (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (k q : ℕ)
    (y : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (Work.SSSR.sigHat y))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat y))).d q ((ComplexShape.down ℕ).next q))) z = 0) :
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (k + 1)).d ((k + 1) + q)
        ((ComplexShape.down ℕ).next ((k + 1) + q))))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f
            ((k + 1) + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z))) = 0 := by
  -- The image of the Eilenberg–Zilber chain in the σ-piece of `y`.
  have hstep1 :
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p (k + 1)).f ((k + 1) + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (Work.SSSR.sndToR (Work.SSSR.sSingP p) y)).f ((k + 1) + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z))
    = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f ((k + 1) + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
          ((k + 1) + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z)) := by
    have h := congrArg (fun (g : (Work.SSSR.sCC 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (Work.SSSR.sigHat y))).X ((k + 1) + q) ⟶
          (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) (k + 1)).X ((k + 1) + q)) =>
        (ModuleCat.Hom.hom g) (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z))
      (Work.SSSR.thetaPhi_mapPhiY_apply_f (R := 𝕜) (Work.SSSR.sSingP p) (k + 1) ((k + 1) + q) y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.symm
  have hstep2 :
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (k + 1)).d ((k + 1) + q)
          ((ComplexShape.down ℕ).next ((k + 1) + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
          ((k + 1) + q)))
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
            ((k + 1) + q)))
            (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z)))
    = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
        ((ComplexShape.down ℕ).next ((k + 1) + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p)
          (Work.SSSR.sigHat y)).d ((k + 1) + q) ((ComplexShape.down ℕ).next ((k + 1) + q))))
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
            ((k + 1) + q)))
            (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z))) :=
    Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k + 1) y)
      (i := (k + 1) + q) (j := (ComplexShape.down ℕ).next ((k + 1) + q))
      ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
        ((k + 1) + q)))
        (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z))
  have hstep3 :
      (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p)
          (Work.SSSR.sigHat y)).d ((k + 1) + q) ((ComplexShape.down ℕ).next ((k + 1) + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) (k + 1) y).f
          ((k + 1) + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib (k + 1) q (Work.SSSR.sigHat y) z)) = 0 :=
    Work.Pi6.MSS.cruxRel (𝕜 := 𝕜) (p := p) hfib (k + 1) q (Work.SSSR.sigHat y) z hz
  rw [hstep1, hstep2, hstep3]
  exact map_zero _

end Work.Pi6.MSS
