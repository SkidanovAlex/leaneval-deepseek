import Mathlib
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.pieceDefs
import Submission.Work.BridgeSquare.ChartAlgA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Work.MbarHomology
open Convexity

namespace Work.BridgeSquare.Psi1L

open Work.BridgeSquare.Psi1

noncomputable section

/-- The `j = 1` analogue of `Work.BridgeSquare.chi_eSimp0_apply`: the value of the characteristic
map on the lower characteristic simplex of the `k`-th unit edge of the `κ_{v,3}`-loop. -/
theorem chi_eSimp0_apply_p1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1)
    (w : Convexity.StdSimplex ℝ (Fin 2)) :
    Mbar.chi 1 (Work.BridgeSquare.Psi1.eSimp0 v k hk) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (1 : Fin 5) (Work.BridgeSquare.edgeCell v 1 k)),
          Work.BridgeSquare.Psi1.eFlag0 v k hk) w := by
  rw [show Mbar.chi 1 (Work.BridgeSquare.Psi1.eSimp0 v k hk)
      = Mbar.chi 1 (Mbar.rootSimplex 1 (by norm_num) (Work.BridgeSquare.edgeCell v 1 k)
          (Work.BridgeSquare.Psi1.eFlag0 v k hk)) from rfl]
  rw [Work.BridgeSquare.Psi1.chi_rootSimplex_apply 1 (by norm_num)
      (Work.BridgeSquare.edgeCell v 1 k) (Work.BridgeSquare.Psi1.eFlag0 v k hk) w]
  rfl

theorem eChi0_chart (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Work.MbarHomology.Mbar.chi 1 (Work.BridgeSquare.Psi1.eSimp0 v k hk)
      = Work.BridgeSquare.cSimp v
          ![Work.BridgeSquare.Yv v k 0, Work.BridgeSquare.Yv v k (1/2)] := by
  ext w
  have hsum : w.weights 0 + w.weights 1 = 1 := by
    have h := Mbar.sum_weights w
    rwa [Fin.sum_univ_two] at h
  have hs0 : 0 ≤ w.weights 1 / 2 := div_nonneg (w.nonneg 1) (by norm_num)
  have hs1 : w.weights 1 / 2 < 1 := by
    have h0 : 0 ≤ w.weights 0 := w.nonneg 0
    have h1 : w.weights 1 ≤ 1 := by linarith
    linarith
  rw [chi_eSimp0_apply_p1 v k hk w, Mbar.chiRep, Mbar.chiPt, cSimp_apply,
    Work.BridgeSquare.Psi1.mbarPtC_Yv_low v k w, Work.RTOwed.mbarPt_eq_mk]
  refine Quotient.sound ⟨Mbar.Enode (Work.BridgeSquare.Psi1.ebit v k)
    (Work.BridgeSquare.edgeFace v 1 k), ?_, ?_⟩
  · show Mbar.Enode (Work.BridgeSquare.Psi1.ebit v k) (Work.BridgeSquare.edgeFace v 1 k)
        ∈ Work.FoldInst.Ksub (Mbar.ptW (Work.BridgeSquare.Psi1.eFlag0 v k hk)
            (fun i => w.weights i))
    rw [Work.BridgeSquare.Psi1.ptW_eFlag0, Work.FoldInst.Ksub_act]
    have hbary : Work.FoldInst.Ksub (bary (Work.BridgeSquare.Psi1.eNice0 v k hk))
        = Mbar.KsubAtlas (Work.BridgeSquare.edgeFace v 1 k) := by
      rw [Mbar.Ksub_bary_eq_KsubAtlas]
      exact congrArg Mbar.KsubAtlas (Work.BridgeSquare.Psi1.topIdx_eNice0 v k hk)
    have hle : Work.FoldInst.Ksub (bary (Work.BridgeSquare.Psi1.eNice0 v k hk))
        ≤ Work.FoldInst.Ksub (Mbar.ptW (Work.BridgeSquare.Psi1.eNice0 v k hk)
            (fun i => w.weights i)) :=
      Mbar.Ksub_bary_le (Work.BridgeSquare.Psi1.eNice0 v k hk) (fun i => w.nonneg i)
        (Mbar.sum_weights w)
    refine hle ?_
    rw [hbary]
    exact Mbar.Enode_mem_KsubAtlas _ _
  · refine Prod.ext ?_ ?_
    · show Mbar.moRootC (Mbar.moCid (1 : Fin 5) (Work.BridgeSquare.edgeCell v 1 k))
          + (Mbar.Enode (Work.BridgeSquare.Psi1.ebit v k)
              (Work.BridgeSquare.edgeFace v 1 k)).2
        = Work.RTOwed.cubeBit (Work.RTOwed.cubeOf v
            (Work.BridgeSquare.cornerPt (Work.BridgeSquare.edgeCube v 1 k)
              + (w.weights 1 / 2) • Work.BridgeSquare.eVec (Work.BridgeSquare.fibreDir v 1)))
      rw [Work.BridgeSquare.Psi1.enode_snd v k hk,
        Work.BridgeSquare.Psi1.cubeOf_corner v k (w.weights 1 / 2) hs0 hs1 hk,
        Work.BridgeSquare.Psi1.cubeBit_edgeCube v k]
      exact Work.BridgeSquare.Psi1.zmod2_add_swap _ _
    · refine Subtype.ext ?_
      show Work.FoldInst.act (Work.BridgeSquare.Psi1.esig v k)
            (Mbar.ptW (Work.BridgeSquare.Psi1.eFlag0 v k hk) (fun i => w.weights i))
        = Work.RTOwed.kleinPt (Work.RTOwed.cubeOf v
              (Work.BridgeSquare.cornerPt (Work.BridgeSquare.edgeCube v 1 k)
                + (w.weights 1 / 2) • Work.BridgeSquare.eVec (Work.BridgeSquare.fibreDir v 1)))
            (Work.RTOwed.redV v
              (Work.BridgeSquare.cornerPt (Work.BridgeSquare.edgeCube v 1 k)
                + (w.weights 1 / 2) • Work.BridgeSquare.eVec (Work.BridgeSquare.fibreDir v 1)))
      rw [Work.BridgeSquare.Psi1.ptW_eFlag0, Work.FoldInst.act_add,
        show Work.BridgeSquare.Psi1.esig v k + Work.BridgeSquare.Psi1.esig v k = 0 from
          funext fun i => Work.FoldInst.ZMod2_add_self _,
        Work.FoldInst.act_zero,
        Work.BridgeSquare.Psi1.ptW_eNice0_eq v k hk (fun i => w.weights i) hsum]
      rw [Work.BridgeSquare.Psi1.cubeOf_corner v k (w.weights 1 / 2) hs0 hs1 hk,
        Work.BridgeSquare.Psi1.redV_corner v k (w.weights 1 / 2) hs0 hs1 hk]

end

end Work.BridgeSquare.Psi1L
