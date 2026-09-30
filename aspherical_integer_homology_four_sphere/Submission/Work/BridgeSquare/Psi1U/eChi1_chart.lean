import Mathlib
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.pieceDefs
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.denseSimplexA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.MbarHomology
open Convexity

namespace Work.BridgeSquare.Psi1U

noncomputable section

/-- `moCid` at the dimension `1` only depends on the value. -/
theorem moCid_one (e : Fin (Work.HomologyIso.Gen.mbarDim 1)) :
    Mbar.moCid ⟨1, by norm_num⟩ e = Mbar.moCid (1 : Fin 5) e := rfl

/-- The upper characteristic half of the `κ_{v,3}` unit edge is the cusp chart simplex
`[Yv k 1, Yv k ½]`. -/
theorem eChi1_chart (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Work.MbarHomology.Mbar.chi 1 (Work.BridgeSquare.Psi1.eSimp1 v k hk)
      = Work.BridgeSquare.cSimp v
          ![Work.BridgeSquare.Yv v k 1, Work.BridgeSquare.Yv v k (1/2)] := by
  have key : ∀ z : Convexity.StdSimplex ℝ (Fin 2), 0 < z.weights 1 →
      Mbar.chi 1 (Psi1.eSimp1 v k hk) z
        = cSimp v ![Yv v k 1, Yv v k (1/2)] z := by
    intro z hz
    have hsumw : ∑ i : Fin 2, z.weights i = 1 := Mbar.sum_weights z
    have hsum2 : z.weights 0 + z.weights 1 = 1 := by
      rw [← Fin.sum_univ_two]; exact hsumw
    have hw0 : 0 ≤ z.weights 0 := Convexity.StdSimplex.weights_nonneg (w := z) 0
    have hw1 : 0 ≤ z.weights 1 := Convexity.StdSimplex.weights_nonneg (w := z) 1
    have ht0 : 0 ≤ z.weights 0 + z.weights 1 / 2 := by nlinarith
    have ht1 : z.weights 0 + z.weights 1 / 2 < 1 := by nlinarith
    have htle : z.weights 0 + z.weights 1 / 2 ≤ 1 := le_of_lt ht1
    have hL : Mbar.chi 1 (Psi1.eSimp1 v k hk) z
        = Work.FoldInst.mk (Mbar.moRootC (Mbar.moCid (1 : Fin 5) (edgeCell v 1 k)),
            ⟨Mbar.ptW (Psi1.eFlag1 v k hk) z.weights,
              Mbar.ptW_mem (Psi1.eFlag1 v k hk)
                (fun i => Convexity.StdSimplex.weights_nonneg (w := z) i) hsumw⟩) := by
      rw [show Mbar.chi 1 (Psi1.eSimp1 v k hk)
          = Mbar.chi 1 (Mbar.rootSimplex 1 (by norm_num) (edgeCell v 1 k)
              (Psi1.eFlag1 v k hk)) from rfl]
      rw [Psi1.chi_rootSimplex_apply 1 (by norm_num) (edgeCell v 1 k) (Psi1.eFlag1 v k hk) z]
      rw [moCid_one]
      simp only [Mbar.chiRep, Mbar.chiPt]
    have hR : cSimp v ![Yv v k 1, Yv v k (1/2)] z
        = Work.FoldInst.mk (Work.RTOwed.cubeBit (edgeCube v 1 k),
            ⟨Work.RTOwed.kleinPt (edgeCube v 1 k)
                (cornerPt (edgeCube v 1 k) + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1)),
              Work.RTOwed.cuspCert.cube_quad.1 (edgeCube v 1 k)
                (cornerPt (edgeCube v 1 k) + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1))
                (Psi1.mem_cubeBox_corner v k (z.weights 0 + z.weights 1 / 2) ht0 htle)⟩) := by
      rw [cSimp_apply, Work.RTOwed.mbarPtC,
        show cPt ![Yv v k 1, Yv v k (1/2)] z + Work.RTOwed.cuspH
            = cornerPt (edgeCube v 1 k)
              + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1)
          from Psi1.cPt_Yv_top v k z,
        Work.RTOwed.mbarPt_eq_mk]
      refine Psi1.mbar_mk_congr ?_ ?_
      · rw [Psi1.cubeOf_corner v k _ ht0 ht1 hk]
      · rw [Psi1.cubeOf_corner v k _ ht0 ht1 hk, Psi1.redV_corner v k _ ht0 ht1 hk]
    have hmem : Mbar.Enode (Psi1.ebit v k) (edgeFace v 1 k)
        ∈ Work.FoldInst.Ksub (Mbar.ptW (Psi1.eFlag1 v k hk) z.weights) := by
      rw [Psi1.ptW_eFlag1 v k hk z.weights, Work.FoldInst.Ksub_act]
      exact Psi1.enode_mem_Ksub (v := v) (k := k) (s := Psi1.eNice1 v k hk)
        (Psi1.topIdx_eNice1 v k hk) z.weights
        (fun i => Convexity.StdSimplex.weights_nonneg (w := z) i) hsumw
    have hptWF : Mbar.ptW (Psi1.eFlag1 v k hk) z.weights
        = Work.FoldInst.act (Psi1.esig v k)
            (Work.RTOwed.kleinPt (edgeCube v 1 k)
              (cornerPt (edgeCube v 1 k)
                + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1))) := by
      rw [Psi1.ptW_eFlag1 v k hk z.weights, Psi1.ptW_eNice1_eq v k hk z.weights hsum2]
    rw [hL, hR]
    refine Psi1.mk_eq_of_rel ?_
    refine ⟨Mbar.Enode (Psi1.ebit v k) (edgeFace v 1 k), hmem, ?_⟩
    apply Prod.ext
    · show Mbar.moRootC (Mbar.moCid (1 : Fin 5) (edgeCell v 1 k))
          + (Mbar.Enode (Psi1.ebit v k) (edgeFace v 1 k)).2 = Work.RTOwed.cubeBit (edgeCube v 1 k)
      rw [Psi1.enode_snd v k hk, Psi1.cubeBit_edgeCube]
      exact Psi1.zmod2_add_swap _ _
    · apply Subtype.ext
      show Work.FoldInst.act (Psi1.esig v k) (Mbar.ptW (Psi1.eFlag1 v k hk) z.weights)
          = Work.RTOwed.kleinPt (edgeCube v 1 k)
              (cornerPt (edgeCube v 1 k)
                + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1))
      rw [hptWF, Psi1.act_esig_self v k]
  apply ContinuousMap.ext
  intro z
  exact congrFun (Continuous.ext_on denseSimplexA
    (Mbar.chi 1 (Psi1.eSimp1 v k hk)).continuous
    (cSimp v ![Yv v k 1, Yv v k (1/2)]).continuous
    (fun z hz => key z hz)) z

end

end Work.BridgeSquare.Psi1U
