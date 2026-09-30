import Mathlib
import Submission.Work.BridgeSquare.CellChiADefs
import Submission.Work.BridgeSquare.denseSimplexA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.MbarHomology

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  Affinity of the cusp chart `kleinPt` -/

theorem kleinPt_sum_smul (a : Fin 48) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (z : ι → cE3)
    (h : ∑ i ∈ s, c i = 1) :
    Work.RTOwed.kleinPt a (∑ i ∈ s, c i • z i)
      = ∑ i ∈ s, c i • Work.RTOwed.kleinPt a (z i) := by
  apply PiLp.ext
  intro i
  simp only [Work.RTOwed.kleinPt, WithLp.ofLp_toLp, Finset.sum_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, smul_eq_mul]
  have hR : ∑ k ∈ s, c k * (∑ x, ↑(Work.Cusp.cubeXToKlein a i x) * (z k).ofLp x
        + ↑(Work.Cusp.cubeXToKleinb a i))
      = (∑ k ∈ s, c k * (∑ x, ↑(Work.Cusp.cubeXToKlein a i x) * (z k).ofLp x))
        + ∑ k ∈ s, c k * ↑(Work.Cusp.cubeXToKleinb a i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k hk => mul_add _ _ _
  rw [hR, ← Finset.sum_mul, h, one_mul]
  congr 1
  rw [show (∑ x, ↑(Work.Cusp.cubeXToKlein a i x) * ∑ k ∈ s, c k * (z k).ofLp x)
      = ∑ x, ∑ k ∈ s, ↑(Work.Cusp.cubeXToKlein a i x) * (c k * (z k).ofLp x) from
    Finset.sum_congr rfl fun x hx => by rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x hx => by ring

theorem kleinPt_two (a : Fin 48) (c0 c1 : ℝ) (z0 z1 : cE3) (h : c0 + c1 = 1) :
    Work.RTOwed.kleinPt a (c0 • z0 + c1 • z1)
      = c0 • Work.RTOwed.kleinPt a z0 + c1 • Work.RTOwed.kleinPt a z1 := by
  have hc : (∑ i : Fin 2, (if i = 0 then c0 else c1)) = 1 := by
    rw [Fin.sum_univ_two]; simpa using h
  have key := kleinPt_sum_smul a (Finset.univ : Finset (Fin 2))
    (fun i : Fin 2 => if i = 0 then c0 else c1)
    (fun i : Fin 2 => if i = 0 then z0 else z1) (by simpa using hc)
  simpa [Fin.sum_univ_two] using key

/-! ## §2  The cube corner of a unit edge, as a vector -/

/-- The cube corner of the cube of the `k`-th unit edge of the `κ_{v,2}`-loop, as a vector. -/
abbrev eX0 (v : Fin 5) (k : Fin 4) : cE3 :=
  WithLp.toLp 2 (fun i : Fin 3 => (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ))

theorem cuspCorner_add_cuspH_u (v : Fin 5) (k : Fin 4) :
    cuspCorner v k + Work.RTOwed.cuspH = eX0 v k := by
  apply PiLp.ext
  intro i
  simp only [cuspCorner, eX0, Work.RTOwed.cuspH, PiLp.add_apply, WithLp.ofLp_toLp]
  ring

theorem eX0_add_axVec (v : Fin 5) (k : Fin 4) :
    eX0 v k + axVec v
      = WithLp.toLp 2 (fun i : Fin 3 => (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)
          + (if i = dirKappa v 1 then 1 else 0)) := by
  show WithLp.toLp 2 (fun i : Fin 3 => (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ))
      + WithLp.toLp 2 (fun i : Fin 3 => if i = dirKappa v 1 then (1 : ℝ) else 0) = _
  rw [← WithLp.toLp_add]
  rfl

/-! ## §3  The affine point of `eNice1` -/

theorem flagIdx_eNice1_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Mbar.flagIdx (eNice1 v k hk) 0 = edgeW1Face v 0 k := by
  show ((eNice1 v k hk) 0).idx = _
  conv_lhs => rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl]
  simp only [eNice1, Work.Subdivision.Simplex.snoc_apply_castSucc,
    Work.Subdivision.Simplex.vertex_apply]

theorem flagIdx_eNice1_one (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Mbar.flagIdx (eNice1 v k hk) 1 = edgeFace v 0 k := by
  show ((eNice1 v k hk) 1).idx = _
  conv_lhs => rw [show (1 : Fin 2) = Fin.last 1 from rfl]
  simp only [eNice1, Work.Subdivision.Simplex.snoc_apply_last]

theorem posR_edgeW0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    QbarPD.posR (edgeW0Face v 0 k) = Work.RTOwed.kleinPt (edgeCube v 0 k) (eX0 v k) := by
  rw [posR_W0 v k hk]

theorem posR_edgeW1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    QbarPD.posR (edgeW1Face v 0 k) = Work.RTOwed.kleinPt (edgeCube v 0 k) (eX0 v k + axVec v) := by
  rw [posR_W1 v k hk, ← eX0_add_axVec]

theorem posR_edgeFace_u (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    QbarPD.posR (edgeFace v 0 k)
      = Work.RTOwed.kleinPt (edgeCube v 0 k) (eX0 v k + (1 / 2 : ℝ) • axVec v) := by
  have h2 : QbarPD.posR (edgeFace v 0 k)
      = (1 / 2 : ℝ) • (QbarPD.posR (edgeW0Face v 0 k) + QbarPD.posR (edgeW1Face v 0 k)) := by
    have hc := congrArg (fun y => (1 / 2 : ℝ) • y) (posR_mid v k hk)
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at hc
    exact hc
  rw [h2, posR_edgeW0 v k hk, posR_edgeW1 v k hk, smul_add]
  rw [← kleinPt_two (edgeCube v 0 k) (1 / 2) (1 / 2) (eX0 v k) (eX0 v k + axVec v) (by norm_num)]
  congr 1
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, eX0, axVec, WithLp.ofLp_toLp, smul_eq_mul]
  ring

theorem ptW_eNice1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (w : Fin 2 → ℝ)
    (hw : w 0 + w 1 = 1) :
    Mbar.ptW (eNice1 v k hk) w
      = Work.RTOwed.kleinPt (edgeCube v 0 k) (eX0 v k + (w 0 + w 1 / 2) • axVec v) := by
  rw [Mbar.ptW, Fin.sum_univ_two, flagIdx_eNice1_zero v k hk, flagIdx_eNice1_one v k hk,
    posR_edgeW1 v k hk, posR_edgeFace_u v k hk]
  rw [← kleinPt_two (edgeCube v 0 k) (w 0) (w 1) (eX0 v k + axVec v)
    (eX0 v k + (1 / 2 : ℝ) • axVec v) hw]
  congr 1
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, eX0, axVec, WithLp.ofLp_toLp, smul_eq_mul]
  linear_combination ((Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)) * hw

/-! ## §4  The cusp chart point of the two vertices of the upper half -/

theorem cPt_edge (v : Fin 5) (k : Fin 4) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    cPt ![cuspCorner1 v k, cuspMid v k] z + Work.RTOwed.cuspH
      = eX0 v k + (z.weights 0 + z.weights 1 / 2) • axVec v := by
  have hsum2 : z.weights 0 + z.weights 1 = 1 := by
    have h := Mbar.sum_weights z
    rw [Fin.sum_univ_two] at h
    exact h
  have hpt : cPt ![cuspCorner1 v k, cuspMid v k] z
      = z.weights 0 • cuspCorner1 v k + z.weights 1 • cuspMid v k := by
    rw [cPt_eq_sum, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hpt]
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, cuspCorner1, cuspMid, cuspCorner, eX0, axVec,
    Work.RTOwed.cuspH, WithLp.ofLp_toLp, smul_eq_mul]
  linear_combination ((Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ) - 1 / 2) * hsum2

/-! ## §5  The floor, cube and representative of the interior point -/

theorem ofLp_eX0 (v : Fin 5) (k : Fin 4) (t : ℝ) (i : Fin 3) :
    (eX0 v k + t • axVec v).ofLp i
      = (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)
        + (if i = dirKappa v 1 then t else 0) := by
  simp only [PiLp.add_apply, PiLp.smul_apply, eX0, axVec, WithLp.ofLp_toLp, smul_eq_mul]
  split_ifs <;> ring

theorem floor_coord_eX0 (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (i : Fin 3) :
    ⌊(eX0 v k + t • axVec v).ofLp i⌋ = Work.Cusp.cubeCorner (edgeCube v 0 k) i := by
  rw [ofLp_eX0]
  rw [Int.floor_eq_iff]
  constructor <;> split_ifs <;> linarith

theorem floorV_eX0 (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    Work.RTOwed.floorV (eX0 v k + t • axVec v) = Work.Cusp.cubeCorner (edgeCube v 0 k) := by
  funext i
  show ⌊(eX0 v k + t • axVec v).ofLp i⌋ = _
  exact floor_coord_eX0 v k t h0 h1 i

theorem cubeOfMod_cubeCorner_edgeCube (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Cusp.cubeOfMod v (Work.Cusp.cubeCorner (edgeCube v 0 k)) = edgeCube v 0 k := by
  fin_cases v <;> fin_cases k <;>
    first | (exfalso; revert hk; decide) | decide

theorem cubeOf_eX0 (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1)
    (hk : (k : ℕ) < fibreLen v 0) :
    Work.RTOwed.cubeOf v (eX0 v k + t • axVec v) = edgeCube v 0 k := by
  rw [Work.RTOwed.cubeOf, floorV_eX0 v k t h0 h1, cubeOfMod_cubeCorner_edgeCube v k hk]

theorem redV_eX0 (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1)
    (hk : (k : ℕ) < fibreLen v 0) :
    Work.RTOwed.redV v (eX0 v k + t • axVec v) = eX0 v k + t • axVec v := by
  rw [Work.RTOwed.redV, cubeOf_eX0 v k t h0 h1 hk]
  show WithLp.toLp 2 (fun i : Fin 3 => (eX0 v k + t • axVec v).ofLp i
      - ↑⌊(eX0 v k + t • axVec v).ofLp i⌋
      + (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)) = eX0 v k + t • axVec v
  rw [show (fun i : Fin 3 => (eX0 v k + t • axVec v).ofLp i
        - ↑⌊(eX0 v k + t • axVec v).ofLp i⌋
        + (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ))
      = (fun i : Fin 3 => (eX0 v k + t • axVec v).ofLp i) from by
    funext i
    rw [floor_coord_eX0 v k t h0 h1 i]; ring]

theorem mem_cubeBox_eX0 (v : Fin 5) (k : Fin 4) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    eX0 v k + s • axVec v ∈ Work.RTOwed.cubeBox (edgeCube v 0 k) := by
  show ∀ i : Fin 3, (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)
      ≤ (eX0 v k + s • axVec v).ofLp i
    ∧ (eX0 v k + s • axVec v).ofLp i
      ≤ (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ) + 1
  intro i
  rw [ofLp_eX0]
  constructor <;> split_ifs <;> linarith

/-! ## §6  Small arithmetic and the identification group -/

theorem zmod2_add_swap (a b : ZMod 2) : a + (b + a) = b := by
  rw [add_comm a (b + a), add_assoc, Work.FoldInst.ZMod2_add_self, add_zero]

theorem act_esig_self (v : Fin 5) (k : Fin 4) (y : Work.FoldInst.E4) :
    Work.FoldInst.act (esig v k) (Work.FoldInst.act (esig v k) y) = y := by
  rw [Work.FoldInst.act_add]
  have h : esig v k + esig v k = 0 := by funext i; exact Work.FoldInst.ZMod2_add_self _
  rw [h, Work.FoldInst.act_zero]

theorem cubeBit_edgeCube (v : Fin 5) (k : Fin 4) :
    Work.RTOwed.cubeBit (edgeCube v 0 k) = ebit v k := rfl

theorem enode_mem_Ksub (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    Mbar.Enode (ebit v k) (edgeFace v 0 k) ∈ Work.FoldInst.Ksub (Mbar.ptW (eFlag1 v k hk) w) := by
  refine Mbar.Ksub_bary_le (eFlag1 v k hk) hw hsum ?_
  rw [Mbar.Ksub_bary_eq_KsubAtlas]
  have htop : ((eFlag1 v k hk).toFun (Fin.last 1)).idx
      = faceAct (esig v k) (edgeFace v 0 k) := by
    rw [show ((eFlag1 v k hk).toFun (Fin.last 1)).idx = Mbar.topIdx (eFlag1 v k hk) from rfl]
    rw [show eFlag1 v k hk = Mbar.flagAct (esig v k) (eNice1 v k hk) from rfl]
    rw [show Mbar.topIdx (Mbar.flagAct (esig v k) (eNice1 v k hk))
        = ((Mbar.flagAct (esig v k) (eNice1 v k hk)).toFun (Fin.last 1)).idx from rfl]
    rw [Mbar.flagAct_idx]
    rw [show ((eNice1 v k hk).toFun (Fin.last 1)).idx = Mbar.topIdx (eNice1 v k hk) from rfl,
      topIdx_eNice1_aux v k hk]
  rw [htop, Mbar.KsubAtlas_faceAct]
  exact Mbar.Enode_mem_KsubAtlas (ebit v k) (edgeFace v 0 k)

theorem enode_snd (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (Mbar.Enode (ebit v k) (edgeFace v 0 k)).2
      = ebit v k + Mbar.moRootC (Mbar.moCid (1 : Fin 5) (edgeCell v 0 k)) := by
  show ebit v k + Mbar.moRootC (Mbar.moCell (ebit v k) (edgeFace v 0 k)) = _
  rw [moCell_ebit_edgeFace v k hk]

/-! ## §7  The characteristic map, unfolded -/

theorem chi_rootSimplex_apply (n : ℕ) (hn : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    (s : Work.Subdivision.Simplex QbarCW.Cell n) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Mbar.chi n (Mbar.rootSimplex n hn e s) z
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid ⟨n, hn⟩ e), s) z := by
  have h1 : Mbar.chi n (Mbar.rootSimplex n hn e s)
      = ⟨fun w => Mbar.chiRep (Mbar.moRootC (Mbar.moCid ⟨n, hn⟩ e), s) w,
          Mbar.continuous_chiRep _⟩ := by
    unfold Mbar.chi
    rw [show Work.MbarHomology.mbarEquiv n (Mbar.rootSimplex n hn e s)
        = Quotient.mk (Work.MbarHomology.flagSetoid n)
            (Mbar.moRootC (Mbar.moCid ⟨n, hn⟩ e), s) from
      Equiv.apply_symm_apply _ _]
    exact Mbar.chiQuot_mk n _
  rw [h1]
  rfl

theorem moCid_one (e : Fin (Work.HomologyIso.Gen.mbarDim 1)) :
    Mbar.moCid ⟨1, by norm_num⟩ e = Mbar.moCid (1 : Fin 5) e := rfl

theorem mk_eq_of_rel {x y : Work.FoldInst.Xbar} (h : Work.FoldInst.rel x y) :
    Work.FoldInst.mk x = Work.FoldInst.mk y :=
  Quotient.sound (s := Work.FoldInst.setoid) h

theorem mbar_mk_congr {b b' : ZMod 2} {q q' : Work.FoldInst.E4} {h : q ∈ Work.FoldInst.Qbar}
    {h' : q' ∈ Work.FoldInst.Qbar} (hb : b = b') (hq : q = q') :
    (Work.FoldInst.mk (b, ⟨q, h⟩) : Work.FoldInst.Mbar)
      = Work.FoldInst.mk (b', ⟨q', h'⟩) :=
  congrArg Work.FoldInst.mk (Prod.ext hb (Subtype.ext hq))

/-! ## §8  The main theorem -/

theorem eChi1_chart_v2 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 0) :
    Work.MbarHomology.Mbar.chi 1 (Work.BridgeSquare.eSimp1 v k hk)
      = Work.BridgeSquare.cSimp v ![Work.BridgeSquare.cuspCorner1 v k, Work.BridgeSquare.cuspMid v k] := by
  have key : ∀ z : Convexity.StdSimplex ℝ (Fin 2), 0 < z.weights 1 →
      Mbar.chi 1 (eSimp1 v k hk) z = cSimp v ![cuspCorner1 v k, cuspMid v k] z := by
    intro z hz
    have hsumw : ∑ i : Fin 2, z.weights i = 1 := Mbar.sum_weights z
    have hsum2 : z.weights 0 + z.weights 1 = 1 := by
      rw [← Fin.sum_univ_two]; exact hsumw
    have hw0 : 0 ≤ z.weights 0 := Convexity.StdSimplex.weights_nonneg (w := z) 0
    have hw1 : 0 ≤ z.weights 1 := Convexity.StdSimplex.weights_nonneg (w := z) 1
    have ht0 : 0 ≤ z.weights 0 + z.weights 1 / 2 := by nlinarith
    have ht1 : z.weights 0 + z.weights 1 / 2 < 1 := by nlinarith
    have htle : z.weights 0 + z.weights 1 / 2 ≤ 1 := le_of_lt ht1
    have hL : Mbar.chi 1 (eSimp1 v k hk) z
        = Work.FoldInst.mk (Mbar.moRootC (Mbar.moCid (1 : Fin 5) (edgeCell v 0 k)),
            ⟨Mbar.ptW (eFlag1 v k hk) z.weights,
              Mbar.ptW_mem (eFlag1 v k hk)
                (fun i => Convexity.StdSimplex.weights_nonneg (w := z) i) hsumw⟩) := by
      rw [show Mbar.chi 1 (eSimp1 v k hk)
          = Mbar.chi 1 (Mbar.rootSimplex 1 (by norm_num) (edgeCell v 0 k) (eFlag1 v k hk)) from rfl]
      rw [chi_rootSimplex_apply 1 (by norm_num) (edgeCell v 0 k) (eFlag1 v k hk) z]
      rw [moCid_one]
      simp only [Mbar.chiRep, Mbar.chiPt]
    have hR : cSimp v ![cuspCorner1 v k, cuspMid v k] z
        = Work.FoldInst.mk (Work.RTOwed.cubeBit (edgeCube v 0 k),
            ⟨Work.RTOwed.kleinPt (edgeCube v 0 k)
                (eX0 v k + (z.weights 0 + z.weights 1 / 2) • axVec v),
              Work.RTOwed.cuspCert.cube_quad.1 (edgeCube v 0 k)
                (eX0 v k + (z.weights 0 + z.weights 1 / 2) • axVec v)
                (mem_cubeBox_eX0 v k (z.weights 0 + z.weights 1 / 2) ht0 htle)⟩) := by
      rw [cSimp_apply, Work.RTOwed.mbarPtC,
        show cPt ![cuspCorner1 v k, cuspMid v k] z + Work.RTOwed.cuspH
            = eX0 v k + (z.weights 0 + z.weights 1 / 2) • axVec v from cPt_edge v k z,
        Work.RTOwed.mbarPt_eq_mk]
      refine mbar_mk_congr ?_ ?_
      · rw [cubeOf_eX0 v k _ ht0 ht1 hk]
      · rw [cubeOf_eX0 v k _ ht0 ht1 hk, redV_eX0 v k _ ht0 ht1 hk]
    have hptWF : Mbar.ptW (eFlag1 v k hk) z.weights
        = Work.FoldInst.act (esig v k)
            (Work.RTOwed.kleinPt (edgeCube v 0 k)
              (eX0 v k + (z.weights 0 + z.weights 1 / 2) • axVec v)) := by
      rw [show Mbar.ptW (eFlag1 v k hk) z.weights
          = Mbar.ptW (Mbar.simplexAct (esig v k) (eNice1 v k hk)) z.weights from rfl]
      rw [Mbar.ptW_simplexAct, ptW_eNice1 v k hk z.weights hsum2]
    rw [hL, hR]
    refine mk_eq_of_rel ?_
    refine ⟨Mbar.Enode (ebit v k) (edgeFace v 0 k),
      enode_mem_Ksub v k hk z.weights
        (fun i => Convexity.StdSimplex.weights_nonneg (w := z) i) hsumw, ?_⟩
    apply Prod.ext
    · show Mbar.moRootC (Mbar.moCid (1 : Fin 5) (edgeCell v 0 k))
          + (Mbar.Enode (ebit v k) (edgeFace v 0 k)).2 = Work.RTOwed.cubeBit (edgeCube v 0 k)
      rw [enode_snd v k hk, cubeBit_edgeCube]
      exact zmod2_add_swap _ _
    · apply Subtype.ext
      show Work.FoldInst.act (esig v k) (Mbar.ptW (eFlag1 v k hk) z.weights)
          = Work.RTOwed.kleinPt (edgeCube v 0 k) (eX0 v k + (z.weights 0 + z.weights 1 / 2) • axVec v)
      rw [hptWF, act_esig_self v k]
  apply ContinuousMap.ext
  intro z
  exact congrFun (Continuous.ext_on denseSimplexA
    (Mbar.chi 1 (eSimp1 v k hk)).continuous
    (cSimp v ![cuspCorner1 v k, cuspMid v k]).continuous
    (fun z hz => key z hz)) z

end

end Work.BridgeSquare
