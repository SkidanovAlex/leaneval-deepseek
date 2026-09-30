import Mathlib
import Submission.Work.BridgeSquare.CellChiADefs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.MbarHomology
open Convexity

namespace Work.BridgeSquare

noncomputable section

/-!
The lower characteristic half of a unit edge is the cusp chart simplex `[cuspCorner, cuspMid]`.

Route.  `chi 1 (rootSimplex 1 _ e s)` unfolds (`Mbar.chiQuot_mk`, `Mbar.rootSimplex`,
`Equiv.apply_symm_apply`) to `w ↦ chiRep (moRootC (moCid 1 e), s) w =
mk (bit, ⟨ptW s w.weights, _⟩)`.  Since `eFlag0 v k hk = flagAct (esig v k) (eNice0 v k hk)`,
`ptW_simplexAct` gives `ptW (eFlag0) w = act (esig v k) (ptW (eNice0) w)`, and
`ptW (eNice0) w = w 0 • posR (edgeW0Face v 0 k) + w 1 • posR (edgeFace v 0 k)` is
`kleinPt (edgeCube v 0 k) (cubeCorner a + (w 1 / 2) • axVec v)` by `posR_W0`, `posR_mid` and the
affinity of `kleinPt`.  The chart value `mbarPtC v (w 0 • cuspCorner + w 1 • cuspMid)` is
`mk (ebit v k, ⟨kleinPt a (cubeCorner a + (w 1 / 2) • axVec v), _⟩)` by `RTOwed.mbarPt_eq_mk`
(that point has floor/cube `cubeCorner a` / `edgeCube v 0 k`: a finite table check), and the two
`mk`-arguments are related by the group element `Mbar.Enode (ebit v k) (edgeFace v 0 k)`, which
lies in `Mbar.KsubAtlas (edgeFace v 0 k)` (`Mbar.Enode_mem_KsubAtlas`; its two components are
`esig v k` and `ebit v k + Mbar.moRootC (Mbar.moCid 1 (edgeCell v 0 k))`, the latter a finite
table identity) and hence in `Ksub` at every point of the closed simplex (`Mbar.Ksub_bary_le` with
`Mbar.Ksub_bary_eq_KsubAtlas`, using `topIdx_eNice0_aux` and `Mbar.Ksub_act`).
-/

/-! ## §0  The affine coordinates of the cube corner -/

/-- The cusp coordinates of the corner of the cube `a`, as an element of `E3`. -/
def CP (a : Fin 48) : RTOwed.CuspE3 :=
  WithLp.toLp 2 fun i : Fin 3 => (Work.Cusp.cubeCorner a i : ℝ)

/-- The image of the `v`-th axis direction under the linear part of `kleinPt a`. -/
def kax (a : Fin 48) (v : Fin 5) : RTOwed.CuspE4 :=
  WithLp.toLp 2 fun i : Fin 4 => ((Work.Cusp.cubeXToKlein a) i (dirKappa v 1) : ℝ)

/-- The `i`-th coordinate of `CP a + s • axVec v`. -/
lemma CP_apply (a : Fin 48) (v : Fin 5) (s : ℝ) (i : Fin 3) :
    (CP a + s • axVec v) i
      = (Work.Cusp.cubeCorner a i : ℝ) + s * (if i = dirKappa v 1 then (1:ℝ) else 0) := by
  simp only [CP, axVec, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- `CP a + s • axVec v` as an explicit `toLp`. -/
lemma CP_add_smul_axVec (a : Fin 48) (v : Fin 5) (s : ℝ) :
    CP a + s • axVec v
      = WithLp.toLp 2 (fun i : Fin 3 =>
          (Work.Cusp.cubeCorner a i : ℝ) + s * (if i = dirKappa v 1 then (1:ℝ) else 0)) := by
  rw [CP, axVec, ← WithLp.toLp_add, ← WithLp.toLp_smul]
  rfl

/-- `CP a + axVec v` is `posR_W1`'s argument. -/
lemma CP_add_axVec (a : Fin 48) (v : Fin 5) :
    CP a + axVec v
      = WithLp.toLp 2 (fun i : Fin 3 =>
          (Work.Cusp.cubeCorner a i : ℝ) + (if i = dirKappa v 1 then (1:ℝ) else 0)) := by
  rw [CP, axVec, ← WithLp.toLp_add]
  rfl

/-- A sum with an indicator factor collapses to the selected term. -/
lemma sum_mul_ind {A : Fin 3 → ℝ} (i0 : Fin 3) :
    ∑ j : Fin 3, A j * (if j = i0 then (1:ℝ) else 0) = A i0 := by
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i0) h

/-- Splitting a sum with a shifted argument. -/
lemma sum_add_ind (A c : Fin 3 → ℝ) (s : ℝ) (i0 : Fin 3) :
    ∑ j : Fin 3, A j * (c j + s * (if j = i0 then (1:ℝ) else 0))
      = (∑ j : Fin 3, A j * c j) + s * A i0 := by
  have h : ∀ j : Fin 3, A j * (c j + s * (if j = i0 then (1:ℝ) else 0))
      = A j * c j + s * (A j * (if j = i0 then (1:ℝ) else 0)) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_mul_ind (A := A) i0]

/-- **The affinity of `kleinPt` along the cube corner.** -/
lemma kleinPt_corner_add (a : Fin 48) (v : Fin 5) (s : ℝ) :
    RTOwed.kleinPt a (CP a + s • axVec v) = RTOwed.kleinPt a (CP a) + s • kax a v := by
  ext i
  simp only [RTOwed.kleinPt, CP, kax, axVec, WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [sum_add_ind (A := fun j => (Work.Cusp.cubeXToKlein a i j : ℝ))
        (c := fun j => (Work.Cusp.cubeCorner a j : ℝ)) s (dirKappa v 1)]
  ring

/-- Two elementary linear identities in a module. -/
lemma smul_half_aux {M : Type*} [AddCommGroup M] [Module ℝ M] (K Y : M) (p q : ℝ)
    (h : p + q = 1) : p • K + q • (K + (1/2:ℝ) • Y) = K + (q / 2) • Y := by
  have h1 : q • (K + (1/2:ℝ) • Y) = q • K + (q / 2) • Y := by
    rw [smul_add, smul_smul, show q * (1/2:ℝ) = q / 2 by ring]
  rw [h1, ← add_assoc, ← add_smul, h, one_smul]

lemma two_smul_half {M : Type*} [AddCommGroup M] [Module ℝ M] (K Y : M) :
    (2:ℝ) • (K + (1/2:ℝ) • Y) = K + (K + Y) := by
  rw [smul_add, smul_smul]
  norm_num
  rw [← add_assoc, ← two_smul ℝ K]

/-! ## §1  The affine point of the lower half of a unit edge -/

lemma flagIdx_eNice0_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Mbar.flagIdx (eNice0 v k hk) 0 = edgeW0Face v 0 k := by
  show ((eNice0 v k hk) 0).idx = edgeW0Face v 0 k
  rw [show (eNice0 v k hk) (0 : Fin 2) = (⟨edgeW0Face v 0 k⟩ : QbarCell) from by
    show (eNice0 v k hk) ((0 : Fin 1).castSucc) = (⟨edgeW0Face v 0 k⟩ : QbarCell)
    rw [show (eNice0 v k hk) ((0 : Fin 1).castSucc) = (⟨edgeW0Face v 0 k⟩ : QbarCell) from
      Subdivision.Simplex.snoc_apply_castSucc _ _ _ (0 : Fin 1)]]

lemma flagIdx_eNice0_one (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Mbar.flagIdx (eNice0 v k hk) 1 = edgeFace v 0 k := by
  show ((eNice0 v k hk) 1).idx = edgeFace v 0 k
  rw [show (eNice0 v k hk) (1 : Fin 2) = (⟨edgeFace v 0 k⟩ : QbarCell) from by
    show (eNice0 v k hk) (Fin.last 1) = (⟨edgeFace v 0 k⟩ : QbarCell)
    rw [show (eNice0 v k hk) (Fin.last 1) = (⟨edgeFace v 0 k⟩ : QbarCell) from
      Subdivision.Simplex.snoc_apply_last _ _ _]]

/-- The affine point of the flag `eNice0` is the midpoint of the ridge. -/
lemma ptW_eNice0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (ww : Fin 2 → ℝ) :
    Mbar.ptW (eNice0 v k hk) ww
      = ww 0 • QbarPD.posR (edgeW0Face v 0 k) + ww 1 • QbarPD.posR (edgeFace v 0 k) := by
  rw [Mbar.ptW, Fin.sum_univ_two]
  rw [flagIdx_eNice0_zero v k hk, flagIdx_eNice0_one v k hk]

/-- The affine point of the ridge, in the Klein coordinates of the cube corner. -/
lemma posR_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    QbarPD.posR (edgeFace v 0 k)
      = RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k) + (1/2:ℝ) • axVec v) := by
  have h0 : QbarPD.posR (edgeW0Face v 0 k)
      = RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k)) := posR_W0 v k hk
  have h1 : QbarPD.posR (edgeW1Face v 0 k)
      = RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k) + axVec v) := by
    rw [posR_W1 v k hk, CP_add_axVec]
  have hAx : RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k) + axVec v)
      = RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k)) + kax (edgeCube v 0 k) v := by
    simpa using kleinPt_corner_add (edgeCube v 0 k) v 1
  have h2 : (2:ℝ) • QbarPD.posR (edgeFace v 0 k)
      = (2:ℝ) • RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k) + (1/2:ℝ) • axVec v) := by
    rw [posR_mid v k hk, h0, h1, kleinPt_corner_add (edgeCube v 0 k) v (1/2), hAx]
    rw [two_smul_half]
  have h3 := congrArg (fun z => (1/2:ℝ) • z) h2
  simpa [smul_smul] using h3

/-- **The affine point of `eNice0`**: `kleinPt` of the cube corner displaced along the edge. -/
lemma ptW_eNice0_eq (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (ww : Fin 2 → ℝ)
    (hsum : ww 0 + ww 1 = 1) :
    Mbar.ptW (eNice0 v k hk) ww
      = RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k) + (ww 1 / 2) • axVec v) := by
  rw [ptW_eNice0 v k hk ww, posR_W0 v k hk, posR_edgeFace v k hk]
  rw [kleinPt_corner_add (edgeCube v 0 k) v (1/2)]
  rw [kleinPt_corner_add (edgeCube v 0 k) v (ww 1 / 2)]
  exact smul_half_aux _ _ (ww 0) (ww 1) hsum

/-- The affine point of `eFlag0` is the sign change of the affine point of `eNice0`. -/
lemma ptW_eFlag0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (ww : Fin 2 → ℝ) :
    Mbar.ptW (eFlag0 v k hk) ww = Work.FoldInst.act (esig v k) (Mbar.ptW (eNice0 v k hk) ww) := by
  rw [show eFlag0 v k hk = Mbar.simplexAct (esig v k) (eNice0 v k hk) from rfl]
  exact Mbar.ptW_simplexAct (esig v k) (eNice0 v k hk) ww

/-! ## §2  The chart point of the lower half -/

/-- The affine point of the chart simplex `[cuspCorner, cuspMid]`. -/
lemma cPt_cuspMid (v : Fin 5) (k : Fin 4) (w : Convexity.StdSimplex ℝ (Fin 2)) :
    cPt ![cuspCorner v k, cuspMid v k] w
      = cuspCorner v k + (w.weights 1 / 2) • axVec v := by
  rw [cPt_eq_sum, Fin.sum_univ_two]
  have hmid : cuspMid v k = cuspCorner v k + (1/2:ℝ) • axVec v := rfl
  rw [hmid]
  have hsum : w.weights 0 + w.weights 1 = 1 := by
    have h := Mbar.sum_weights w
    rwa [Fin.sum_univ_two] at h
  exact smul_half_aux (cuspCorner v k) (axVec v) (w.weights 0) (w.weights 1) hsum

/-- `cuspCorner` is `CP` shifted by `-cuspH`. -/
lemma cuspCorner_add_cuspH (v : Fin 5) (k : Fin 4) :
    cuspCorner v k + RTOwed.cuspH = CP (edgeCube v 0 k) := by
  rw [cuspCorner, RTOwed.cuspH, CP, ← WithLp.toLp_add]
  congr 1
  ext i
  simp only [Pi.add_apply]
  norm_num

/-- The chart point of the lower half of the unit edge, in the cusp coordinates of the chart. -/
lemma mbarPtC_cuspMid (v : Fin 5) (k : Fin 4) (w : Convexity.StdSimplex ℝ (Fin 2)) :
    RTOwed.mbarPtC v (cPt ![cuspCorner v k, cuspMid v k] w)
      = RTOwed.mbarPt v (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v) := by
  rw [cPt_cuspMid v k w, RTOwed.mbarPtC]
  congr 1
  rw [add_assoc, add_comm ((w.weights 1 / 2) • axVec v) RTOwed.cuspH, ← add_assoc,
    cuspCorner_add_cuspH]

/-! ## §3  The cube and floor tables -/

/-- **The table check**: the cube of cusp `v` carrying the corner of `edgeCube v 0 k` is
`edgeCube v 0 k`. -/
lemma cubeOfMod_corner (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Cusp.cubeOfMod v (fun i => Work.Cusp.cubeCorner (edgeCube v 0 k) i)
      = edgeCube v 0 k := by
  decide +revert

/-- The floor of the displaced corner is the corner. -/
lemma floor_CP_add (a : Fin 48) (v : Fin 5) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (i : Fin 3) :
    ⌊(CP a + s • axVec v) i⌋ = Work.Cusp.cubeCorner a i := by
  rw [CP_apply, Int.floor_eq_iff]
  constructor
  · have h : 0 ≤ s * (if i = dirKappa v 1 then (1:ℝ) else 0) := by split_ifs <;> linarith
    push_cast; linarith
  · have h : s * (if i = dirKappa v 1 then (1:ℝ) else 0) ≤ 1/2 := by split_ifs <;> linarith
    push_cast; linarith

lemma cubeOf_CP_add (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) :
    RTOwed.cubeOf v (CP (edgeCube v 0 k) + s • axVec v) = edgeCube v 0 k := by
  have hfloor : RTOwed.floorV (CP (edgeCube v 0 k) + s • axVec v)
      = fun i => Work.Cusp.cubeCorner (edgeCube v 0 k) i := by
    funext i
    rw [RTOwed.floorV]
    exact floor_CP_add (edgeCube v 0 k) v s hs0 hs1 i
  rw [RTOwed.cubeOf, hfloor]
  exact cubeOfMod_corner v k hk

lemma redV_CP_add (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) :
    RTOwed.redV v (CP (edgeCube v 0 k) + s • axVec v) = CP (edgeCube v 0 k) + s • axVec v := by
  have hF : ∀ i : Fin 3,
      ⌊(CP (edgeCube v 0 k) + s • axVec v) i⌋ = Work.Cusp.cubeCorner (edgeCube v 0 k) i :=
    fun i => floor_CP_add (edgeCube v 0 k) v s hs0 hs1 i
  have hC : RTOwed.cubeOf v (CP (edgeCube v 0 k) + s • axVec v) = edgeCube v 0 k :=
    cubeOf_CP_add v k hk s hs0 hs1
  rw [RTOwed.redV, hC]
  rw [show (fun i : Fin 3 => (CP (edgeCube v 0 k) + s • axVec v) i
        - (⌊(CP (edgeCube v 0 k) + s • axVec v) i⌋ : ℝ)
        + (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ))
      = (fun i : Fin 3 =>
          (Work.Cusp.cubeCorner (edgeCube v 0 k) i : ℝ)
            + s * (if i = dirKappa v 1 then (1:ℝ) else 0)) from by
      funext i
      rw [hF i, CP_apply (edgeCube v 0 k) v s i]
      ring]
  rw [CP_add_smul_axVec]

/-! ## §4  The unfolding of `chi` -/

/-- The value of `chi` on the characteristic simplex of the lower half of a unit edge. -/
lemma chi_eSimp0_apply (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0)
    (w : Convexity.StdSimplex ℝ (Fin 2)) :
    Mbar.chi 1 (eSimp0 v k hk) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid 1 (edgeCell v 0 k)), eFlag0 v k hk) w := by
  rw [show Mbar.chi 1 (eSimp0 v k hk) = Mbar.chiQuot 1 (Quotient.mk (flagSetoid 1)
        (Mbar.moRootC (Mbar.moCid 1 (edgeCell v 0 k)), eFlag0 v k hk)) from by
      simp only [eSimp0, Mbar.chi, Mbar.rootSimplex, Equiv.apply_symm_apply]
      rfl]
  rw [Mbar.chiQuot_mk]
  rfl

theorem eChi0_chart (v : Fin 5) (k : Fin 4)
    (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 0) :
    Work.MbarHomology.Mbar.chi 1 (Work.BridgeSquare.eSimp0 v k hk)
      = Work.BridgeSquare.cSimp v
          ![Work.BridgeSquare.cuspCorner v k, Work.BridgeSquare.cuspMid v k] := by
  ext w
  have hsum : w.weights 0 + w.weights 1 = 1 := by
    have h := Mbar.sum_weights w
    rwa [Fin.sum_univ_two] at h
  have hs0 : 0 ≤ w.weights 1 / 2 := by
    have h : 0 ≤ w.weights 1 := w.nonneg 1
    exact div_nonneg h (by norm_num)
  have hs1 : w.weights 1 / 2 ≤ 1 / 2 := by
    have h0 : 0 ≤ w.weights 0 := w.nonneg 0
    have h1 : w.weights 1 ≤ 1 := by
      rw [← hsum]
      exact le_add_of_nonneg_left h0
    linarith
  rw [chi_eSimp0_apply v k hk w, Mbar.chiRep, Mbar.chiPt, cSimp_apply,
    mbarPtC_cuspMid v k w, RTOwed.mbarPt_eq_mk]
  refine Quotient.sound ⟨Mbar.Enode (ebit v k) (edgeFace v 0 k), ?_, ?_⟩
  · show Mbar.Enode (ebit v k) (edgeFace v 0 k)
        ∈ FoldInst.Ksub (Mbar.ptW (eFlag0 v k hk) (fun i => w.weights i))
    rw [ptW_eFlag0, Work.FoldInst.Ksub_act]
    have hbary : FoldInst.Ksub (bary (eNice0 v k hk)) = Mbar.KsubAtlas (edgeFace v 0 k) := by
      rw [Mbar.Ksub_bary_eq_KsubAtlas]
      exact congrArg Mbar.KsubAtlas (topIdx_eNice0_aux v k hk)
    have hle : FoldInst.Ksub (bary (eNice0 v k hk))
        ≤ FoldInst.Ksub (Mbar.ptW (eNice0 v k hk) (fun i => w.weights i)) :=
      Mbar.Ksub_bary_le (eNice0 v k hk) (fun i => w.nonneg i) (Mbar.sum_weights w)
    refine hle ?_
    rw [hbary]
    exact Mbar.Enode_mem_KsubAtlas _ _
  · refine Prod.ext ?_ ?_
    · show Mbar.moRootC (Mbar.moCid 1 (edgeCell v 0 k))
          + (ebit v k + Mbar.moRootC (Mbar.moCell (ebit v k) (edgeFace v 0 k)))
        = RTOwed.cubeBit (RTOwed.cubeOf v (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v))
      rw [moCell_ebit_edgeFace v k hk, cubeOf_CP_add v k hk (w.weights 1 / 2) hs0 hs1,
        show RTOwed.cubeBit (edgeCube v 0 k) = ebit v k from rfl]
      rw [← add_assoc, add_comm (Mbar.moRootC (Mbar.moCid 1 (edgeCell v 0 k))) (ebit v k),
        add_assoc, Work.FoldInst.ZMod2_add_self, add_zero]
    · refine Subtype.ext ?_
      show FoldInst.act (esig v k) (Mbar.ptW (eFlag0 v k hk) (fun i => w.weights i))
        = RTOwed.kleinPt (RTOwed.cubeOf v (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v))
            (RTOwed.redV v (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v))
      rw [ptW_eFlag0, Work.FoldInst.act_add,
        show esig v k + esig v k = 0 from funext fun i => Work.FoldInst.ZMod2_add_self _,
        Work.FoldInst.act_zero, ptW_eNice0_eq v k hk (fun i => w.weights i) hsum]
      show RTOwed.kleinPt (edgeCube v 0 k) (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v)
        = RTOwed.kleinPt (RTOwed.cubeOf v (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v))
            (RTOwed.redV v (CP (edgeCube v 0 k) + (w.weights 1 / 2) • axVec v))
      rw [cubeOf_CP_add v k hk (w.weights 1 / 2) hs0 hs1,
        redV_CP_add v k hk (w.weights 1 / 2) hs0 hs1]

end

end Work.BridgeSquare
