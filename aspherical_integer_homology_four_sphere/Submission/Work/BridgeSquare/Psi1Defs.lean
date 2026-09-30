/-
# `BridgeSquare/Psi1Defs.lean` — the vocabulary and geometry of the `κ_{v,3}` unit edges

This module is the `j = 1` analogue of `BridgeSquare/CellChiADefs.lean` (the `κ_{v,2}` case).

For every cusp `v` and every unit edge `k < fibreLen v 1` of the `κ_{v,3}`-longitude we record

* the cube `edgeCube v 1 k` carrying the edge and its cusp chart coordinates
  `Yv v k t = cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1) − cuspH`;
* the cell `edgeCell v 1 k` of `C_1(mbarCx)` and the two characteristic `1`-simplices `eFlag0`,
  `eFlag1` of its subdivision, with their images `eChi0`, `eChi1` in `C_1(M̄)`;
* the table facts identifying the facets `eU0`, `eU1` of the root face `eRoot` with the two ends
  of the edge, and the coefficient identity `eBeta v k = edgeSign v 1 k * cpsi v`
  (`eBeta_eq`);
* the affine geometry (`kleinPt` affinity, the floor/cube/representative of a point of a cube
  edge) and the unfolding of the characteristic maps.

Everything is in the namespace `Work.BridgeSquare.Psi1`, so that the two chart identifications
(`Psi1L.eChi0_chart`, `Psi1U.eChi1_chart`) can be developed independently.
-/
import Mathlib
import Submission.Work.BridgeSquare.CellChiADefs
import Submission.Work.BridgeSquare.edgeFace_struct_j1
import Submission.Work.BridgeSquare.posR_facts_j1
import Submission.Work.BridgeSquare.pieceDefs
import Submission.Work.BridgeSquare.subdivCell_one_apply

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.MbarHomology

namespace Work.BridgeSquare
namespace Psi1

noncomputable section

/-! ## §1  The vocabulary -/

/-- The copy bit of the cube carrying the `k`-th unit edge of the `κ_{v,3}`-loop. -/
def ebit (v : Fin 5) (k : Fin 4) : ZMod 2 := cubeBitF (edgeCube v 1 k)

/-- The sign vector of the node of the `k`-th unit edge of the `κ_{v,3}`-loop. -/
def esig (v : Fin 5) (k : Fin 4) : Fin 4 → ZMod 2 :=
  Mbar.sigVec (ebit v k) (edgeFace v 1 k)

/-- The root face of the cell `edgeCell v 1 k`, as an index. -/
def eRootI (v : Fin 5) (k : Fin 4) : Fin 865 :=
  Mbar.moRoot (Mbar.moCid (1 : Fin 5) (edgeCell v 1 k))

/-- The root face of the cell `edgeCell v 1 k`, as a `1`-cell of `Q̄`. -/
def eRoot (v : Fin 5) (k : Fin 4) : QbarCell := ⟨eRootI v k⟩

/-- The lower facet of the root face: the image of the lower end of the unit edge. -/
def eU0 (v : Fin 5) (k : Fin 4) : QbarCell := ⟨faceAct (esig v k) (edgeW0Face v 1 k)⟩

/-- The upper facet of the root face: the image of the upper end of the unit edge. -/
def eU1 (v : Fin 5) (k : Fin 4) : QbarCell := ⟨faceAct (esig v k) (edgeW1Face v 1 k)⟩

/-- The coefficient of the per-cell identity of the `κ_{v,3}` unit edge. -/
def eBeta (v : Fin 5) (k : Fin 4) : ℤ := qInc (eRootI v k) (eU0 v k).idx

/-- The cube-coordinate axis vector of the `κ_{v,3}` loop. -/
def eAx (v : Fin 5) : cE3 := eVec (fibreDir v 1)

/-- The `k`-th unit edge as a subdivision `1`-simplex of `Q̄` (lower vertex, ridge). -/
def eNice0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Work.Subdivision.Simplex.snoc
    (Work.Subdivision.Simplex.vertex (⟨edgeW0Face v 1 k⟩ : QbarCell))
    (⟨edgeFace v 1 k⟩ : QbarCell)
    (fun _ => QbarCW.facet_lt (by
      rw [(edgeFace_struct_j1 v k hk).2.1]
      exact Finset.mem_insert_self _ _))

/-- The `k`-th unit edge as a subdivision `1`-simplex of `Q̄` (upper vertex, ridge). -/
def eNice1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Work.Subdivision.Simplex.snoc
    (Work.Subdivision.Simplex.vertex (⟨edgeW1Face v 1 k⟩ : QbarCell))
    (⟨edgeFace v 1 k⟩ : QbarCell)
    (fun _ => QbarCW.facet_lt (by
      rw [(edgeFace_struct_j1 v k hk).2.1]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- The lower characteristic simplex of the edge, in the subdivision of `Q̄`. -/
def eFlag0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Mbar.flagAct (esig v k) (eNice0 v k hk)

/-- The upper characteristic simplex of the edge, in the subdivision of `Q̄`. -/
def eFlag1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Mbar.flagAct (esig v k) (eNice1 v k hk)

/-- The characteristic simplex of the lower half of the `k`-th unit edge, in `mbarSd`. -/
def eSimp0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) : Fin (mbarCard 1) :=
  Mbar.rootSimplex 1 (by norm_num) (edgeCell v 1 k) (eFlag0 v k hk)

/-- The characteristic simplex of the upper half of the `k`-th unit edge, in `mbarSd`. -/
def eSimp1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) : Fin (mbarCard 1) :=
  Mbar.rootSimplex 1 (by norm_num) (edgeCell v 1 k) (eFlag1 v k hk)

/-- The image of the lower characteristic simplex in `C_1(M̄)`. -/
def eChi0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    (singCxFun.obj cMtop).X 1 := singGen (Mbar.chi 1 (eSimp0 v k hk))

/-- The image of the upper characteristic simplex in `C_1(M̄)`. -/
def eChi1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    (singCxFun.obj cMtop).X 1 := singGen (Mbar.chi 1 (eSimp1 v k hk))

/-! ## §2  The table facts -/

/-- The two vertices of the ridge of the `k`-th unit edge are exactly its facets. -/
theorem facets_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    QbarCW.facets (⟨edgeFace v 1 k⟩ : QbarCell)
      = {(⟨edgeW0Face v 1 k⟩ : QbarCell), (⟨edgeW1Face v 1 k⟩ : QbarCell)} :=
  (edgeFace_struct_j1 v k hk).2.1

/-- The root face of the cell of the `k`-th unit edge is the image of the ridge under the sign
change. -/
theorem eRootI_eq_faceAct_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    faceAct (esig v k) (edgeFace v 1 k) = eRootI v k := by decide +kernel

theorem eRootI_eq_faceAct (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    faceAct (esig v k) (edgeFace v 1 k) = eRootI v k :=
  eRootI_eq_faceAct_aux v k hk

/-- The node `(ebit v k, edgeFace v 1 k)` is the root node of the cell `edgeCell v 1 k`. -/
theorem moCell_ebit_edgeFace_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    Mbar.moCell (ebit v k) (edgeFace v 1 k) = Mbar.moCid (1 : Fin 5) (edgeCell v 1 k) := by
  decide +kernel

theorem moCell_ebit_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.moCell (ebit v k) (edgeFace v 1 k) = Mbar.moCid (1 : Fin 5) (edgeCell v 1 k) :=
  moCell_ebit_edgeFace_aux v k hk

/-- The two facets of the root face are `eU0` and `eU1`. -/
theorem facets_eRoot_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    QbarCW.facets (eRoot v k) = {eU0 v k, eU1 v k} := by decide +kernel

theorem facets_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    QbarCW.facets (eRoot v k) = {eU0 v k, eU1 v k} :=
  facets_eRoot_aux v k hk

theorem eU0_lt_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    eU0 v k < eRoot v k :=
  QbarCW.facet_lt (by rw [facets_eRoot v k hk]; exact Finset.mem_insert_self _ _)

theorem eU1_lt_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    eU1 v k < eRoot v k :=
  QbarCW.facet_lt (by
    rw [facets_eRoot v k hk]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The two facets of the root face are distinct. -/
theorem eU0_ne_eU1_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    eU0 v k ≠ eU1 v k := by decide +kernel

theorem eU0_ne_eU1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    eU0 v k ≠ eU1 v k := eU0_ne_eU1_aux v k hk

/-- The two incidences at the root face are opposite. -/
theorem qInc_eU1_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    qInc (eRootI v k) (eU1 v k).idx = -qInc (eRootI v k) (eU0 v k).idx := by decide +kernel

theorem qInc_eU1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    qInc (eRootI v k) (eU1 v k).idx = -qInc (eRootI v k) (eU0 v k).idx :=
  qInc_eU1_aux v k hk

/-- The root face of the cell of the `k`-th unit edge is a `1`-cell. -/
theorem dim_eRoot_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    QbarCW.dim (eRoot v k) = 1 := by decide +kernel

theorem dim_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    QbarCW.dim (eRoot v k) = 1 := dim_eRoot_aux v k hk

/-- **The coefficient of the identity**: `eBeta` is the fibre-loop sign times the cusp sign. -/
theorem eBeta_eq : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 1 →
    eBeta v k = edgeSign v 1 k * cpsi v := by decide +kernel

/-- The coefficient of `rootCoeff` of the subdivision chain of the root face. -/
theorem rootCoeff_eq (v : Fin 5) (k : Fin 4) (s : Work.Subdivision.Simplex QbarCW.Cell 1) :
    Mbar.mbarAtlasOf.rootCoeff 1 (edgeCell v 1 k) s
      = if s (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 1 k) then
          -(qInc (eRootI v k) (s 0).idx) else 0 := by
  show Work.Subdivision.PolyCW.subdivCell QbarCW 1
      ⟨Mbar.rootCx 1 (edgeCell v 1 k), Mbar.rootCx_dim 1 (edgeCell v 1 k)⟩ s = _
  rw [Work.BridgeSquare.subdivCell_one_apply (P := QbarCW) (Mbar.rootCx 1 (edgeCell v 1 k))
    (Mbar.rootCx_dim 1 (edgeCell v 1 k)) s]
  simp only [QbarCW_inc]
  rfl

/-- The top vertex of the lower characteristic simplex is the ridge. -/
theorem topIdx_eNice0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.topIdx (eNice0 v k hk) = edgeFace v 1 k := rfl

/-- The top vertex of the upper characteristic simplex is the ridge. -/
theorem topIdx_eNice1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.topIdx (eNice1 v k hk) = edgeFace v 1 k := rfl

/-! ## §3  Elementary linear algebra -/

/-- A sum with an indicator factor collapses to the selected term. -/
theorem sum_mul_ind {A : Fin 3 → ℝ} (i0 : Fin 3) :
    ∑ j : Fin 3, A j * (if j = i0 then (1 : ℝ) else 0) = A i0 := by
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i0) h

/-- Splitting a sum with a shifted argument. -/
theorem sum_add_ind (A c : Fin 3 → ℝ) (s : ℝ) (i0 : Fin 3) :
    ∑ j : Fin 3, A j * (c j + s * (if j = i0 then (1 : ℝ) else 0))
      = (∑ j : Fin 3, A j * c j) + s * A i0 := by
  have h : ∀ j : Fin 3, A j * (c j + s * (if j = i0 then (1 : ℝ) else 0))
      = A j * c j + s * (A j * (if j = i0 then (1 : ℝ) else 0)) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_mul_ind (A := A) i0]

/-- Two elementary linear identities in a module. -/
theorem smul_half_aux {M : Type*} [AddCommGroup M] [Module ℝ M] (K Y : M) (p q : ℝ)
    (h : p + q = 1) : p • K + q • (K + (1/2 : ℝ) • Y) = K + (q / 2) • Y := by
  have h1 : q • (K + (1/2 : ℝ) • Y) = q • K + (q / 2) • Y := by
    rw [smul_add, smul_smul, show q * (1/2 : ℝ) = q / 2 by ring]
  rw [h1, ← add_assoc, ← add_smul, h, one_smul]

theorem two_smul_half {M : Type*} [AddCommGroup M] [Module ℝ M] (K Y : M) :
    (2 : ℝ) • (K + (1/2 : ℝ) • Y) = K + (K + Y) := by
  rw [smul_add, smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul, two_smul ℝ K]
  abel

/-- The two-endpoint form of the affinity. -/
theorem smul_pair_aux {M : Type*} [AddCommGroup M] [Module ℝ M] (K Y : M) (w0 w1 : ℝ)
    (h : w0 + w1 = 1) :
    w0 • (K + Y) + w1 • (K + (1/2 : ℝ) • Y) = K + (w0 + w1 / 2) • Y := by
  have h1 : w0 • (K + Y) + w1 • (K + (1/2 : ℝ) • Y)
      = (w0 + w1) • K + (w0 + w1 / 2) • Y := by
    rw [smul_add, smul_add, smul_smul,
      show w1 * (1/2 : ℝ) = w1 / 2 from by ring, add_smul, add_smul]
    abel
  rw [h1, h, one_smul]

/-! ## §4  The affine geometry of the cube edge -/

/-- `cornerPt a + s • eVec j`, as an explicit `toLp`. -/
theorem cornerPt_add_smul_eVec (a : Fin 48) (j : Fin 3) (s : ℝ) :
    cornerPt a + s • eVec j
      = WithLp.toLp 2 (fun i : Fin 3 =>
          (Work.Cusp.cubeCorner a i : ℝ) + s * (if i = j then (1 : ℝ) else 0)) := by
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_toLp, cornerPt_ofLp, eVec_ofLp,
    smul_eq_mul]
  try ring

theorem ofLp_cornerPt_add (a : Fin 48) (j : Fin 3) (s : ℝ) (i : Fin 3) :
    (cornerPt a + s • eVec j).ofLp i
      = (Work.Cusp.cubeCorner a i : ℝ) + s * (if i = j then (1 : ℝ) else 0) := by
  rw [cornerPt_add_smul_eVec]

theorem ofLp_cornerPt_add_eVec (a : Fin 48) (j : Fin 3) (i : Fin 3) :
    (cornerPt a + eVec j).ofLp i
      = (Work.Cusp.cubeCorner a i : ℝ) + (if i = j then (1 : ℝ) else 0) := by
  rw [← one_smul ℝ (eVec j), ofLp_cornerPt_add]
  simp

/-- `cornerPt a + 1 • eVec j`, as an explicit `toLp`. -/
theorem cornerPt_add_one_smul_eVec (a : Fin 48) (j : Fin 3) :
    cornerPt a + (1 : ℝ) • eVec j
      = WithLp.toLp 2 (fun i : Fin 3 =>
          (Work.Cusp.cubeCorner a i : ℝ) + (if i = j then (1 : ℝ) else 0)) := by
  rw [cornerPt_add_smul_eVec a j 1]
  congr 1
  funext i
  ring

/-- The image of the axis direction under the linear part of `kleinPt a`. -/
def kax (a : Fin 48) (j : Fin 3) : RTOwed.CuspE4 :=
  WithLp.toLp 2 fun i : Fin 4 => ((Work.Cusp.cubeXToKlein a) i j : ℝ)

/-- **The affinity of `kleinPt` along the cube corner.** -/
theorem kleinPt_corner_add (a : Fin 48) (j : Fin 3) (s : ℝ) :
    RTOwed.kleinPt a (cornerPt a + s • eVec j) = RTOwed.kleinPt a (cornerPt a) + s • kax a j := by
  ext i
  simp only [RTOwed.kleinPt, cornerPt, kax, eVec, WithLp.ofLp_toLp, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [sum_add_ind (A := fun j => (Work.Cusp.cubeXToKlein a i j : ℝ))
        (c := fun j => (Work.Cusp.cubeCorner a j : ℝ)) s j]
  ring

/-! ## §5  The corner edge `Yv` in the cusp chart -/

theorem Yv_zero_add_cuspH (v : Fin 5) (k : Fin 4) :
    Yv v k 0 + RTOwed.cuspH = cornerPt (edgeCube v 1 k) := by
  rw [Yv]
  simp only [zero_smul, add_zero, one_smul]
  abel

theorem Yv_half_eq (v : Fin 5) (k : Fin 4) :
    Yv v k (1 / 2) = Yv v k 0 + (1 / 2 : ℝ) • eVec (fibreDir v 1) := by
  rw [Yv, Yv]
  simp only [zero_smul, add_zero, one_smul]
  abel

theorem Yv_one_eq (v : Fin 5) (k : Fin 4) :
    Yv v k 1 = Yv v k 0 + eVec (fibreDir v 1) := by
  rw [Yv, Yv]
  simp only [zero_smul, add_zero, one_smul]
  abel

/-- The affine point of the lower chart simplex `[Yv k 0, Yv k ½]`. -/
theorem cPt_Yv_low (v : Fin 5) (k : Fin 4) (w : Convexity.StdSimplex ℝ (Fin 2)) :
    cPt ![Yv v k 0, Yv v k (1 / 2)] w
      = Yv v k 0 + (w.weights 1 / 2) • eVec (fibreDir v 1) := by
  rw [cPt_eq_sum, Fin.sum_univ_two, Yv_half_eq v k]
  have hsum : w.weights 0 + w.weights 1 = 1 := by
    have h := Mbar.sum_weights w
    rwa [Fin.sum_univ_two] at h
  exact smul_half_aux (Yv v k 0) (eVec (fibreDir v 1)) (w.weights 0) (w.weights 1) hsum

/-- The chart point of the lower half of the unit edge. -/
theorem mbarPtC_Yv_low (v : Fin 5) (k : Fin 4) (w : Convexity.StdSimplex ℝ (Fin 2)) :
    RTOwed.mbarPtC v (cPt ![Yv v k 0, Yv v k (1 / 2)] w)
      = RTOwed.mbarPt v (cornerPt (edgeCube v 1 k) + (w.weights 1 / 2) • eVec (fibreDir v 1)) := by
  rw [cPt_Yv_low v k w, RTOwed.mbarPtC]
  congr 1
  rw [show Yv v k 0 + (w.weights 1 / 2) • eVec (fibreDir v 1) + RTOwed.cuspH
        = (Yv v k 0 + RTOwed.cuspH) + (w.weights 1 / 2) • eVec (fibreDir v 1) from by abel,
      Yv_zero_add_cuspH v k]

/-- The affine point of the upper chart simplex `[Yv k 1, Yv k ½]`, in cusp coordinates. -/
theorem cPt_Yv_top (v : Fin 5) (k : Fin 4) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    cPt ![Yv v k 1, Yv v k (1 / 2)] z + RTOwed.cuspH
      = cornerPt (edgeCube v 1 k) + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1) := by
  have hsum2 : z.weights 0 + z.weights 1 = 1 := by
    have h := Mbar.sum_weights z
    rw [Fin.sum_univ_two] at h
    exact h
  have hpt : cPt ![Yv v k 1, Yv v k (1 / 2)] z
      = z.weights 0 • Yv v k 1 + z.weights 1 • Yv v k (1 / 2) := by
    rw [cPt_eq_sum, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hpt]
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, Yv, cornerPt, eVec, RTOwed.cuspH, PiLp.sub_apply,
    smul_eq_mul]
  linear_combination ((Work.Cusp.cubeCorner (edgeCube v 1 k) i : ℝ) - 1 / 2) * hsum2

/-- The chart point of the upper half of the unit edge. -/
theorem mbarPtC_Yv_top (v : Fin 5) (k : Fin 4) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    RTOwed.mbarPtC v (cPt ![Yv v k 1, Yv v k (1 / 2)] z)
      = RTOwed.mbarPt v
          (cornerPt (edgeCube v 1 k) + (z.weights 0 + z.weights 1 / 2) • eVec (fibreDir v 1)) := by
  rw [RTOwed.mbarPtC]
  congr 1
  exact cPt_Yv_top v k z

/-! ## §6  The polytope points of the two ends of the edge -/

theorem posR_W0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    QbarPD.posR (edgeW0Face v 1 k)
      = RTOwed.kleinPt (edgeCube v 1 k) (cornerPt (edgeCube v 1 k)) := by
  apply PiLp.ext
  intro i
  rw [(posR_facts_j1 v k hk).1 i]
  rfl

theorem posR_W1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    QbarPD.posR (edgeW1Face v 1 k)
      = RTOwed.kleinPt (edgeCube v 1 k)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            (Work.Cusp.cubeCorner (edgeCube v 1 k) j : ℝ)
              + (if j = fibreDir v 1 then (1 : ℝ) else 0))) := by
  apply PiLp.ext
  intro i
  rw [(posR_facts_j1 v k hk).2.1 i]

theorem posR_mid (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    (2 : ℝ) • QbarPD.posR (edgeFace v 1 k)
      = QbarPD.posR (edgeW0Face v 1 k) + QbarPD.posR (edgeW1Face v 1 k) :=
  (posR_facts_j1 v k hk).2.2

/-- The affine point of the ridge, in the Klein coordinates of the cube corner. -/
theorem posR_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    QbarPD.posR (edgeFace v 1 k)
      = RTOwed.kleinPt (edgeCube v 1 k)
          (cornerPt (edgeCube v 1 k) + (1 / 2 : ℝ) • eVec (fibreDir v 1)) := by
  have hAx : RTOwed.kleinPt (edgeCube v 1 k)
        (WithLp.toLp 2 (fun j : Fin 3 =>
          (Work.Cusp.cubeCorner (edgeCube v 1 k) j : ℝ)
            + (if j = fibreDir v 1 then (1 : ℝ) else 0)))
      = RTOwed.kleinPt (edgeCube v 1 k) (cornerPt (edgeCube v 1 k))
          + kax (edgeCube v 1 k) (fibreDir v 1) := by
    rw [← cornerPt_add_one_smul_eVec (edgeCube v 1 k) (fibreDir v 1)]
    simpa using kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) 1
  have h2 : (2 : ℝ) • QbarPD.posR (edgeFace v 1 k)
      = (2 : ℝ) • RTOwed.kleinPt (edgeCube v 1 k)
          (cornerPt (edgeCube v 1 k) + (1 / 2 : ℝ) • eVec (fibreDir v 1)) := by
    rw [posR_mid v k hk, posR_W0 v k hk, posR_W1 v k hk,
      kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) (1 / 2), hAx]
    rw [two_smul_half]
  have h3 := congrArg (fun z => (1 / 2 : ℝ) • z) h2
  simpa [smul_smul] using h3

/-! ## §7  The affine point of the characteristic simplices -/

theorem flagIdx_eNice0_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.flagIdx (eNice0 v k hk) 0 = edgeW0Face v 1 k := rfl

theorem flagIdx_eNice0_one (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.flagIdx (eNice0 v k hk) 1 = edgeFace v 1 k := rfl

theorem flagIdx_eNice1_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.flagIdx (eNice1 v k hk) 0 = edgeW1Face v 1 k := rfl

theorem flagIdx_eNice1_one (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Mbar.flagIdx (eNice1 v k hk) 1 = edgeFace v 1 k := rfl

theorem ptW_eNice0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) (ww : Fin 2 → ℝ) :
    Mbar.ptW (eNice0 v k hk) ww
      = ww 0 • QbarPD.posR (edgeW0Face v 1 k) + ww 1 • QbarPD.posR (edgeFace v 1 k) := by
  rw [Mbar.ptW, Fin.sum_univ_two]
  rw [flagIdx_eNice0_zero v k hk, flagIdx_eNice0_one v k hk]

theorem ptW_eNice1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) (ww : Fin 2 → ℝ) :
    Mbar.ptW (eNice1 v k hk) ww
      = ww 0 • QbarPD.posR (edgeW1Face v 1 k) + ww 1 • QbarPD.posR (edgeFace v 1 k) := by
  rw [Mbar.ptW, Fin.sum_univ_two]
  rw [flagIdx_eNice1_zero v k hk, flagIdx_eNice1_one v k hk]

/-- **The affine point of `eNice0`**: `kleinPt` of the cube corner displaced along the edge. -/
theorem ptW_eNice0_eq (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) (ww : Fin 2 → ℝ)
    (hsum : ww 0 + ww 1 = 1) :
    Mbar.ptW (eNice0 v k hk) ww
      = RTOwed.kleinPt (edgeCube v 1 k)
          (cornerPt (edgeCube v 1 k) + (ww 1 / 2) • eVec (fibreDir v 1)) := by
  rw [ptW_eNice0 v k hk ww, posR_W0 v k hk, posR_edgeFace v k hk]
  rw [kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) (1 / 2)]
  rw [kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) (ww 1 / 2)]
  exact smul_half_aux _ _ (ww 0) (ww 1) hsum

/-- **The affine point of `eNice1`**. -/
theorem ptW_eNice1_eq (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) (ww : Fin 2 → ℝ)
    (hsum : ww 0 + ww 1 = 1) :
    Mbar.ptW (eNice1 v k hk) ww
      = RTOwed.kleinPt (edgeCube v 1 k)
          (cornerPt (edgeCube v 1 k) + (ww 0 + ww 1 / 2) • eVec (fibreDir v 1)) := by
  rw [ptW_eNice1 v k hk ww, posR_W1 v k hk, posR_edgeFace v k hk]
  rw [← cornerPt_add_one_smul_eVec (edgeCube v 1 k) (fibreDir v 1)]
  rw [kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) 1,
    kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) (1 / 2),
    kleinPt_corner_add (edgeCube v 1 k) (fibreDir v 1) (ww 0 + ww 1 / 2)]
  rw [one_smul]
  exact smul_pair_aux _ _ (ww 0) (ww 1) hsum

/-- The affine point of the lower characteristic simplex. -/
theorem ptW_eFlag0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) (w : Fin 2 → ℝ) :
    Mbar.ptW (eFlag0 v k hk) w
      = Work.FoldInst.act (esig v k) (Mbar.ptW (eNice0 v k hk) w) := by
  rw [show eFlag0 v k hk = Mbar.simplexAct (esig v k) (eNice0 v k hk) from rfl]
  exact Mbar.ptW_simplexAct (esig v k) (eNice0 v k hk) w

/-- The affine point of the upper characteristic simplex. -/
theorem ptW_eFlag1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) (w : Fin 2 → ℝ) :
    Mbar.ptW (eFlag1 v k hk) w
      = Work.FoldInst.act (esig v k) (Mbar.ptW (eNice1 v k hk) w) := by
  rw [show eFlag1 v k hk = Mbar.simplexAct (esig v k) (eNice1 v k hk) from rfl]
  exact Mbar.ptW_simplexAct (esig v k) (eNice1 v k hk) w

/-! ## §8  The floor, the cube and the representative of a point of a cube edge -/

theorem floor_coord (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (i : Fin 3) :
    ⌊(cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i⌋
      = Work.Cusp.cubeCorner (edgeCube v 1 k) i := by
  rw [ofLp_cornerPt_add]
  rw [Int.floor_eq_iff]
  constructor <;> split_ifs <;> linarith

theorem floorV_corner (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    Work.RTOwed.floorV (cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1))
      = Work.Cusp.cubeCorner (edgeCube v 1 k) := by
  funext i
  show ⌊(cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i⌋ = _
  exact floor_coord v k t h0 h1 i

theorem cubeOfMod_corner (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    Work.Cusp.cubeOfMod v (Work.Cusp.cubeCorner (edgeCube v 1 k)) = edgeCube v 1 k := by
  fin_cases v <;> fin_cases k <;>
    first | (exfalso; revert hk; decide) | decide

theorem cubeOf_corner (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1)
    (hk : (k : ℕ) < fibreLen v 1) :
    Work.RTOwed.cubeOf v (cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1))
      = edgeCube v 1 k := by
  rw [Work.RTOwed.cubeOf, floorV_corner v k t h0 h1, cubeOfMod_corner v k hk]

theorem redV_corner (v : Fin 5) (k : Fin 4) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1)
    (hk : (k : ℕ) < fibreLen v 1) :
    Work.RTOwed.redV v (cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1))
      = cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1) := by
  rw [Work.RTOwed.redV, cubeOf_corner v k t h0 h1 hk]
  show WithLp.toLp 2 (fun i : Fin 3 =>
      (cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i
      - ↑⌊(cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i⌋
      + (Work.Cusp.cubeCorner (edgeCube v 1 k) i : ℝ))
    = cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)
  rw [show (fun i : Fin 3 =>
        (cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i
        - ↑⌊(cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i⌋
        + (Work.Cusp.cubeCorner (edgeCube v 1 k) i : ℝ))
      = (fun i : Fin 3 =>
          (cornerPt (edgeCube v 1 k) + t • eVec (fibreDir v 1)).ofLp i) from by
    funext i
    rw [floor_coord v k t h0 h1 i]; ring]

theorem mem_cubeBox_corner (v : Fin 5) (k : Fin 4) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    cornerPt (edgeCube v 1 k) + s • eVec (fibreDir v 1) ∈ Work.RTOwed.cubeBox (edgeCube v 1 k) := by
  show ∀ i : Fin 3, (Work.Cusp.cubeCorner (edgeCube v 1 k) i : ℝ)
      ≤ (cornerPt (edgeCube v 1 k) + s • eVec (fibreDir v 1)).ofLp i
    ∧ (cornerPt (edgeCube v 1 k) + s • eVec (fibreDir v 1)).ofLp i
      ≤ (Work.Cusp.cubeCorner (edgeCube v 1 k) i : ℝ) + 1
  intro i
  rw [ofLp_cornerPt_add]
  constructor <;> split_ifs <;> linarith

/-! ## §9  Unfolding the characteristic map -/

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
            (Mbar.moRootC (Mbar.moCid ⟨n, hn⟩ e), s) from Equiv.apply_symm_apply _ _]
    exact Mbar.chiQuot_mk n _
  rw [h1]
  rfl

theorem mk_eq_of_rel {x y : Work.FoldInst.Xbar} (h : Work.FoldInst.rel x y) :
    Work.FoldInst.mk x = Work.FoldInst.mk y :=
  Quotient.sound (s := Work.FoldInst.setoid) h

theorem mbar_mk_congr {b b' : ZMod 2} {q q' : Work.FoldInst.E4} {h : q ∈ Work.FoldInst.Qbar}
    {h' : q' ∈ Work.FoldInst.Qbar} (hb : b = b') (hq : q = q') :
    (Work.FoldInst.mk (b, ⟨q, h⟩) : Work.FoldInst.Mbar)
      = Work.FoldInst.mk (b', ⟨q', h'⟩) :=
  congrArg Work.FoldInst.mk (Prod.ext hb (Subtype.ext hq))

/-! ## §10  The identification group of the node -/

theorem zmod2_add_swap (a b : ZMod 2) : a + (b + a) = b := by
  rw [add_comm a (b + a), add_assoc, Work.FoldInst.ZMod2_add_self, add_zero]

theorem act_esig_self (v : Fin 5) (k : Fin 4) (y : Work.FoldInst.E4) :
    Work.FoldInst.act (esig v k) (Work.FoldInst.act (esig v k) y) = y := by
  rw [Work.FoldInst.act_add]
  have h : esig v k + esig v k = 0 := by funext i; exact Work.FoldInst.ZMod2_add_self _
  rw [h, Work.FoldInst.act_zero]

theorem cubeBit_edgeCube (v : Fin 5) (k : Fin 4) :
    Work.RTOwed.cubeBit (edgeCube v 1 k) = ebit v k := rfl

/-- The second component of the node group element. -/
theorem enode_snd (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 1) :
    (Mbar.Enode (ebit v k) (edgeFace v 1 k)).2
      = ebit v k + Mbar.moRootC (Mbar.moCid (1 : Fin 5) (edgeCell v 1 k)) := by
  show ebit v k + Mbar.moRootC (Mbar.moCell (ebit v k) (edgeFace v 1 k)) = _
  rw [moCell_ebit_edgeFace v k hk]

/-- The node group element of the edge acts inside the identification group of every point of
the closed star of the ridge. -/
theorem enode_mem_Ksub {v : Fin 5} {k : Fin 4}
    {s : Work.Subdivision.Simplex QbarCW.Cell 1}
    (h : Mbar.topIdx s = edgeFace v 1 k) (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    Mbar.Enode (ebit v k) (edgeFace v 1 k) ∈ Work.FoldInst.Ksub (Mbar.ptW s w) := by
  refine Mbar.Ksub_bary_le s hw hsum ?_
  rw [Mbar.Ksub_bary_eq_KsubAtlas]
  show Mbar.Enode (ebit v k) (edgeFace v 1 k) ∈ Mbar.KsubAtlas (Mbar.topIdx s)
  rw [h]
  exact Mbar.Enode_mem_KsubAtlas (ebit v k) (edgeFace v 1 k)

end
end Psi1
end Work.BridgeSquare
