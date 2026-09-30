/-
# `BridgeSquare/CellChiADefs.lean` — the vocabulary of the per-cell `A`-identity `cellChiA`
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreGeomDataA
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.MbarHomology.Mbar.AtlasKsub

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.MbarHomology

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The vocabulary -/

/-- The copy bit of the cube carrying the `k`-th unit edge of the `κ_{v,2}`-loop. -/
def ebit (v : Fin 5) (k : Fin 4) : ZMod 2 := cubeBitF (edgeCube v 0 k)

/-- The sign vector of the node of the `k`-th unit edge. -/
def esig (v : Fin 5) (k : Fin 4) : Fin 4 → ZMod 2 :=
  Mbar.sigVec (ebit v k) (edgeFace v 0 k)

/-- The root face of the cell `edgeCell v 0 k`, as an index. -/
def eRootI (v : Fin 5) (k : Fin 4) : Fin 865 :=
  Mbar.moRoot (Mbar.moCid 1 (edgeCell v 0 k))

/-- The root face of the cell `edgeCell v 0 k`, as a `1`-cell of `Q̄`. -/
def eRoot (v : Fin 5) (k : Fin 4) : QbarCell := ⟨eRootI v k⟩

/-- The lower facet of the root face: the image of the lower end of the unit edge. -/
def eU0 (v : Fin 5) (k : Fin 4) : QbarCell := ⟨faceAct (esig v k) (edgeW0Face v 0 k)⟩

/-- The upper facet of the root face: the image of the upper end of the unit edge. -/
def eU1 (v : Fin 5) (k : Fin 4) : QbarCell := ⟨faceAct (esig v k) (edgeW1Face v 0 k)⟩

/-- The coefficient of the per-cell identity. -/
def eBeta (v : Fin 5) (k : Fin 4) : ℤ := qInc (eRootI v k) (eU0 v k).idx

/-! ## §2  The two characteristic simplices of a unit edge -/

/-- The `k`-th unit edge as a subdivision `1`-simplex of `Q̄` (lower vertex, ridge). -/
def eNice0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Work.Subdivision.Simplex.snoc
    (Work.Subdivision.Simplex.vertex (⟨edgeW0Face v 0 k⟩ : QbarCell))
    (⟨edgeFace v 0 k⟩ : QbarCell)
    (fun _ => QbarCW.facet_lt (by
      rw [facets_edgeFace v k hk]
      exact Finset.mem_insert_self _ _))

/-- The `k`-th unit edge as a subdivision `1`-simplex of `Q̄` (upper vertex, ridge). -/
def eNice1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Work.Subdivision.Simplex.snoc
    (Work.Subdivision.Simplex.vertex (⟨edgeW1Face v 0 k⟩ : QbarCell))
    (⟨edgeFace v 0 k⟩ : QbarCell)
    (fun _ => QbarCW.facet_lt (by
      rw [facets_edgeFace v k hk]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- The lower characteristic simplex of the edge, in the subdivision of `Q̄`. -/
def eFlag0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Mbar.flagAct (esig v k) (eNice0 v k hk)

/-- The upper characteristic simplex of the edge, in the subdivision of `Q̄`. -/
def eFlag1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Work.Subdivision.Simplex QbarCW.Cell 1 :=
  Mbar.flagAct (esig v k) (eNice1 v k hk)

/-- The characteristic simplex of the lower half of the `k`-th unit edge, in `mbarSd`. -/
def eSimp0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Fin (mbarCard 1) :=
  Mbar.rootSimplex 1 (by norm_num) (edgeCell v 0 k) (eFlag0 v k hk)

/-- The characteristic simplex of the upper half of the `k`-th unit edge, in `mbarSd`. -/
def eSimp1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Fin (mbarCard 1) :=
  Mbar.rootSimplex 1 (by norm_num) (edgeCell v 0 k) (eFlag1 v k hk)

/-- The image of the lower characteristic simplex in `C_1(M̄)`. -/
def eChi0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (singCxFun.obj cMtop).X 1 := singGen (Mbar.chi 1 (eSimp0 v k hk))

/-- The image of the upper characteristic simplex in `C_1(M̄)`. -/
def eChi1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (singCxFun.obj cMtop).X 1 := singGen (Mbar.chi 1 (eSimp1 v k hk))

/-! ## §2b  The top face of the characteristic simplex -/

theorem topIdx_eNice0_aux : ∀ (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0),
    Mbar.topIdx (eNice0 v k hk) = edgeFace v 0 k := by
  intro v k hk
  show (eNice0 v k hk (Fin.last 1)).idx = edgeFace v 0 k
  rw [show (eNice0 v k hk) (Fin.last 1) = (⟨edgeFace v 0 k⟩ : QbarCell) from
    Work.Subdivision.Simplex.snoc_apply_last _ _ _]

theorem topIdx_eNice1_aux : ∀ (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0),
    Mbar.topIdx (eNice1 v k hk) = edgeFace v 0 k := by
  intro v k hk
  show (eNice1 v k hk (Fin.last 1)).idx = edgeFace v 0 k
  rw [show (eNice1 v k hk) (Fin.last 1) = (⟨edgeFace v 0 k⟩ : QbarCell) from
    Work.Subdivision.Simplex.snoc_apply_last _ _ _]

/-! ## §3  The table facts -/

/-- The root face of the cell of the `k`-th unit edge is the image of the ridge under the sign
change. -/
theorem eRootI_eq_faceAct_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 0 →
    faceAct (esig v k) (edgeFace v 0 k) = eRootI v k := by
  decide

theorem eRootI_eq_faceAct (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    faceAct (esig v k) (edgeFace v 0 k) = eRootI v k :=
  eRootI_eq_faceAct_aux v k hk

/-- The node `(ebit v k, edgeFace v 0 k)` is the root node of the cell `edgeCell v 0 k`. -/
theorem moCell_ebit_edgeFace_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 0 →
    Mbar.moCell (ebit v k) (edgeFace v 0 k) = Mbar.moCid 1 (edgeCell v 0 k) := by
  decide

theorem moCell_ebit_edgeFace (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    Mbar.moCell (ebit v k) (edgeFace v 0 k) = Mbar.moCid 1 (edgeCell v 0 k) :=
  moCell_ebit_edgeFace_aux v k hk

/-- The two facets of the root face are `eU0` and `eU1`. -/
theorem facets_eRoot_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 0 →
    QbarCW.facets (eRoot v k) = {eU0 v k, eU1 v k} := by
  decide

theorem facets_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    QbarCW.facets (eRoot v k) = {eU0 v k, eU1 v k} :=
  facets_eRoot_aux v k hk

theorem eU0_lt_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eU0 v k < eRoot v k :=
  QbarCW.facet_lt (by rw [facets_eRoot v k hk]; exact Finset.mem_insert_self _ _)

theorem eU1_lt_eRoot (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eU1 v k < eRoot v k :=
  QbarCW.facet_lt (by rw [facets_eRoot v k hk]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The two facets of the root face are distinct. -/
theorem eU0_ne_eU1_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 0 →
    eU0 v k ≠ eU1 v k := by
  decide

theorem eU0_ne_eU1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eU0 v k ≠ eU1 v k := eU0_ne_eU1_aux v k hk

/-- The two incidences at the root face are opposite. -/
theorem qInc_eU1_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 0 →
    qInc (eRootI v k) (eU1 v k).idx = -qInc (eRootI v k) (eU0 v k).idx := by
  decide

theorem qInc_eU1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    qInc (eRootI v k) (eU1 v k).idx = -qInc (eRootI v k) (eU0 v k).idx :=
  qInc_eU1_aux v k hk

/-- The coefficient times the fibre-loop sign is the constant sign of the case. -/
theorem eBeta_edgeSign_aux : ∀ (v : Fin 5) (k : Fin 4), (k : ℕ) < fibreLen v 0 →
    eBeta v k * edgeSign v 0 k = (if (v : ℕ) = 0 ∨ (v : ℕ) = 2 then (1 : ℤ) else -1) := by
  decide

theorem eBeta_edgeSign (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eBeta v k * edgeSign v 0 k = (if (v : ℕ) = 0 ∨ (v : ℕ) = 2 then (1 : ℤ) else -1) :=
  eBeta_edgeSign_aux v k hk

/-- The sign vanishes on the dummy edges. -/
theorem edgeSign_zero_aux : ∀ (v : Fin 5) (k : Fin 4), ¬ (k : ℕ) < fibreLen v 0 →
    edgeSign v 0 k = 0 := by
  decide

theorem edgeSign_zero (v : Fin 5) (k : Fin 4) (hk : ¬ (k : ℕ) < fibreLen v 0) :
    edgeSign v 0 k = 0 :=
  edgeSign_zero_aux v k hk

end

end Work.BridgeSquare
