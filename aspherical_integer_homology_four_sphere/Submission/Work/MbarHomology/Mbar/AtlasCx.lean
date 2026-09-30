/-
# The cell atlas of the barycentric subdivision of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the atlas itself.

* `cellOf i` is the pair `(dimension, position)` of a cell of `M̄`;
* `carQ x` is the cell of a flag `x` (the cell of its top face), `liftQ x` is the canonical
  representative of the orbit of `x` (the flag carried to the root face by `Enode`);
* `car`, `lift` are their descent to the orbits, i.e. to the simplices of `mbarSd`;
* `rootCx n e` is the root face of the `e`-th cell of dimension `n`.

The cocycle identity `Enode_cocycle` shows that `carQ` and `liftQ` only depend on the orbit
(`rel_car_lift`), so that `car` and `lift` are well defined; `liftCx_bij` shows that `lift` is a
bijection from the simplices with a given carrier onto the flags over the root face, with explicit
inverse `s ↦ [root n e, s]`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.Assemble
import Submission.Work.MbarHomology.Mbar.bary_inj
import Submission.Work.MbarHomology.Mbar.AtlasCocycle
import Submission.Work.MbarHomology.CellAtlas.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells
open scoped BigOperators

noncomputable section

/-! ## 0. The finite table facts -/

/-- The root node of a cell is a node of that cell. -/
theorem moCell_root (i : Fin 482) : moCell (moRootC i) (moRoot i) = i := by decide +revert

/-- The enumeration `moCid` is a section of the pair (dimension, position). -/
theorem moCid_moCell (i : Fin 482) :
    moCid ⟨moDim i, mbarDim_lt_fin i⟩ ⟨moPos i, moPos_lt i⟩ = i := by decide +revert

/-! ## 1. The cell of a flag and the canonical lift -/

/-- A cell of `M̄` as a pair `(dimension, position)`. -/
def cellOf (i : Fin 482) : Σ n : ℕ, Fin (Work.HomologyIso.Gen.mbarDim n) :=
  ⟨moDim i, ⟨moPos i, moPos_lt i⟩⟩

/-- The `(dimension, position)` pair read back as a cell of `M̄` (junk outside the image). -/
def cellPairIdx (x : Σ n : ℕ, Fin (Work.HomologyIso.Gen.mbarDim n)) : Fin 482 :=
  if h : x.1 < 5 then moCid ⟨x.1, h⟩ x.2 else 0

theorem cellPairIdx_cellOf (i : Fin 482) : cellPairIdx (cellOf i) = i := by
  unfold cellPairIdx cellOf
  rw [dif_pos (mbarDim_lt_fin i)]
  exact moCid_moCell i

theorem cellOf_inj {i j : Fin 482} (h : cellOf i = cellOf j) : i = j := by
  rw [← cellPairIdx_cellOf i, ← cellPairIdx_cellOf j, h]

/-- The cell of the `e`-th cell of dimension `n` is `(n,e)`. -/
theorem cellOf_moCid (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    cellOf (moCid n e) = ⟨(n : ℕ), e⟩ := by decide +revert

/-- The carrier of a flag: the cell of its top face. -/
def carQ {k : ℕ} (x : FlagQ k) : Σ n : ℕ, Fin (Work.HomologyIso.Gen.mbarDim n) :=
  cellOf (moCell x.1 (topIdx x.2))

/-- The canonical lift of a flag: the sign-changed representative ending at the root face. -/
def liftQ {k : ℕ} (x : FlagQ k) : Simplex QbarCW.Cell k :=
  flagAct (sigVec x.1 (topIdx x.2)) x.2

theorem carQ_def {k : ℕ} (x : FlagQ k) :
    carQ x = cellOf (moCell x.1 (topIdx x.2)) := rfl

theorem liftQ_def {k : ℕ} (x : FlagQ k) :
    liftQ x = flagAct (sigVec x.1 (topIdx x.2)) x.2 := rfl

theorem carQ_congr {k : ℕ} {x y : FlagQ k} (h : moCell x.1 (topIdx x.2) = moCell y.1 (topIdx y.2)) :
    carQ x = carQ y := by
  rw [carQ_def, carQ_def, h]

/-- The sign change acts trivially through `0`. -/
theorem flagAct_zero {k : ℕ} (s : Simplex QbarCW.Cell k) : flagAct 0 s = s := by
  apply Simplex.ext
  intro i
  simp only [flagAct_apply]
  exact QbarCell.ext (faceAct_zero (s i).idx)

/-- The sign vector of a root node vanishes. -/
theorem sigVec_root (n : Fin 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    sigVec (moRootC (moCid n e)) (moRoot (moCid n e)) = 0 := by
  have h1 : (toRoot (moRootC (moCid n e)) (moRoot (moCid n e))).1 = moRootC (moCid n e) := by
    unfold toRoot
    rw [moCell_root]
  have h2 : (toRoot (moRootC (moCid n e)) (moRoot (moCid n e))).2 = moRoot (moCid n e) := by
    unfold toRoot
    rw [moCell_root]
  have h := sigVec_toRoot (moRootC (moCid n e)) (moRoot (moCid n e))
  rwa [h1, h2] at h

/-- The sign vector of a node is additive on the first component. -/
theorem gg_fst_add_self (γ : Work.FoldInst.Gg) : γ.1 + γ.1 = 0 :=
  funext fun i => zmod2_add_self' (γ.1 i)

/-- The last vertex of a flag is unchanged by dropping a non-last vertex. -/
theorem face_apply_last {k : ℕ} (i : Fin (k + 1)) (s : Simplex QbarCW.Cell (k + 1)) :
    (Simplex.face i.castSucc s) (Fin.last k) = s (Fin.last (k + 1)) := by
  rw [Simplex.face_apply]
  congr 1
  unfold Fin.succAbove
  split
  · rename_i hlt
    exfalso
    simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hlt
    have h := i.isLt
    omega
  · rfl

/-- The last vertex of the last face of a flag. -/
theorem face_last_apply {k : ℕ} (s : Simplex QbarCW.Cell (k + 1)) :
    (Simplex.face (Fin.last (k + 1)) s) (Fin.last k) = s (Fin.last k).castSucc := by
  simp only [Simplex.face_apply, Fin.succAbove_last_apply]

/-! ## 2. The invariance of the carrier and of the lift -/

/-- The top face of the acted flag. -/
theorem topIdx_nodeAct {k : ℕ} (γ : Work.FoldInst.Gg) (x : FlagQ k) :
    topIdx (flagAct γ.1 x.2) = faceAct γ.1 (topIdx x.2) := by
  show ((flagAct γ.1 x.2) (Fin.last k)).idx = faceAct γ.1 (topIdx x.2)
  rw [flagAct_idx]
  rfl

/-- **The cocycle identity, in the form needed for the nodes of a flag.** -/
theorem Enode_cocycle_flag {γ : Work.FoldInst.Gg} {k : ℕ} {x : FlagQ k}
    (hγ : γ ∈ KsubAtlas (topIdx x.2)) :
    Enode (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)) = Enode x.1 (topIdx x.2) + γ := by
  have h := Enode_cocycle (F := topIdx x.2) hγ x.1
  simpa only [nodeAct_fst, nodeAct_snd] using h

/-- **The root node is invariant under the identification group.** -/
theorem toRoot_cocycle {γ : Work.FoldInst.Gg} {k : ℕ} (x : FlagQ k)
    (hγ : γ ∈ KsubAtlas (topIdx x.2)) :
    toRoot (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)) = toRoot x.1 (topIdx x.2) := by
  have hcoc := Enode_cocycle_flag hγ
  rw [← Enode_act (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)), hcoc]
  show nodeAct (Enode x.1 (topIdx x.2) + γ) (nodeAct γ (x.1, topIdx x.2)) = toRoot x.1 (topIdx x.2)
  rw [nodeAct_add]
  rw [show nodeAct γ (nodeAct γ (x.1, topIdx x.2)) = nodeAct (γ + γ) (x.1, topIdx x.2) from
    (nodeAct_add γ γ (x.1, topIdx x.2)).symm]
  rw [gg_add_self, nodeAct_zero]
  exact Enode_act x.1 (topIdx x.2)

/-- **The carrier is invariant under the identification group.** -/
theorem cell_act {γ : Work.FoldInst.Gg} {k : ℕ} (x : FlagQ k) (hγ : γ ∈ KsubAtlas (topIdx x.2)) :
    moCell (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)) = moCell x.1 (topIdx x.2) := by
  rw [← moCell_toRoot (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)), ← moCell_toRoot x.1 (topIdx x.2),
    toRoot_cocycle x hγ]

/-- **The lift is invariant under the identification group.** -/
theorem lift_act {γ : Work.FoldInst.Gg} {k : ℕ} (x : FlagQ k) (hγ : γ ∈ KsubAtlas (topIdx x.2)) :
    liftQ (x.1 + γ.2, flagAct γ.1 x.2) = liftQ x := by
  have hsig : sigVec (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)) = sigVec x.1 (topIdx x.2) + γ.1 :=
    congrArg Prod.fst (Enode_cocycle_flag hγ)
  show flagAct (sigVec (x.1 + γ.2) (topIdx (flagAct γ.1 x.2))) (flagAct γ.1 x.2)
      = flagAct (sigVec x.1 (topIdx x.2)) x.2
  rw [topIdx_nodeAct, hsig, flagAct_add]
  rw [show flagAct γ.1 (flagAct γ.1 x.2) = flagAct (γ.1 + γ.1) x.2 from
    (flagAct_add γ.1 γ.1 x.2).symm]
  rw [gg_fst_add_self, flagAct_zero]

/-- **The carrier and the lift only depend on the orbit of a flag.** -/
theorem rel_car_lift {k : ℕ} {x y : FlagQ k} (h : flagRel x y) :
    carQ x = carQ y ∧ liftQ x = liftQ y := by
  obtain ⟨γ, hγ, hy1, hy2⟩ := h
  have hmem : γ ∈ KsubAtlas (topIdx x.2) := by
    rw [show topIdx x.2 = (x.2 (Fin.last k)).idx from rfl, ← Ksub_bary_eq_KsubAtlas x.2]
    exact hγ
  have hy : y.2 = flagAct γ.1 x.2 := by
    refine bary_inj ?_
    rw [bary_flagAct, hy2]
  have hy' : y = (x.1 + γ.2, flagAct γ.1 x.2) := Prod.ext hy1 hy
  constructor
  · rw [hy']
    show carQ x = carQ (x.1 + γ.2, flagAct γ.1 x.2)
    rw [carQ_def, carQ_def]
    show cellOf (moCell x.1 (topIdx x.2))
        = cellOf (moCell (x.1 + γ.2) (faceAct γ.1 (topIdx x.2)))
    exact congrArg cellOf (cell_act x hmem).symm
  · rw [hy']
    exact (lift_act x hmem).symm

/-! ## 3. The descent to the orbits of flags -/

/-- The carrier of a flag, as a function of its orbit. -/
def carQq {k : ℕ} : Quotient (flagSetoid k) → Σ n : ℕ, Fin (Work.HomologyIso.Gen.mbarDim n) :=
  Quot.lift carQ fun _ _ h => (rel_car_lift h).1

/-- The canonical lift of a flag, as a function of its orbit. -/
def liftQq {k : ℕ} : Quotient (flagSetoid k) → Simplex QbarCW.Cell k :=
  Quot.lift liftQ fun _ _ h => (rel_car_lift h).2

@[simp] theorem carQq_mk {k : ℕ} (x : FlagQ k) : carQq (Quot.mk _ x) = carQ x := rfl

@[simp] theorem liftQq_mk {k : ℕ} (x : FlagQ k) : liftQq (Quot.mk _ x) = liftQ x := rfl

/-! ## 4. The root face of a cell -/

/-- The root face of the `e`-th cell of dimension `n`. -/
def rootCx (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) : QbarCW.Cell :=
  if h : n < 5 then ⟨moRoot (moCid ⟨n, h⟩ e)⟩ else ⟨0⟩

/-- The root copy bit of the `e`-th cell of dimension `n`. -/
def rootCopy (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) : ZMod 2 :=
  if h : n < 5 then moRootC (moCid ⟨n, h⟩ e) else 0

theorem rootCx_of_lt {n : ℕ} (h : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    rootCx n e = ⟨moRoot (moCid ⟨n, h⟩ e)⟩ := dif_pos h

theorem rootCopy_of_lt {n : ℕ} (h : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    rootCopy n e = moRootC (moCid ⟨n, h⟩ e) := dif_pos h

theorem rootCx_dim (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    QbarCW.dim (rootCx n e) = n := by
  by_cases h : n < 5
  · rw [rootCx_of_lt h]
    exact moRoot_dim ⟨n, h⟩ e
  · have h0 : Work.HomologyIso.Gen.mbarDim n = 0 :=
      Work.HomologyIso.Gen.mbarDim_eq_zero n (by omega)
    exact Fin.elim0 (h0 ▸ e)

/-- The root face of the cell of a node. -/
theorem rootCx_cellOf (i : Fin 482) :
    rootCx (moDim i) ⟨moPos i, moPos_lt i⟩ = ⟨moRoot i⟩ := by
  rw [rootCx_of_lt (mbarDim_lt_fin i), moCid_moCell i]

/-- The root copy bit of the cell of a node. -/
theorem rootCopy_cellOf (i : Fin 482) :
    rootCopy (moDim i) ⟨moPos i, moPos_lt i⟩ = moRootC i := by
  rw [rootCopy_of_lt (mbarDim_lt_fin i), moCid_moCell i]

/-- The top face of the root node of a cell. -/
theorem topIdx_rootNode (n : ℕ) (hn : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    {k : ℕ} (s : Simplex QbarCW.Cell k) (hs : s (Fin.last k) = rootCx n e) :
    topIdx s = moRoot (moCid ⟨n, hn⟩ e) := by
  have h1 : s (Fin.last k) = (⟨moRoot (moCid ⟨n, hn⟩ e)⟩ : QbarCell) := by
    rw [hs, rootCx_of_lt hn]
  exact congrArg QbarCell.idx h1

theorem carQ_rootNode (n : ℕ) (hn : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    {k : ℕ} (s : Simplex QbarCW.Cell k) (hs : s (Fin.last k) = rootCx n e) :
    carQ (moRootC (moCid ⟨n, hn⟩ e), s) = ⟨n, e⟩ := by
  show cellOf (moCell (moRootC (moCid ⟨n, hn⟩ e)) (topIdx s)) = ⟨n, e⟩
  rw [topIdx_rootNode n hn e s hs, moCell_root]
  exact cellOf_moCid ⟨n, hn⟩ e

theorem liftQ_rootNode (n : ℕ) (hn : n < 5) (e : Fin (Work.HomologyIso.Gen.mbarDim n))
    {k : ℕ} (s : Simplex QbarCW.Cell k) (hs : s (Fin.last k) = rootCx n e) :
    liftQ (moRootC (moCid ⟨n, hn⟩ e), s) = s := by
  show flagAct (sigVec (moRootC (moCid ⟨n, hn⟩ e)) (topIdx s)) s = s
  rw [topIdx_rootNode n hn e s hs, sigVec_root, flagAct_zero]

/-- The lift of a flag ends at the root face of its carrier. -/
theorem liftQ_last {k : ℕ} (x : FlagQ k) :
    liftQ x (Fin.last k) = rootCx (carQ x).1 (carQ x).2 := by
  show faceActCell (sigVec x.1 (topIdx x.2)) (x.2 (Fin.last k))
      = rootCx (moDim (moCell x.1 (topIdx x.2)))
          ⟨moPos (moCell x.1 (topIdx x.2)), moPos_lt _⟩
  rw [rootCx_cellOf]
  apply QbarCell.ext
  show faceAct (sigVec x.1 (topIdx x.2)) (topIdx x.2) = moRoot (moCell x.1 (topIdx x.2))
  have h := congrArg Prod.snd (Enode_act x.1 (topIdx x.2))
  simpa only [nodeAct_snd, Enode, toRoot] using h

/-- A flag whose carrier is a given cell is related to the root node of that cell. -/
theorem rel_rootFlag {k : ℕ} {x : FlagQ k} {n : ℕ} (hn : n < 5)
    {e : Fin (Work.HomologyIso.Gen.mbarDim n)} (hx : carQ x = ⟨n, e⟩) :
    flagRel x (moRootC (moCid ⟨n, hn⟩ e), liftQ x) := by
  have hcell : moCell x.1 (topIdx x.2) = moCid ⟨n, hn⟩ e := by
    apply cellOf_inj
    rw [carQ_def] at hx
    rw [hx]
    exact (cellOf_moCid ⟨n, hn⟩ e).symm
  refine ⟨Enode x.1 (topIdx x.2), ?_, ?_, ?_⟩
  · rw [Ksub_bary_eq_KsubAtlas x.2]
    exact Enode_mem_KsubAtlas _ _
  · show moRootC (moCid ⟨n, hn⟩ e) = x.1 + (x.1 + moRootC (moCell x.1 (topIdx x.2)))
    rw [hcell, ← add_assoc, zmod2_add_self', zero_add]
  · show bary (liftQ x) = Work.FoldInst.act (sigVec x.1 (topIdx x.2)) (bary x.2)
    rw [liftQ_def, bary_flagAct]

/-! ## 5. Dropping a vertex -/

theorem topIdx_face {k : ℕ} (x : FlagQ (k + 1)) (i : Fin (k + 1)) :
    topIdx (Simplex.face i.castSucc x.2) = topIdx x.2 := by
  show ((Simplex.face i.castSucc x.2) (Fin.last k)).idx = (x.2 (Fin.last (k + 1))).idx
  rw [face_apply_last]

theorem carQ_face {k : ℕ} (x : FlagQ (k + 1)) (i : Fin (k + 1)) :
    carQ (x.1, Simplex.face i.castSucc x.2) = carQ x := by
  show cellOf (moCell x.1 (topIdx (Simplex.face i.castSucc x.2))) = cellOf (moCell x.1 (topIdx x.2))
  rw [topIdx_face]

theorem liftQ_face {k : ℕ} (x : FlagQ (k + 1)) (i : Fin (k + 1)) :
    liftQ (x.1, Simplex.face i.castSucc x.2) = (liftQ x).face i.castSucc := by
  show flagAct (sigVec x.1 (topIdx (Simplex.face i.castSucc x.2))) (Simplex.face i.castSucc x.2)
      = Simplex.face i.castSucc (flagAct (sigVec x.1 (topIdx x.2)) x.2)
  rw [topIdx_face, flagAct_face]

/-- Dropping the last vertex strictly lowers the carrier dimension. -/
theorem dim_face_last {k : ℕ} (x : FlagQ (k + 1)) :
    (carQ (x.1, Simplex.face (Fin.last (k + 1)) x.2)).1 < (carQ x).1 := by
  show moDim (moCell x.1 ((Simplex.face (Fin.last (k + 1)) x.2) (Fin.last k)).idx)
      < moDim (moCell x.1 ((x.2 (Fin.last (k + 1))).idx))
  rw [face_last_apply, moDim_moCell, moDim_moCell]
  refine QbarCW.dim_lt (le_of_lt (x.2.strictMono (Fin.castSucc_lt_last (Fin.last k)))) ?_
  intro h
  have hlt : (⟨(x.2 (Fin.last k).castSucc).idx⟩ : QbarCW.Cell)
      < (⟨(x.2 (Fin.last (k + 1))).idx⟩ : QbarCW.Cell) :=
    x.2.strictMono (Fin.castSucc_lt_last (Fin.last k))
  rw [h] at hlt
  exact absurd hlt (lt_irrefl _)

/-! ## 6. The atlas -/

/-- The carrier of a simplex of `mbarSd`. -/
def carCx {k : ℕ} (σ : Fin (mbarSd.card k)) : Σ n : ℕ, Fin (Work.HomologyIso.Gen.mbarDim n) :=
  carQq (mbarEquiv k σ)

/-- The canonical lift of a simplex of `mbarSd`. -/
def liftCx {k : ℕ} (σ : Fin (mbarSd.card k)) : Simplex QbarCW.Cell k :=
  liftQq (mbarEquiv k σ)

theorem carCx_def {k : ℕ} (σ : Fin (mbarSd.card k)) : carCx σ = carQq (mbarEquiv k σ) := rfl

theorem liftCx_def {k : ℕ} (σ : Fin (mbarSd.card k)) : liftCx σ = liftQq (mbarEquiv k σ) := rfl

/-- The canonical simplex of `mbarSd` over the root face of the `e`-th cell of dimension `n`,
attached to a flag `s` of the subdivision of that root face. -/
noncomputable def rootSimplex {k : ℕ} (n : ℕ) (hn : n < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim n)) (s : Simplex QbarCW.Cell k) :
    Fin (mbarSd.card k) :=
  (mbarEquiv k).symm (Quotient.mk (flagSetoid k) (moRootC (moCid ⟨n, hn⟩ e), s))

theorem carCx_rootSimplex {k : ℕ} (n : ℕ) (hn : n < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim n)) (s : Simplex QbarCW.Cell k)
    (hs : s (Fin.last k) = rootCx n e) :
    carCx (rootSimplex n hn e s) = ⟨n, e⟩ := by
  show carQq ((mbarEquiv k) ((mbarEquiv k).symm
    (Quotient.mk (flagSetoid k) (moRootC (moCid ⟨n, hn⟩ e), s)))) = ⟨n, e⟩
  rw [Equiv.apply_symm_apply]
  show carQ (moRootC (moCid ⟨n, hn⟩ e), s) = ⟨n, e⟩
  exact carQ_rootNode n hn e s hs

theorem liftCx_rootSimplex {k : ℕ} (n : ℕ) (hn : n < 5)
    (e : Fin (Work.HomologyIso.Gen.mbarDim n)) (s : Simplex QbarCW.Cell k)
    (hs : s (Fin.last k) = rootCx n e) :
    liftCx (rootSimplex n hn e s) = s := by
  show liftQq ((mbarEquiv k) ((mbarEquiv k).symm
    (Quotient.mk (flagSetoid k) (moRootC (moCid ⟨n, hn⟩ e), s)))) = s
  rw [Equiv.apply_symm_apply]
  show liftQ (moRootC (moCid ⟨n, hn⟩ e), s) = s
  exact liftQ_rootNode n hn e s hs


/-- The face maps of `mbarSd` on the orbits. -/
theorem mbarSd_face_eq {k : ℕ} (σ : Fin (mbarSd.card (k + 1))) (i : Fin (k + 2)) :
    mbarSd.face σ i = (mbarEquiv k).symm (mbarFaceQ flagRel_face i (mbarEquiv (k + 1) σ)) := rfl

/-- The lift of a simplex ends at the root face of its carrier. -/
theorem liftCx_top {k : ℕ} (σ : Fin (mbarSd.card k)) :
    liftCx σ (Fin.last k) = rootCx (carCx σ).1 (carCx σ).2 := by
  obtain ⟨x, hx⟩ := (mbarEquiv k σ).exists_rep
  have hx' : Quot.mk (flagSetoid k) x = mbarEquiv k σ := hx
  show liftQq (mbarEquiv k σ) (Fin.last k) = rootCx (carQq (mbarEquiv k σ)).1 (carQq (mbarEquiv k σ)).2
  rw [← hx']
  exact liftQ_last x

/-- Dropping a vertex other than the last keeps the carrier and commutes with the lift. -/
theorem face_ne_last_cx {k : ℕ} (σ : Fin (mbarSd.card (k + 1))) (i : Fin (k + 1)) :
    carCx (mbarSd.face σ i.castSucc) = carCx σ ∧
      liftCx (mbarSd.face σ i.castSucc) = (liftCx σ).face i.castSucc := by
  obtain ⟨x, hx⟩ := (mbarEquiv (k + 1) σ).exists_rep
  have hx' : Quot.mk (flagSetoid (k + 1)) x = mbarEquiv (k + 1) σ := hx
  have hface : (mbarEquiv k) (mbarSd.face σ i.castSucc)
      = Quot.mk (flagSetoid k) (x.1, Simplex.face i.castSucc x.2) := by
    rw [mbarSd_face_eq, Equiv.apply_symm_apply, ← hx', mbarFaceQ_mk]
  constructor
  · rw [carCx_def, hface, carQq_mk, carCx_def, ← hx', carQq_mk]
    exact carQ_face x i
  · rw [liftCx_def, hface, liftQq_mk, liftCx_def, ← hx', liftQq_mk]
    exact liftQ_face x i

/-- Dropping the last vertex strictly lowers the carrier dimension. -/
theorem face_last_cx {k : ℕ} (σ : Fin (mbarSd.card (k + 1))) :
    (carCx (mbarSd.face σ (Fin.last (k + 1)))).1 < (carCx σ).1 := by
  obtain ⟨x, hx⟩ := (mbarEquiv (k + 1) σ).exists_rep
  have hx' : Quot.mk (flagSetoid (k + 1)) x = mbarEquiv (k + 1) σ := hx
  have hface : (mbarEquiv k) (mbarSd.face σ (Fin.last (k + 1)))
      = Quot.mk (flagSetoid k) (x.1, Simplex.face (Fin.last (k + 1)) x.2) := by
    rw [mbarSd_face_eq, Equiv.apply_symm_apply, ← hx', mbarFaceQ_mk]
  rw [carCx_def, hface, carQq_mk, carCx_def, ← hx', carQq_mk]
  exact dim_face_last x

/-- The lift is a bijection from the simplices with a given carrier onto the flags over the root
face of that carrier. -/
theorem liftCx_bij (k : ℕ) (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim n)) :
    Function.Bijective (fun σ : {σ : Fin (mbarSd.card k) // carCx σ = ⟨n, e⟩} =>
      (⟨liftCx σ.1, by rw [liftCx_top σ.1, σ.2]⟩ :
        {s : Simplex QbarCW.Cell k // s (Fin.last k) = rootCx n e})) := by
  by_cases hn : n < 5
  · refine ⟨fun a b hab => ?_, fun b => ?_⟩
    · -- injectivity
      obtain ⟨xa, hxa⟩ := (mbarEquiv k a.1).exists_rep
      obtain ⟨xb, hxb⟩ := (mbarEquiv k b.1).exists_rep
      have hxa' : Quot.mk (flagSetoid k) xa = mbarEquiv k a.1 := hxa
      have hxb' : Quot.mk (flagSetoid k) xb = mbarEquiv k b.1 := hxb
      have hca : carQ xa = ⟨n, e⟩ := by
        have h := a.2
        rw [carCx_def, ← hxa', carQq_mk] at h
        exact h
      have hcb : carQ xb = ⟨n, e⟩ := by
        have h := b.2
        rw [carCx_def, ← hxb', carQq_mk] at h
        exact h
      have hlift : liftQ xa = liftQ xb := by
        have h : liftCx a.1 = liftCx b.1 := congrArg Subtype.val hab
        rw [liftCx_def, ← hxa', liftQq_mk, liftCx_def, ← hxb', liftQq_mk] at h
        exact h
      have h1 := rel_rootFlag hn hca
      have h2 := rel_rootFlag hn hcb
      rw [hlift] at h1
      have hrel : flagRel xa xb := flagRel_trans h1 (flagRel_symm h2)
      apply Subtype.ext
      apply (mbarEquiv k).injective
      rw [← hxa', ← hxb']
      exact Quot.sound hrel
    · -- surjectivity
      exact ⟨⟨rootSimplex n hn e b.1, carCx_rootSimplex n hn e b.1 b.2⟩,
        Subtype.ext (liftCx_rootSimplex n hn e b.1 b.2)⟩
  · -- `n ≥ 5`: the type of cells is empty
    have h0 : Work.HomologyIso.Gen.mbarDim n = 0 :=
      Work.HomologyIso.Gen.mbarDim_eq_zero n (by omega)
    exact ⟨fun a b _ => Fin.elim0 (h0 ▸ e), fun b => ⟨Fin.elim0 (h0 ▸ e), Fin.elim0 (h0 ▸ e)⟩⟩

/-- **The cell atlas of `mbarSd`.** -/
noncomputable def mbarAtlasOf :
    CellAtlas mbarSd QbarCW Work.HomologyIso.Gen.mbarCx where
  root := rootCx
  dim_root := fun n e => rootCx_dim n e
  car := fun {k} σ => carCx σ
  lift := fun {k} σ => liftCx σ
  lift_top := fun {k} σ => liftCx_top σ
  lift_bij := fun k n e => liftCx_bij k n e
  face_ne_last := fun {k} σ i => face_ne_last_cx σ i
  face_last := fun {k} σ => face_last_cx σ

end

end Work.MbarHomology.Mbar
