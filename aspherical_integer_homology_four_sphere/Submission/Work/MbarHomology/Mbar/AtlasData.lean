/-
# The combinatorial data of the cell atlas of `M̄`

**Work package W7** of `Submission/Work/NOTES_LEAD_eA.md`: the definitions read off the generated
tables `Submission/Work/MbarHomology/Data/MbarOrbits.lean`, and their elementary properties.

* `sigVec c F` — the sign vector of the node `(c, F)`, decoded from `moSig`;
* `Enode c F` — the group element `(sigVec c F, c + moRootC (moCell c F))` of `Gg` taking the node
  `(c, F)` to the root of its cell (`Enode_act`);
* `toRoot c F` — the root node of the cell of `(c, F)`;
* `nodeAct γ x` — the action of `Gg` on nodes (face action plus copy flip).

The finite checks on the tables are `node_facts` (a conjunction over the `1730` nodes),
`moCid_spec`, `moRoot_dim` and `moDim_moCell`; the geometric lemmas on the sign-change action
(`posR_faceAct_q`, `bary_flagAct`) are proved from `qAct_spec_pos`, the additivity of the linear
action, and the injectivity of `posR` on the faces of `Q̄`.
-/
import Mathlib
import Submission.Work.MbarHomology.Data.MbarOrbits
import Submission.Work.MbarHomology.Mbar.FaceActIso
import Submission.Work.MbarHomology.Qbar.qAct_spec
import Submission.Work.MbarHomology.Mbar.Flags
import Submission.Work.MbarHomology.Mbar.Sd
import Submission.Work.MbarHomology.ConvexCells.sd_realization_of_basic

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

/-! ## 1. The sign-change action on the faces and flags of `Q̄` -/

/-- `signVecT` is `Work.FoldInst.signVec` under the encoding `enc`. -/
theorem signVecT_enc_q (g : Fin 4 → ZMod 2) :
    signVecT (Work.FoldInst.enc g) = Work.FoldInst.signVec g := by decide +revert

/-- The `pos` point of a face is moved by the sign change. -/
theorem posR_faceAct_q (g : Fin 4 → ZMod 2) (f : Fin 865) :
    QbarPD.posR (faceAct g f) = Work.FoldInst.act g (QbarPD.posR f) := by
  have hpos : qPos (faceAct g f) = fun i => Work.FoldInst.signVec g i * qPos f i := by
    rw [faceAct, Work.MbarHomology.Qbar.qAct_spec_pos (Work.FoldInst.enc g) f, signVecT_enc_q]
  have h2 : Work.ConvexCells.toE (fun i => Work.FoldInst.signVec g i * qPos f i)
      = Work.FoldInst.act g (Work.ConvexCells.toE (qPos f)) := by
    apply PiLp.ext
    intro i
    rw [Work.FoldInst.act_apply_apply, Work.ConvexCells.toE_apply, Work.ConvexCells.toE_apply]
    push_cast
    ring
  have hsm : Work.FoldInst.act g (((1920 : ℝ))⁻¹ • Work.ConvexCells.toE (qPos f))
      = ((1920 : ℝ))⁻¹ • Work.FoldInst.act g (Work.ConvexCells.toE (qPos f)) := by
    apply PiLp.ext
    intro i
    simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  show ((1920 : ℝ))⁻¹ • Work.ConvexCells.toE (qPos (faceAct g f))
      = Work.FoldInst.act g (((1920 : ℝ))⁻¹ • Work.ConvexCells.toE (qPos f))
  rw [hpos, h2, hsm]

/-- A constraint is tight at a face iff it is an equality at the `pos` point of the face. -/
theorem mem_qTight_iff_inner (f : Fin 865) (i : Fin 48) :
    i ∈ qTight f ↔ inner ℝ (QbarPD.nR i) (QbarPD.posR f) = QbarPD.bR i :=
  (inner_posR_eq_iff_basic QbarPD_okBasic f i).symm

/-- `posR` is injective on the faces of `Q̄`. -/
theorem posR_inj {f f' : Fin 865} (h : QbarPD.posR f = QbarPD.posR f') : f = f' := by
  have hT : qTight f = qTight f' := by
    ext i
    rw [mem_qTight_iff_inner f i, h, mem_qTight_iff_inner f' i]
  exact qTight_inj hT

/-- The action of the sign changes on the faces is additive. -/
theorem faceAct_add (g h : Fin 4 → ZMod 2) (f : Fin 865) :
    faceAct (g + h) f = faceAct g (faceAct h f) := by
  apply posR_inj
  rw [posR_faceAct_q, posR_faceAct_q, posR_faceAct_q, Work.FoldInst.act_add]

theorem faceAct_zero (f : Fin 865) : faceAct 0 f = f := by
  apply posR_inj
  rw [posR_faceAct_q]
  show Work.FoldInst.act 0 (QbarPD.posR f) = QbarPD.posR f
  rw [Work.FoldInst.act_zero]

theorem faceAct_invol (g : Fin 4 → ZMod 2) (f : Fin 865) : faceAct g (faceAct g f) = f := by
  rw [← faceAct_add]
  have : g + g = 0 := funext fun i => Work.FoldInst.ZMod2_add_self (g i)
  rw [this, faceAct_zero]

theorem faceAct_inj (g : Fin 4 → ZMod 2) : Function.Injective (faceAct g) := fun a b h =>
  by rw [← faceAct_invol g a, h, faceAct_invol g b]

/-- `Work.FoldInst.act` is `ℝ`-homogeneous. -/
theorem act_smul_q (g : Fin 4 → ZMod 2) (c : ℝ) (y : Work.FoldInst.E4) :
    Work.FoldInst.act g (c • y) = c • Work.FoldInst.act g y := by
  apply PiLp.ext
  intro i
  simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `Work.FoldInst.act` commutes with linear combinations. -/
theorem act_sum_q (g : Fin 4 → ZMod 2) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (z : ι → Work.FoldInst.E4) :
    Work.FoldInst.act g (∑ i ∈ s, c i • z i) = ∑ i ∈ s, c i • Work.FoldInst.act g (z i) := by
  apply PiLp.ext
  intro k
  simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The sign change acting on a flag of `Q̄`. -/
def flagAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) : Simplex QbarCW.Cell k where
  toFun i := faceActCell g (s i)
  strictMono := fun _ _ hij => faceActCell_lt (s.strictMono hij)

@[simp] theorem flagAct_apply (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k)
    (i : Fin (k + 1)) : flagAct g s i = faceActCell g (s i) := rfl

@[simp] theorem flagAct_idx (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k)
    (i : Fin (k + 1)) : (flagAct g s i).idx = faceAct g (s i).idx := rfl

theorem flagAct_add (g h : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    flagAct (g + h) s = flagAct g (flagAct h s) := by
  apply Simplex.ext
  intro i
  simp only [flagAct_apply]
  exact QbarCell.ext (faceAct_add g h (s i).idx)

/-- The action on flags commutes with dropping a vertex. -/
theorem flagAct_face (g : Fin 4 → ZMod 2) {k : ℕ} (i : Fin (k + 2))
    (s : Simplex QbarCW.Cell (k + 1)) :
    Simplex.face i (flagAct g s) = flagAct g (Simplex.face i s) := by
  ext j; rfl

/-- The barycentre of a flag is moved by the sign change. -/
theorem bary_flagAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    bary (flagAct g s) = Work.FoldInst.act g (bary s) := by
  have h1 : ∀ i, QbarPD.posR (faceAct g (s i).idx)
      = Work.FoldInst.act g (QbarPD.posR (s i).idx) := fun i => posR_faceAct_q g (s i).idx
  show (∑ i, ((k + 1 : ℝ))⁻¹ • QbarPD.posR (faceAct g (s i).idx))
      = Work.FoldInst.act g (∑ i, ((k + 1 : ℝ))⁻¹ • QbarPD.posR (s i).idx)
  rw [show (∑ i, ((k + 1 : ℝ))⁻¹ • QbarPD.posR (faceAct g (s i).idx))
      = ∑ i, ((k + 1 : ℝ))⁻¹ • Work.FoldInst.act g (QbarPD.posR (s i).idx) from
    Finset.sum_congr rfl fun i _ => by rw [h1 i]]
  rw [act_sum_q]

/-! ## 2. The node data -/

/-- The sign vector of the node `(c, F)`, decoded from the generated code `moSig`. -/
def sigVec (c : ZMod 2) (F : Fin 865) : Fin 4 → ZMod 2 :=
  fun i => if (moSig c F).val / 2 ^ i.val % 2 = 0 then 0 else 1

/-- The group element taking the node `(c, F)` to the root of its cell. -/
def Enode (c : ZMod 2) (F : Fin 865) : Work.FoldInst.Gg :=
  (sigVec c F, c + moRootC (moCell c F))

/-- The root node of the cell of `(c, F)`. -/
def toRoot (c : ZMod 2) (F : Fin 865) : ZMod 2 × Fin 865 :=
  (moRootC (moCell c F), moRoot (moCell c F))

/-- The action of a group element on a node. -/
def nodeAct (γ : Work.FoldInst.Gg) (x : ZMod 2 × Fin 865) : ZMod 2 × Fin 865 :=
  (x.1 + γ.2, faceAct γ.1 x.2)

@[simp] theorem nodeAct_fst (γ : Work.FoldInst.Gg) (x : ZMod 2 × Fin 865) :
    (nodeAct γ x).1 = x.1 + γ.2 := rfl

@[simp] theorem nodeAct_snd (γ : Work.FoldInst.Gg) (x : ZMod 2 × Fin 865) :
    (nodeAct γ x).2 = faceAct γ.1 x.2 := rfl

theorem nodeAct_add (γ η : Work.FoldInst.Gg) (x : ZMod 2 × Fin 865) :
    nodeAct (γ + η) x = nodeAct γ (nodeAct η x) := by
  refine Prod.ext ?_ ?_
  · show x.1 + (γ + η).2 = x.1 + η.2 + γ.2
    rw [show (γ + η).2 = (γ.2 + η.2) from rfl, add_assoc, add_comm γ.2 η.2]
  · show faceAct (γ + η).1 x.2 = faceAct γ.1 (faceAct η.1 x.2)
    rw [show (γ + η).1 = (γ.1 + η.1) from rfl]
    exact faceAct_add γ.1 η.1 x.2

theorem nodeAct_zero (x : ZMod 2 × Fin 865) : nodeAct 0 x = x := by
  refine Prod.ext ?_ ?_
  · show x.1 + (0 : Work.FoldInst.Gg).2 = x.1
    simp
  · show faceAct (0 : Work.FoldInst.Gg).1 x.2 = x.2
    simp [faceAct_zero]

end

end Work.MbarHomology.Mbar
