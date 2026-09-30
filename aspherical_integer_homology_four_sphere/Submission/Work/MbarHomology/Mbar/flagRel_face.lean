import Mathlib
import Submission.Work.MbarHomology.Mbar.Flags
import Submission.Work.MbarHomology.Qbar.Act
import Submission.Work.MbarHomology.ConvexCells.sd_carrier_of_basic
import Submission.Work.MbarHomology.ConvexCells.sd_realization_of_basic
import Submission.Work.MbarHomology.Mbar.bary_inj
import Submission.Work.MbarHomology.Mbar.Ksub_bary_face
import Submission.Work.MbarHomology.QbarPos.g7

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
open Work.MbarHomology.ConvexCells
open scoped BigOperators

noncomputable section

/-! ## 1. The finite data: sign vectors and the constraint permutation

`Work.MbarHomology.Qbar.qAct_spec` bundles the four finite identities relating the sign-change
action on the faces of `Q̄` to the tables.  They are computations over `16 × 865` faces; the `pos`
and `tight` components are checked in the modules `Submission.Work.MbarHomology.QbarPos.*` and in
`Submission.Work.MbarHomology.Qbar.QbarPD_carriers`, and the remaining small tables are handled
here. -/

/-- `signVecT` is `Work.FoldInst.signVec` under the encoding `Work.FoldInst.enc`. -/
private theorem signVecT_enc (g : Fin 4 → ZMod 2) :
    signVecT (Work.FoldInst.enc g) = Work.FoldInst.signVec g := by
  decide +revert

/-- The induced permutation of the `48` constraints of `QbarPD` is injective. -/
private theorem consActT_injective : ∀ e : Fin 16, Function.Injective (consActT e) := by
  decide +revert

/-- The induced permutation of the `48` constraints of `QbarPD` is an involution. -/
private theorem consActT_invol : ∀ e : Fin 16, ∀ i : Fin 48, consActT e (consActT e i) = i := by
  decide +revert

private theorem consAct_injective (g : Fin 4 → ZMod 2) : Function.Injective (consAct g) :=
  consActT_injective (Work.FoldInst.enc g)

private theorem consAct_invol (g : Fin 4 → ZMod 2) (i : Fin 48) :
    consAct g (consAct g i) = i :=
  consActT_invol (Work.FoldInst.enc g) i

/-- The constraint permutation maps the side constraints by `Work.FoldInst.sidePerm`. -/
private theorem consAct_castAdd (g : Fin 4 → ZMod 2) (S : Fin 24) :
    consAct g (Fin.castAdd 24 S) = Fin.castAdd 24 (Work.FoldInst.sidePerm g S) := by
  decide +revert

/-- The constraint permutation maps the truncation constraints by `Work.FoldInst.truncPerm`. -/
private theorem consAct_natAdd (g : Fin 4 → ZMod 2) (w : Fin 24) :
    consAct g (Fin.natAdd 24 w) = Fin.natAdd 24 (Work.FoldInst.truncPerm g w) := by
  decide +revert

/-! ## 2. The `pos` points are equivariant -/

/-- The `pos` point of a sign-changed face is the sign-changed `pos` point, coordinatewise. -/
private theorem qPos_faceActT (e : Fin 16) (f : Fin 865) (i : Fin 4) :
    qPos (faceActT e f) i = signVecT e i * qPos f i := by
  fin_cases e
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_0 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_1 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_2 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_3 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_4 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_5 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_6 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_7 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_8 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_9 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_10 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_11 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_12 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_13 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_14 f i
  · exact Work.MbarHomology.QbarPos.qPos_faceActT_15 f i

/-- `Work.FoldInst.act` is additive. -/
private theorem act_add (g : Fin 4 → ZMod 2) (x y : Work.FoldInst.E4) :
    Work.FoldInst.act g (x + y) = Work.FoldInst.act g x + Work.FoldInst.act g y := by
  apply PiLp.ext
  intro i
  simp only [Work.FoldInst.act_apply_apply, PiLp.add_apply]
  ring

/-- `Work.FoldInst.act` is `ℝ`-homogeneous. -/
private theorem act_smul (g : Fin 4 → ZMod 2) (c : ℝ) (y : Work.FoldInst.E4) :
    Work.FoldInst.act g (c • y) = c • Work.FoldInst.act g y := by
  apply PiLp.ext
  intro i
  simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `Work.FoldInst.act` commutes with linear combinations. -/
private theorem act_sum (g : Fin 4 → ZMod 2) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (z : ι → Work.FoldInst.E4) :
    Work.FoldInst.act g (∑ i ∈ s, c i • z i) = ∑ i ∈ s, c i • Work.FoldInst.act g (z i) := by
  classical
  apply PiLp.ext
  intro k
  simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `Work.FoldInst.act g` is an isometry of the Euclidean space. -/
private theorem inner_act (g : Fin 4 → ZMod 2) (a b : E 4) :
    inner ℝ (Work.FoldInst.act g a) (Work.FoldInst.act g b) = inner ℝ a b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.FoldInst.act_apply_apply, Work.FoldInst.act_apply_apply]
  have h : (Work.FoldInst.signVec g i : ℝ) * (Work.FoldInst.signVec g i : ℝ) = 1 := by
    exact_mod_cast Work.FoldInst.signVec_sq g i
  rw [show (Work.FoldInst.signVec g i : ℝ) * b i * ((Work.FoldInst.signVec g i : ℝ) * a i)
      = ((Work.FoldInst.signVec g i : ℝ) * (Work.FoldInst.signVec g i : ℝ)) * (b i * a i)
      by ring,
    h, one_mul]

/-- `Work.FoldInst.act g` is an involution. -/
private theorem act_invol (g : Fin 4 → ZMod 2) (x : Work.FoldInst.E4) :
    Work.FoldInst.act g (Work.FoldInst.act g x) = x := by
  rw [Work.FoldInst.act_add,
    show (g + g : Fin 4 → ZMod 2) = 0 from funext fun k => Work.FoldInst.ZMod2_add_self (g k)]
  exact Work.FoldInst.act_zero x

/-- The sign change acts on the `pos` points of the faces by `Work.FoldInst.act`. -/
private theorem posR_faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) :
    QbarPD.posR (faceAct g f) = Work.FoldInst.act g (QbarPD.posR f) := by
  have hpos : qPos (faceActT (Work.FoldInst.enc g) f)
      = fun i => Work.FoldInst.signVec g i * qPos f i := by
    funext i
    rw [qPos_faceActT (Work.FoldInst.enc g) f i, signVecT_enc]
  have h2 : Work.ConvexCells.toE (fun i => Work.FoldInst.signVec g i * qPos f i)
      = Work.FoldInst.act g (Work.ConvexCells.toE (qPos f)) := by
    apply PiLp.ext
    intro i
    rw [Work.FoldInst.act_apply_apply, Work.ConvexCells.toE_apply, Work.ConvexCells.toE_apply]
    push_cast
    ring
  show ((1920 : ℝ))⁻¹ • Work.ConvexCells.toE (qPos (faceAct g f))
      = Work.FoldInst.act g (((1920 : ℝ))⁻¹ • Work.ConvexCells.toE (qPos f))
  rw [faceAct, hpos, h2, act_smul]

/-! ## 3. The tight sets are equivariant -/

/-- The real normal vector of a constraint is moved by the sign change according to the
constraint permutation. -/
private theorem act_nR (g : Fin 4 → ZMod 2) (i : Fin 48) :
    Work.FoldInst.act g (QbarPD.nR i) = QbarPD.nR (consAct g i) := by
  rcases lt_or_ge (i : ℕ) 24 with hi | hi
  · have hie : i = Fin.castAdd 24 (⟨(i : ℕ), hi⟩ : Fin 24) := Fin.ext rfl
    rw [hie, consAct_castAdd]
    simp only [PolytopeData.nR, QbarPD_nrm, QbarPD_D, qNrm_castAdd, Nat.cast_ofNat]
    rw [act_smul]
    congr 1
    apply PiLp.ext
    intro k
    rw [Work.FoldInst.act_apply_apply, Work.ConvexCells.toE_apply, Work.ConvexCells.toE_apply,
      Work.FoldInst.sideNormal_sidePerm]
    push_cast
    ring
  · have hie : i = Fin.natAdd 24 (⟨(i : ℕ) - 24, by omega⟩ : Fin 24) :=
      Fin.ext (by simp [Fin.natAdd]; omega)
    rw [hie, consAct_natAdd]
    simp only [PolytopeData.nR, QbarPD_nrm, QbarPD_D, qNrm_natAdd, Nat.cast_ofNat]
    rw [act_smul]
    congr 1
    apply PiLp.ext
    intro k
    rw [Work.FoldInst.act_apply_apply, Work.ConvexCells.toE_apply, Work.ConvexCells.toE_apply,
      Work.FoldInst.truncNormal2_truncPerm]
    push_cast
    ring

/-- The real right hand side of a constraint is invariant under the constraint permutation. -/
private theorem bR_consAct (g : Fin 4 → ZMod 2) (i : Fin 48) :
    QbarPD.bR (consAct g i) = QbarPD.bR i := by
  rcases lt_or_ge (i : ℕ) 24 with hi | hi
  · have hie : i = Fin.castAdd 24 (⟨(i : ℕ), hi⟩ : Fin 24) := Fin.ext rfl
    rw [hie, consAct_castAdd]
    simp only [PolytopeData.bR, QbarPD_rhs, QbarPD_D, qRhs_castAdd, Int.cast_one]
  · have hie : i = Fin.natAdd 24 (⟨(i : ℕ) - 24, by omega⟩ : Fin 24) :=
      Fin.ext (by simp [Fin.natAdd]; omega)
    rw [hie, consAct_natAdd]
    simp only [PolytopeData.bR, QbarPD_rhs, QbarPD_D, qRhs_natAdd]

/-- A constraint lies in the tight set of a face iff it is an equality at the `pos` point. -/
private theorem mem_qTight_iff (f : Fin 865) (i : Fin 48) :
    i ∈ qTight f ↔ inner ℝ (QbarPD.nR i) (QbarPD.posR f) = QbarPD.bR i :=
  (inner_posR_eq_iff_basic QbarPD_okBasic f i).symm

/-- A constraint is tight at a sign-changed face iff the permuted constraint is tight at the
original face. -/
private theorem mem_qTight_faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) (i : Fin 48) :
    i ∈ qTight (faceAct g f) ↔ consAct g i ∈ qTight f := by
  rw [mem_qTight_iff (faceAct g f) i, mem_qTight_iff f (consAct g i)]
  rw [posR_faceAct g f, bR_consAct g i, ← act_nR g i,
    show inner ℝ (QbarPD.nR i) (Work.FoldInst.act g (QbarPD.posR f))
        = inner ℝ (Work.FoldInst.act g (QbarPD.nR i)) (QbarPD.posR f) from by
      calc inner ℝ (QbarPD.nR i) (Work.FoldInst.act g (QbarPD.posR f))
          = inner ℝ (Work.FoldInst.act g (Work.FoldInst.act g (QbarPD.nR i)))
              (Work.FoldInst.act g (QbarPD.posR f)) := by rw [act_invol]
        _ = inner ℝ (Work.FoldInst.act g (QbarPD.nR i)) (QbarPD.posR f) :=
            inner_act g _ _]

/-- The tight set of a sign-changed face is the image of its tight set under the constraint
permutation. -/
private theorem tight_faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) :
    qTight (faceAct g f) = (qTight f).image (consAct g) := by
  ext i
  rw [mem_qTight_faceAct g f i, Finset.mem_image]
  exact ⟨fun h => ⟨consAct g i, h, consAct_invol g i⟩,
    fun ⟨j, hj, hji⟩ => by rw [← hji, consAct_invol]; exact hj⟩

/-! ## 4. The sign change acting on the flags of `Q̄` -/

/-- The order of the face poset of `Q̄`, in terms of the tight sets. -/
private theorem QbarCell_lt_iff {a b : QbarCell} :
    a < b ↔ qTight b.idx ⊂ qTight a.idx := Iff.rfl

/-- The sign change acting on the flags of `Q̄`. -/
private def simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    Simplex QbarCW.Cell k where
  toFun i := ⟨faceAct g (s i).idx⟩
  strictMono := by
    intro i j hij
    have h := s.strictMono hij
    have h' : qTight (faceAct g (s j).idx) ⊂ qTight (faceAct g (s i).idx) := by
      rw [tight_faceAct, tight_faceAct]
      exact (Finset.image_ssubset_image (consAct_injective g)).mpr (QbarCell_lt_iff.mp h)
    show (⟨faceAct g (s i).idx⟩ : QbarCell) < ⟨faceAct g (s j).idx⟩
    rw [QbarCell_lt_iff]
    exact h'

@[simp] private theorem simplexAct_apply (g : Fin 4 → ZMod 2) {k : ℕ}
    (s : Simplex QbarCW.Cell k) (i : Fin (k + 1)) :
    (simplexAct g s) i = ⟨faceAct g (s i).idx⟩ := rfl

@[simp] private theorem simplexAct_idx (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k)
    (i : Fin (k + 1)) : ((simplexAct g s) i).idx = faceAct g (s i).idx := rfl

/-- The sign change commutes with dropping a vertex of a flag. -/
private theorem face_simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (i : Fin (k + 2))
    (s : Simplex QbarCW.Cell (k + 1)) :
    Simplex.face i (simplexAct g s) = simplexAct g (Simplex.face i s) := by
  ext j
  rfl

/-- The affine point `∑ w_i · posR(F_i)` of the open simplex of the flag `s` with weights `w`. -/
private def ptW {k : ℕ} (s : Simplex QbarCW.Cell k) (w : Fin (k + 1) → ℝ) : E 4 :=
  ∑ i, w i • QbarPD.posR (s i).idx

/-- `ptW` at the uniform weights is the barycentre `bary` of the flag. -/
private theorem ptW_uniform {k : ℕ} (s : Simplex QbarCW.Cell k) :
    ptW s (fun _ => ((k + 1 : ℝ))⁻¹) = bary s := rfl

/-- The sign change commutes with the affine realization `ptW` of a flag. -/
private theorem ptW_simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k)
    (w : Fin (k + 1) → ℝ) :
    ptW (simplexAct g s) w = Work.FoldInst.act g (ptW s w) := by
  have h1 : ∀ i, QbarPD.posR (faceAct g (s i).idx)
      = Work.FoldInst.act g (QbarPD.posR (s i).idx) := fun i => posR_faceAct g (s i).idx
  simp only [ptW, simplexAct_idx]
  rw [show (∑ i, w i • QbarPD.posR (faceAct g (s i).idx))
      = ∑ i, w i • Work.FoldInst.act g (QbarPD.posR (s i).idx) from
    Finset.sum_congr rfl fun i _ => by rw [h1 i]]
  rw [← act_sum g Finset.univ w (fun i => QbarPD.posR (s i).idx)]

/-- The sign change commutes with the barycentre of a flag. -/
private theorem bary_simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    bary (simplexAct g s) = Work.FoldInst.act g (bary s) := by
  rw [← ptW_uniform (simplexAct g s), ← ptW_uniform s, ptW_simplexAct]

/-! ## 5. The face maps descend to the orbit relation of flags -/

/-- **The face maps descend to the orbit relation of flags.**  This is the well-definedness input
for the `Δ`-complex `mbarSd` of `M̄` (work package W4): dropping a vertex of a flag does not change
the orbit.  Given `γ ∈ Ksub (bary x.2)` from `h`, the same `γ` witnesses the conclusion; the two
inputs are `Ksub (bary x.2) ≤ Ksub (bary (face i x.2))` (the tight set of the top face only grows
when a vertex is dropped) and the equivariance of the barycentre, which uses `qAct_spec` and the
injectivity half of `Work.MbarHomology.ConvexCells.sd_realization_of_basic`. -/
theorem flagRel_face {k : ℕ} (i : Fin (k + 2)) {x y : Work.MbarHomology.FlagQ (k + 1)}
    (h : Work.MbarHomology.flagRel x y) :
    Work.MbarHomology.flagRel (x.1, Work.Subdivision.Simplex.face i x.2)
      (y.1, Work.Subdivision.Simplex.face i y.2) := by
  obtain ⟨γ, hγ, hy1, hy2⟩ := h
  refine ⟨γ, Ksub_bary_face i x.2 hγ, hy1, ?_⟩
  have hb : bary (simplexAct γ.1 x.2) = bary y.2 := by rw [bary_simplexAct, hy2]
  have hy2' : y.2 = simplexAct γ.1 x.2 := (bary_inj hb).symm
  calc bary (Simplex.face i y.2)
      = bary (Simplex.face i (simplexAct γ.1 x.2)) := by rw [hy2']
    _ = bary (simplexAct γ.1 (Simplex.face i x.2)) := by rw [face_simplexAct γ.1 i x.2]
    _ = Work.FoldInst.act γ.1 (bary (Simplex.face i x.2)) :=
        bary_simplexAct γ.1 (Simplex.face i x.2)

end

end Work.MbarHomology.Mbar
