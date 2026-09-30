import Mathlib
import Submission.Work.MbarHomology.Mbar.Sd
import Submission.Work.MbarHomology.ConvexCells.sd_carrier_of_basic
import Submission.Work.MbarHomology.ConvexCells.sd_realization_of_basic
import Submission.Work.MbarHomology.Qbar.QbarPD_carriers
import Submission.Work.MbarHomology.Qbar.qAct_spec
import Submission.Work.FoldInst.Quotient
import Submission.Work.DeltaHomology.RealizationDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells Work.DeltaHomology
open scoped BigOperators
open Convexity

noncomputable section

/-! ## 1. The sign-change action on the faces and constraints of `Q̄` -/

/-- `signVecT` is `Work.FoldInst.signVec` under the encoding `Work.FoldInst.enc`. -/
theorem signVecT_enc (g : Fin 4 → ZMod 2) :
    signVecT (Work.FoldInst.enc g) = Work.FoldInst.signVec g := by
  decide +revert

/-- The permutation of the `48` constraints is injective. -/
theorem consActT_injective : ∀ e : Fin 16, Function.Injective (consActT e) := by
  decide +revert

/-- The action on the `48` constraints of `QbarPD` is injective. -/
theorem consAct_injective (g : Fin 4 → ZMod 2) : Function.Injective (consAct g) :=
  consActT_injective (Work.FoldInst.enc g)

/-- The tight set of a sign-changed face is the sign-changed tight set. -/
theorem tight_faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) :
    QbarPD.tight (faceAct g f) = (QbarPD.tight f).image (consAct g) :=
  Work.MbarHomology.Qbar.qAct_spec.2.1 (Work.FoldInst.enc g) f

/-- `Work.FoldInst.act` is additive. -/
theorem act_add (g : Fin 4 → ZMod 2) (x y : Work.FoldInst.E4) :
    Work.FoldInst.act g (x + y) = Work.FoldInst.act g x + Work.FoldInst.act g y := by
  apply PiLp.ext
  intro i
  simp only [Work.FoldInst.act_apply_apply, PiLp.add_apply]
  ring

/-- `Work.FoldInst.act` is `ℝ`-homogeneous. -/
theorem act_smul (g : Fin 4 → ZMod 2) (c : ℝ) (y : Work.FoldInst.E4) :
    Work.FoldInst.act g (c • y) = c • Work.FoldInst.act g y := by
  apply PiLp.ext
  intro i
  simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `Work.FoldInst.act` commutes with linear combinations. -/
theorem act_sum (g : Fin 4 → ZMod 2) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (z : ι → Work.FoldInst.E4) :
    Work.FoldInst.act g (∑ i ∈ s, c i • z i) = ∑ i ∈ s, c i • Work.FoldInst.act g (z i) := by
  classical
  apply PiLp.ext
  intro k
  simp only [Work.FoldInst.act_apply_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The sign change acts on the `pos` points of the faces by `Work.FoldInst.act`. -/
theorem posR_faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) :
    QbarPD.posR (faceAct g f) = Work.FoldInst.act g (QbarPD.posR f) := by
  have hpos : qPos (faceActT (Work.FoldInst.enc g) f)
      = fun i => Work.FoldInst.signVec g i * qPos f i := by
    rw [Work.MbarHomology.Qbar.qAct_spec.1 (Work.FoldInst.enc g) f, signVecT_enc]
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

/-! ## 2. The affine points of the open simplices of a flag -/

/-- The index of the `i`-th face of a flag of `Q̄`. -/
def flagIdx {k : ℕ} (s : Simplex QbarCW.Cell k) (i : Fin (k + 1)) : Fin 865 :=
  (s i).idx

@[simp] theorem flagIdx_eq {k : ℕ} (s : Simplex QbarCW.Cell k) (i : Fin (k + 1)) :
    flagIdx s i = (s i).idx := rfl

/-- The affine point `∑ w_i · posR(F_i)` of the open simplex of the flag `s` with weights `w`. -/
def ptW {k : ℕ} (s : Simplex QbarCW.Cell k) (w : Fin (k + 1) → ℝ) : E 4 :=
  ∑ i, w i • QbarPD.posR (flagIdx s i)

/-- `ptW` at the uniform weights is the barycentre `bary` of the flag. -/
theorem ptW_uniform {k : ℕ} (s : Simplex QbarCW.Cell k) :
    ptW s (fun _ => ((k + 1 : ℝ))⁻¹) = bary s := rfl

/-- The weights of a standard simplex sum to one. -/
theorem sum_weights {k : ℕ} (w : StdSimplex ℝ (Fin (k + 1))) :
    ∑ i, w.weights i = 1 := by
  rw [← Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => by
      by_contra h
      exact hi (Finsupp.mem_support_iff.mpr h))]
  exact w.total

/-- The affine point of the open simplex of a flag lies in `Q̄`. -/
theorem ptW_mem {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) : ptW s w ∈ Work.FoldInst.Qbar := by
  rw [← QbarPD_Pset]
  show ∑ i, w i • QbarPD.posR (flagIdx s i) ∈ QbarPD.Pset
  exact QbarPD.Pset_convex.sum_mem (t := Finset.univ) (fun i _ => by simpa using hw i)
    (by simpa using hsum)
    (fun i _ => posR_mem_Pset_basic QbarPD_okBasic (flagIdx s i))

/-- The uniform weights on `Fin (k+1)` sum to one. -/
theorem uniform_sum (k : ℕ) :
    (∑ _i : Fin (k + 1), ((k + 1 : ℝ))⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

/-- The barycentre of a flag lies in `Q̄`. -/
theorem bary_mem {k : ℕ} (s : Simplex QbarCW.Cell k) : bary s ∈ Work.FoldInst.Qbar := by
  rw [← ptW_uniform s]
  exact ptW_mem s (fun _ => by positivity) (uniform_sum k)

/-- The top (largest) face of a flag, as an index. -/
def topIdx {k : ℕ} (s : Simplex QbarCW.Cell k) : Fin 865 := flagIdx s (Fin.last k)

/-- A constraint is tight at a point of the open simplex of a flag iff it is tight at the top
face of the flag. -/
theorem mem_tight_iff_top {k : ℕ} (s : Simplex QbarCW.Cell k) (c : Fin 48) :
    (∀ i, c ∈ QbarPD.tight (flagIdx s i)) ↔ c ∈ QbarPD.tight (topIdx s) := by
  refine ⟨fun h => h (Fin.last k), fun h i => ?_⟩
  have hle : s i ≤ s (Fin.last k) := by
    rcases lt_or_eq_of_le (Fin.le_last i) with hlt | heq
    · exact le_of_lt (s.strictMono hlt)
    · rw [heq]
  exact hle h

/-- The tight set of the affine point of a flag with strictly positive weights is the tight set of
the top face of the flag. -/
theorem ptW_tightAt {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    QbarPD.tightAt (ptW s w) = QbarPD.tight (topIdx s) := by
  have hcombo := PolytopeData.tightAt_combo (P := QbarPD) (s := Finset.univ) (w := w)
    (z := fun i => QbarPD.posR (flagIdx s i))
    (fun i _ => le_of_lt (hw i)) (by simpa using hsum)
    (fun i _ => posR_mem_Pset_basic QbarPD_okBasic (flagIdx s i))
  ext c
  have hiff : (∀ i, inner ℝ (QbarPD.nR c) (QbarPD.posR (flagIdx s i)) = QbarPD.bR c)
      ↔ c ∈ QbarPD.tight (topIdx s) :=
    Iff.trans (forall_congr' fun i => inner_posR_eq_iff_basic QbarPD_okBasic (flagIdx s i) c)
      (mem_tight_iff_top s c)
  simp only [ptW]
  rw [hcombo c]
  simp only [Finset.mem_univ, true_implies]
  exact Iff.trans ⟨fun h i => h i (ne_of_gt (hw i)), fun h i _ => h i⟩ hiff

/-- The tight set of the barycentre of a flag is the tight set of its top face. -/
theorem bary_tightAt {k : ℕ} (s : Simplex QbarCW.Cell k) :
    QbarPD.tightAt (bary s) = QbarPD.tight (topIdx s) := by
  rw [← ptW_uniform s]
  exact ptW_tightAt s (fun _ => by positivity) (uniform_sum k)

/-- The tight set of the top face of a flag is contained in the tight set of every point of the
closed simplex (the weights are only assumed nonnegative). -/
theorem tight_top_subset_tightAt {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    QbarPD.tight (topIdx s) ⊆ QbarPD.tightAt (ptW s w) := by
  have hmem : ptW s w ∈ QbarPD.Pset := by
    rw [QbarPD_Pset]; exact ptW_mem s hw hsum
  intro c hc
  rw [PolytopeData.tightAt_of_mem (P := QbarPD) hmem c]
  have hinner : inner ℝ (QbarPD.nR c) (ptW s w)
      = ∑ i, w i * inner ℝ (QbarPD.nR c) (QbarPD.posR (flagIdx s i)) :=
    PolytopeData.inner_sum_smul (P := QbarPD) Finset.univ w
      (fun i => QbarPD.posR (flagIdx s i)) c
  rw [hinner]
  have hb : ∀ i, inner ℝ (QbarPD.nR c) (QbarPD.posR (flagIdx s i)) = QbarPD.bR c :=
    fun i => inner_nR_posR_of_mem_basic QbarPD_okBasic (flagIdx s i) c
      ((mem_tight_iff_top s c).mpr hc i)
  rw [Finset.sum_congr rfl (fun i _ => by rw [hb i])]
  rw [← Finset.sum_mul, hsum, one_mul]

/-! ## 3. `Ksub` against the tight sets of the sides -/

/-- The subgroup of `Gg` generated by the face indices of `T` that are side constraints. -/
def KsubF (T : Finset (Fin 48)) : AddSubgroup Work.FoldInst.Gg :=
  AddSubgroup.closure {γ : Work.FoldInst.Gg |
    ∃ S : Fin 24, Fin.castAdd 24 S ∈ T ∧ γ = Work.FoldInst.sideType S}

/-- `KsubF` is monotone in the tight set. -/
theorem KsubF_mono {T T' : Finset (Fin 48)} (h : T ⊆ T') : KsubF T ≤ KsubF T' :=
  AddSubgroup.closure_mono fun _ ⟨S, hS, hg⟩ => ⟨S, h hS, hg⟩

/-- A side constraint is an equality at `y ∈ Q̄` iff it is a tight constraint there. -/
theorem sideSlack_eq_zero_iff_tightAt {y : E 4} (hy : y ∈ Work.FoldInst.Qbar) (S : Fin 24) :
    Fin.castAdd 24 S ∈ QbarPD.tightAt y ↔ Work.FoldInst.sideSlack S y = 0 := by
  have hy' : y ∈ QbarPD.Pset := QbarPD_Pset ▸ hy
  refine (PolytopeData.tightAt_of_mem (P := QbarPD) hy' (Fin.castAdd 24 S)).trans ?_
  have hnR : QbarPD.nR (Fin.castAdd 24 S)
      = ((1920 : ℝ))⁻¹ • Work.ConvexCells.toE (Work.FoldInst.sideNormal S) := by
    simp only [PolytopeData.nR, QbarPD_nrm, QbarPD_D, qNrm_castAdd, Nat.cast_ofNat]
  have hbR : QbarPD.bR (Fin.castAdd 24 S) = ((1920 : ℝ))⁻¹ := by
    simp only [PolytopeData.bR, QbarPD_rhs, QbarPD_D, qRhs_castAdd, Int.cast_one]
    norm_num
  rw [hnR, hbR, inner_smul_left, Work.ConvexCells.inner_toE_right]
  simp only [RCLike.conj_to_real]
  constructor
  · intro h
    have hX : (∑ j, (Work.FoldInst.sideNormal S j : ℝ) * y j) = 1 := by
      have h' : ((1920 : ℝ))⁻¹ * (∑ j, (Work.FoldInst.sideNormal S j : ℝ) * y j)
          = ((1920 : ℝ))⁻¹ * 1 := by rw [mul_one]; exact h
      exact mul_left_cancel₀ (by norm_num) h'
    rw [Work.FoldInst.sideSlack, hX, sub_self]
  · intro h
    have hX : (∑ j, (Work.FoldInst.sideNormal S j : ℝ) * y j) = 1 := by
      have h1 : (1 : ℝ) = ∑ j, (Work.FoldInst.sideNormal S j : ℝ) * y j := by
        rw [Work.FoldInst.sideSlack, sub_eq_zero] at h
        exact h
      exact h1.symm
    rw [hX, mul_one]

/-- The identification subgroup `Ksub y` at a point of `Q̄` is generated by the side constraints
tight there. -/
theorem Ksub_eq_KsubF {y : E 4} (hy : y ∈ Work.FoldInst.Qbar) :
    Work.FoldInst.Ksub y = KsubF (QbarPD.tightAt y) := by
  unfold Work.FoldInst.Ksub KsubF
  congr 1
  ext γ
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, (sideSlack_eq_zero_iff_tightAt hy S).mpr hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, (sideSlack_eq_zero_iff_tightAt hy S).mp hS, rfl⟩

/-! ## 4. The sign change acting on the flags of `Q̄` -/

/-- The order of the face poset of `Q̄`, in terms of the tight sets. -/
theorem QbarCell_lt_iff {a b : QbarCell} :
    a < b ↔ QbarPD.tight b.idx ⊂ QbarPD.tight a.idx := Iff.rfl

/-- The sign change acting on the flags of `Q̄`. -/
def simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    Simplex QbarCW.Cell k where
  toFun i := ⟨faceAct g (flagIdx s i)⟩
  strictMono := by
    intro i j hij
    have h := s.strictMono hij
    have h' : QbarPD.tight (faceAct g (flagIdx s j)) ⊂ QbarPD.tight (faceAct g (flagIdx s i)) := by
      rw [tight_faceAct, tight_faceAct]
      exact (Finset.image_ssubset_image (consAct_injective g)).mpr (QbarCell_lt_iff.mp h)
    show (⟨faceAct g (flagIdx s i)⟩ : QbarCW.Cell) < ⟨faceAct g (flagIdx s j)⟩
    rw [QbarCell_lt_iff]
    exact h'

@[simp] theorem simplexAct_idx (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k)
    (i : Fin (k + 1)) : flagIdx (simplexAct g s) i = faceAct g (flagIdx s i) := rfl

/-- The sign change commutes with the affine realization of a flag. -/
theorem ptW_simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k)
    (w : Fin (k + 1) → ℝ) :
    ptW (simplexAct g s) w = Work.FoldInst.act g (ptW s w) := by
  have h1 : ∀ i, QbarPD.posR (faceAct g (flagIdx s i))
      = Work.FoldInst.act g (QbarPD.posR (flagIdx s i)) :=
    fun i => posR_faceAct g (flagIdx s i)
  simp only [ptW, simplexAct_idx]
  rw [show (∑ i, w i • QbarPD.posR (faceAct g (flagIdx s i)))
      = ∑ i, w i • Work.FoldInst.act g (QbarPD.posR (flagIdx s i)) from
    Finset.sum_congr rfl fun i _ => by rw [h1 i]]
  rw [← act_sum g Finset.univ w (fun i => QbarPD.posR (flagIdx s i))]

/-- The sign change commutes with the barycentre of a flag. -/
theorem bary_simplexAct (g : Fin 4 → ZMod 2) {k : ℕ} (s : Simplex QbarCW.Cell k) :
    bary (simplexAct g s) = Work.FoldInst.act g (bary s) := by
  rw [← ptW_uniform (simplexAct g s), ← ptW_uniform s, ptW_simplexAct]

/-! ## 5. The bridge to the flag points of `PolytopeData` -/

/-- The `PolytopeData.FlagPt` carried by a flag and weights. -/
noncomputable def simplexFlagPt {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) : QbarPD.FlagPt where
  flag := List.ofFn (fun i => flagIdx s i)
  isFlag := (List.pairwise_ofFn).mpr (fun i j hij => s.strictMono hij)
  wt := fun i => w (Fin.cast (List.length_ofFn (f := fun i => flagIdx s i)) i)
  wt_pos := fun i => hw _
  wt_sum := by
    have hlen : (List.ofFn (fun i => flagIdx s i)).length = k + 1 := List.length_ofFn
    exact ((Finset.sum_congr rfl (fun i _ =>
        congrArg w (Fin.castOrderIso_apply hlen i).symm)).trans
      (Equiv.sum_comp ((Fin.castOrderIso hlen).toEquiv) w)).trans hsum

/-- The realization of the flag point of a flag is the affine point of the flag. -/
theorem simplexFlagPt_toE' {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    (simplexFlagPt s hw hsum).toE' = ptW s w := by
  have hlen : (List.ofFn (fun i => flagIdx s i)).length = k + 1 := List.length_ofFn
  have step1 : (simplexFlagPt s hw hsum).toE'
      = ∑ i : Fin (List.ofFn (fun i => flagIdx s i)).length,
          w (Fin.cast hlen i) • QbarPD.posR (flagIdx s (Fin.cast hlen i)) := by
    simp only [PolytopeData.FlagPt.toE', simplexFlagPt]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine congrArg₂ (· • ·) rfl (congrArg QbarPD.posR ?_)
    exact List.get_ofFn (fun j => flagIdx s j) i
  have step2 : (∑ i : Fin (List.ofFn (fun i => flagIdx s i)).length,
          w (Fin.cast hlen i) • QbarPD.posR (flagIdx s (Fin.cast hlen i)))
      = ∑ i : Fin (k+1), w i • QbarPD.posR (flagIdx s i) :=
    (Finset.sum_congr rfl (fun i _ => congrArg₂ (· • ·)
        (congrArg w (Fin.castOrderIso_apply hlen i).symm)
        (congrArg (fun j => QbarPD.posR (flagIdx s j))
          (Fin.castOrderIso_apply hlen i).symm))).trans
      (Equiv.sum_comp ((Fin.castOrderIso hlen).toEquiv)
        (fun i : Fin (k+1) => w i • QbarPD.posR (flagIdx s i)))
  exact step1.trans step2

/-- **The realization of an open flag simplex determines the flag.**  Two flag points with
strictly positive weights and the same realization have the same flag. -/
theorem ptW_inj_same {k : ℕ} (s t : Simplex QbarCW.Cell k) {w w' : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hw' : ∀ i, 0 < w' i) (hsum' : ∑ i, w' i = 1)
    (h : ptW s w = ptW t w') : s = t ∧ w = w' := by
  have hfl : simplexFlagPt s hw hsum = simplexFlagPt t hw' hsum' :=
    Work.MbarHomology.ConvexCells.flagPt_unique_basic QbarPD QbarPD_okBasic _ _
      (by rw [simplexFlagPt_toE', simplexFlagPt_toE']; exact h)
  have hflag : (simplexFlagPt s hw hsum).flag = (simplexFlagPt t hw' hsum').flag :=
    congrArg (fun x : QbarPD.FlagPt => x.flag) hfl
  simp only [simplexFlagPt] at hflag
  have hidx : (fun i => flagIdx s i) = (fun i => flagIdx t i) := List.ofFn_inj.mp hflag
  have hst : s = t := by
    refine Simplex.ext fun i => ?_
    have h1 : (s i).idx = (t i).idx := by
      rw [← flagIdx_eq, ← flagIdx_eq, congrFun hidx i]
    exact QbarCell.ext h1
  subst hst
  refine ⟨rfl, ?_⟩
  have hwt : (simplexFlagPt s hw hsum).wt = (simplexFlagPt s hw' hsum').wt := by
    have h := hfl
    simp only [simplexFlagPt] at h
    injection h with hwt
  simp only [simplexFlagPt] at hwt
  funext i
  have hlen : (List.ofFn (fun i => flagIdx s i)).length = k + 1 := List.length_ofFn
  exact congrFun hwt (Fin.cast hlen.symm i)

/-- **The realization of an open flag simplex determines its dimension.**  Flag simplices of
different dimensions cannot realize the same point with strictly positive weights. -/
theorem ptW_dim_eq {k k' : ℕ} (s : Simplex QbarCW.Cell k) (t : Simplex QbarCW.Cell k')
    {w : Fin (k + 1) → ℝ} {w' : Fin (k' + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (hw' : ∀ i, 0 < w' i) (hsum' : ∑ i, w' i = 1)
    (h : ptW s w = ptW t w') : k = k' := by
  have hfl : simplexFlagPt s hw hsum = simplexFlagPt t hw' hsum' :=
    Work.MbarHomology.ConvexCells.flagPt_unique_basic QbarPD QbarPD_okBasic _ _
      (by rw [simplexFlagPt_toE', simplexFlagPt_toE']; exact h)
  have hlen : (List.ofFn (fun i => flagIdx s i)).length
      = (List.ofFn (fun i => flagIdx t i)).length :=
    congrArg List.length (congrArg (fun x : QbarPD.FlagPt => x.flag) hfl)
  rw [List.length_ofFn, List.length_ofFn] at hlen
  omega


/-! ## 6. The relation on the flags, concretely -/

/-- The orbit relation of the flags, in terms of the action on the flags. -/
theorem flagRel_iff {k : ℕ} (x y : FlagQ k) :
    flagRel x y ↔ ∃ γ : Work.FoldInst.Gg, γ ∈ Work.FoldInst.Ksub (bary x.2) ∧
      y.1 = x.1 + γ.2 ∧ y.2 = simplexAct γ.1 x.2 := by
  constructor
  · rintro ⟨γ, hγ, h1, h2⟩
    refine ⟨γ, hγ, h1, ?_⟩
    refine (ptW_inj_same (simplexAct γ.1 x.2) y.2 (fun _ => by positivity) (uniform_sum k)
      (fun _ => by positivity) (uniform_sum k) ?_).1.symm
    rw [ptW_uniform, ptW_uniform, bary_simplexAct, h2]
  · rintro ⟨γ, hγ, h1, h2⟩
    exact ⟨γ, hγ, h1, by rw [h2, bary_simplexAct]⟩

/-- The identification subgroup at the barycentre of a flag is contained in the one at every point
of the closed simplex. -/
theorem Ksub_bary_le {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    Work.FoldInst.Ksub (bary s) ≤ Work.FoldInst.Ksub (ptW s w) := by
  rw [Ksub_eq_KsubF (bary_mem s), Ksub_eq_KsubF (ptW_mem s hw hsum)]
  refine KsubF_mono ?_
  rw [bary_tightAt s]
  exact tight_top_subset_tightAt s hw hsum

/-- The identification subgroup at a point of the open simplex of a flag. -/
theorem Ksub_ptW_eq {k : ℕ} (s : Simplex QbarCW.Cell k) {w : Fin (k + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    Work.FoldInst.Ksub (ptW s w) = KsubF (QbarPD.tight (topIdx s)) := by
  rw [Ksub_eq_KsubF (ptW_mem s (fun i => le_of_lt (hw i)) hsum), ptW_tightAt s hw hsum]

/-! ## 7. The characteristic maps -/

/-- The point of `Q̄` attached to a flag and a point of the standard simplex. -/
def chiPt {k : ℕ} (x : FlagQ k) (w : StdSimplex ℝ (Fin (k + 1))) : Work.FoldInst.Qbar :=
  ⟨ptW x.2 (fun i => w.weights i), ptW_mem x.2 (fun i => w.nonneg i) (sum_weights w)⟩

/-- The point of `M̄` attached to a flag and a point of the standard simplex. -/
def chiRep {k : ℕ} (x : FlagQ k) (w : StdSimplex ℝ (Fin (k + 1))) : Work.FoldInst.Mbar :=
  Work.FoldInst.mk (x.1, chiPt x w)

/-- The value of the characteristic map does not depend on the representative of the orbit. -/
theorem chiRep_eq {k : ℕ} {x y : FlagQ k} (h : flagRel x y)
    (w : StdSimplex ℝ (Fin (k + 1))) : chiRep x w = chiRep y w := by
  obtain ⟨γ, hγ, h1, h2⟩ := (flagRel_iff x y).mp h
  refine Quotient.sound ?_
  refine ⟨γ, Ksub_bary_le x.2 (fun i => w.nonneg i) (sum_weights w) hγ, ?_⟩
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show x.1 + γ.2 = y.1
    rw [h1]
  · show Work.FoldInst.act γ.1 (ptW x.2 (fun i => w.weights i))
      = ptW y.2 (fun i => w.weights i)
    exact (ptW_simplexAct γ.1 x.2 (fun i => w.weights i)).symm.trans (by rw [← h2])

theorem continuous_chiRep {k : ℕ} (x : FlagQ k) :
    Continuous fun w : StdSimplex ℝ (Fin (k + 1)) => chiRep x w := by
  have hpt : Continuous fun w : StdSimplex ℝ (Fin (k + 1)) =>
      (⟨ptW x.2 (fun i => w.weights i),
        ptW_mem x.2 (fun i => w.nonneg i) (sum_weights w)⟩ : Work.FoldInst.Qbar) :=
    Continuous.subtype_mk (by
      unfold ptW
      apply continuous_finsetSum
      intro i _
      exact (by fun_prop : Continuous fun w : StdSimplex ℝ (Fin (k + 1)) => w.weights i).smul
        continuous_const) _
  unfold chiRep Work.FoldInst.mk
  refine (continuous_quotient_mk' (s := Work.FoldInst.setoid)).comp ?_
  exact Continuous.prodMk continuous_const hpt

/-- The characteristic map attached to an orbit of flags, as a continuous map. -/
noncomputable def chiQuot (k : ℕ) :
    Quotient (flagSetoid k) → C(StdSimplex ℝ (Fin (k + 1)), TopCat.of Work.FoldInst.Mbar) :=
  Quotient.lift (fun x => ⟨fun w => chiRep x w, continuous_chiRep x⟩)
    (fun _ _ hab => ContinuousMap.ext fun w => chiRep_eq hab w)

theorem chiQuot_mk (k : ℕ) (x : FlagQ k) :
    chiQuot k (Quotient.mk (flagSetoid k) x) = ⟨fun w => chiRep x w, continuous_chiRep x⟩ :=
  rfl

/-- The characteristic map of a simplex of the barycentric subdivision of `M̄`. -/
noncomputable def chi (k : ℕ) (σ : Fin (mbarCard k)) :
    C(StdSimplex ℝ (Fin (k + 1)), TopCat.of Work.FoldInst.Mbar) :=
  chiQuot k (mbarEquiv k σ)



/-! ## 8. The realization of the barycentric subdivision -/

/-- The characteristic map of a simplex, as a singular simplex of `M̄`. -/
noncomputable def chiSSet (hface : MbarFaceCompat) (k : ℕ) (σ : Fin (mbarCard k)) :
    (TopCat.toSSet.obj (TopCat.of Work.FoldInst.Mbar)).obj
      (Opposite.op (SimplexCategory.mk k)) :=
  (TopCat.toSSetObjEquiv (TopCat.of Work.FoldInst.Mbar)
    (Opposite.op (SimplexCategory.mk k))).symm (chi k σ)

@[simp] theorem toSSetObjEquiv_chiSSet (hface : MbarFaceCompat) (k : ℕ)
    (σ : Fin (mbarCard k)) :
    TopCat.toSSetObjEquiv (TopCat.of Work.FoldInst.Mbar)
      (Opposite.op (SimplexCategory.mk k)) (chiSSet hface k σ) = chi k σ :=
  Equiv.apply_symm_apply _ _

/-- Face compatibility of the characteristic maps. -/
theorem chiSSet_face (hface : MbarFaceCompat) {k : ℕ}
    (σ : Fin (mbarCard (k + 1))) (i : Fin (k + 2)) :
    chiSSet hface k ((mbarSdOf hface).face σ i) = singFace i (chiSSet hface (k + 1) σ) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Work.FoldInst.Mbar)
    (Opposite.op (SimplexCategory.mk k))).injective
  ext z
  erw [toSSetObjEquiv_chiSSet, singFace, TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_chiSSet]
  show chi k ((mbarSdOf hface).face σ i) z = chi (k + 1) σ (StdSimplex.map i.succAbove z)
  rw [show (mbarSdOf hface).face σ i
      = (mbarEquiv k).symm (mbarFaceQ hface i (mbarEquiv (k + 1) σ)) from rfl]
  simp only [chi]
  rw [Equiv.apply_symm_apply]
  · refine Quotient.inductionOn (mbarEquiv (k + 1) σ) (fun x => ?_)
    rw [show (⟦x⟧ : Quotient (flagSetoid (k + 1))) = Quot.mk (flagSetoid (k + 1)) x from rfl]
    rw [mbarFaceQ_mk hface i x]
    show chiRep (x.1, Simplex.face i x.2) z = chiRep x (StdSimplex.map i.succAbove z)
    simp only [chiRep, chiPt]
    congr 2
    refine Subtype.ext ?_
    show ptW (Simplex.face i x.2) (fun j => z.weights j)
      = ptW x.2 (fun j => (StdSimplex.map i.succAbove z).weights j)
    rw [show ptW x.2 (fun j => (StdSimplex.map i.succAbove z).weights j)
        = ∑ j : Fin (k + 2),
            (StdSimplex.map i.succAbove z).weights j • QbarPD.posR (flagIdx x.2 j) from rfl,
      Fin.sum_univ_succAbove _ i]
    have hzero : (StdSimplex.map i.succAbove z).weights i = 0 := by
      rw [Convexity.StdSimplex.weights_map]
      exact Finsupp.mapDomain_of_notMem_range z.weights i
        (by simp [Set.mem_range, Fin.succAbove_ne])
    rw [hzero, zero_smul, zero_add]
    rw [show ptW (Simplex.face i x.2) (fun j => z.weights j)
        = ∑ a : Fin (k + 1), z.weights a • QbarPD.posR (flagIdx (Simplex.face i x.2) a)
        from rfl]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Convexity.StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
    refine congrArg₂ (· • ·) rfl (congrArg QbarPD.posR ?_)
    rw [flagIdx_eq, flagIdx_eq]
    rfl

/-- The characteristic maps of the barycentric subdivision of `M̄`. -/
noncomputable def chiSMap (hface : MbarFaceCompat) :
    DeltaSimplexMap (mbarSdOf hface) (TopCat.of Work.FoldInst.Mbar) where
  χ := fun k σ => chiSSet hface k σ
  face_compat := fun σ i => chiSSet_face hface σ i

@[simp] theorem chiSMap_cls (hface : MbarFaceCompat) (k : ℕ)
    (σ : Fin ((mbarSdOf hface).card k)) :
    DeltaSimplexMap.cls (chiSMap hface) k σ = chi k σ := by
  simp only [DeltaSimplexMap.cls, chiSMap, chiSSet]
  exact Equiv.apply_symm_apply _ _

/-! ## 9. The realization -/

/-- The simplex of `QbarCW` attached to a flag `l` of length `k+1`. -/
def simplexOfFlag {k : ℕ} (l : List (Fin 865)) (hlen : l.length = k + 1)
    (hp : l.Pairwise QbarPD.SubFace) : Simplex QbarCW.Cell k where
  toFun i := ⟨l.get (Fin.cast hlen.symm i)⟩
  strictMono := by
    intro i j hij
    exact QbarCell_lt_iff.mpr
      (List.Pairwise.rel_get_of_lt hp (show Fin.cast hlen.symm i < Fin.cast hlen.symm j from hij))

/-- The weights of a flag point on a fixed index type. -/
def flagWt {k : ℕ} (l : List (Fin 865)) (hlen : l.length = k + 1)
    (w : Fin l.length → ℝ) : Fin (k + 1) → ℝ :=
  fun i => w (Fin.cast hlen.symm i)

/-- A standard-simplex point built from a weight function. -/
noncomputable def stdSimplexOf {k : ℕ} (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : StdSimplex ℝ (Fin (k + 1)) where
  weights := Finsupp.equivFunOnFinite.symm w
  nonneg := by
    rw [Finsupp.le_def]
    intro i
    rw [Finsupp.zero_apply,
      show (Finsupp.equivFunOnFinite.symm w : Fin (k + 1) →₀ ℝ) i = w i from
        congrFun (Equiv.apply_symm_apply Finsupp.equivFunOnFinite w) i]
    exact hw i
  total := by
    rw [Finsupp.sum_fintype (Finsupp.equivFunOnFinite.symm w) (fun _ r => r) (fun i => by simp)]
    rw [show (∑ i, (Finsupp.equivFunOnFinite.symm w : Fin (k + 1) →₀ ℝ) i) = ∑ i, w i from
      Finset.sum_congr rfl (fun i _ =>
        congrFun (Equiv.apply_symm_apply Finsupp.equivFunOnFinite w) i)]
    exact hsum

theorem stdSimplexOf_weights {k : ℕ} (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (i : Fin (k + 1)) :
    (stdSimplexOf w hw hsum).weights i = w i := by
  rw [stdSimplexOf,
    show (Finsupp.equivFunOnFinite.symm w : Fin (k + 1) →₀ ℝ) i = w i from
      congrFun (Equiv.apply_symm_apply Finsupp.equivFunOnFinite w) i]


/-- The realization of an open simplex of `mbarSd` is its characteristic map. -/
theorem real_eq_chi (hface : MbarFaceCompat) (p : OpenSimplex (mbarSdOf hface)) :
    DeltaSimplexMap.real (chiSMap hface) p = chi p.dim p.idx p.pt := by
  rw [show DeltaSimplexMap.real (chiSMap hface) p
      = DeltaSimplexMap.cls (chiSMap hface) p.dim p.idx p.pt from rfl, chiSMap_cls]

/-- The affine realization of a flag point of `Q̄` lies in `Q̄`. -/
theorem flagPt_mem_Qbar (s : QbarPD.FlagPt) : s.toE' ∈ Work.FoldInst.Qbar :=
  QbarPD_Pset ▸ Work.MbarHomology.ConvexCells.flagPt_mem_basic QbarPD QbarPD_okBasic s

/-- Reindexing a sum over `Fin n` to a sum over `Fin (k+1)`. -/
theorem sum_cast_eq {k n : ℕ} (h : n = k + 1) (f : Fin n → ℝ) :
    (∑ i : Fin (k + 1), f (Fin.cast h.symm i)) = ∑ j : Fin n, f j :=
  Equiv.sum_comp ((Fin.castOrderIso h.symm).toEquiv) f

/-- The standard-simplex point of the weights of a flag. -/
noncomputable def flagPtW {k : ℕ} (l : List (Fin 865)) (hlen : l.length = k + 1)
    (w : Fin l.length → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    StdSimplex ℝ (Fin (k + 1)) :=
  stdSimplexOf (flagWt l hlen w) (fun i => le_of_lt (hw _)) (by
    rw [show (∑ i, flagWt l hlen w i) = ∑ j : Fin l.length, w j from sum_cast_eq hlen w]
    exact hsum)

theorem flagPtW_weights {k : ℕ} (l : List (Fin 865)) (hlen : l.length = k + 1)
    (w : Fin l.length → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (i : Fin (k + 1)) :
    (flagPtW l hlen w hw hsum).weights i = w (Fin.cast hlen.symm i) :=
  stdSimplexOf_weights (flagWt l hlen w) (fun i => le_of_lt (hw _)) _ i

/-- **The open simplex attached to a flag point of `Q̄`.** -/
noncomputable def openSimplexOf (hface : MbarFaceCompat) (c : ZMod 2) (k : ℕ)
    (s : QbarPD.FlagPt) (hk : s.flag.length = k + 1) : OpenSimplex (mbarSdOf hface) where
  dim := k
  idx := (mbarEquiv k).symm (Quotient.mk (flagSetoid k) (c, simplexOfFlag s.flag hk s.isFlag))
  pt := flagPtW s.flag hk s.wt s.wt_pos s.wt_sum
  pos := fun i => (flagPtW_weights s.flag hk s.wt s.wt_pos s.wt_sum i) ▸ s.wt_pos _

/-- The realization of the open simplex attached to a flag point of `Q̄`. -/
theorem real_openSimplexOf (hface : MbarFaceCompat) (c : ZMod 2) (k : ℕ)
    (s : QbarPD.FlagPt) (hk : s.flag.length = k + 1) :
    DeltaSimplexMap.real (chiSMap hface) (openSimplexOf hface c k s hk)
      = Work.FoldInst.mk (c, ⟨s.toE', flagPt_mem_Qbar s⟩) := by
  have hw : ∀ i : Fin (k + 1),
      (openSimplexOf hface c k s hk).pt.weights i = s.wt (Fin.cast hk.symm i) :=
    fun i => flagPtW_weights s.flag hk s.wt s.wt_pos s.wt_sum i
  have hpt : ptW (simplexOfFlag s.flag hk s.isFlag)
      (fun i => (openSimplexOf hface c k s hk).pt.weights i) = s.toE' := by
    simp only [ptW, simplexOfFlag, flagIdx]
    have h1 : (∑ i : Fin (k + 1),
          (openSimplexOf hface c k s hk).pt.weights i •
            QbarPD.posR (s.flag.get (Fin.cast hk.symm i)))
        = ∑ i : Fin (k + 1),
            s.wt (Fin.cast hk.symm i) • QbarPD.posR (s.flag.get (Fin.cast hk.symm i)) :=
      Finset.sum_congr rfl fun i _ => by rw [hw i]
    exact h1.trans (Equiv.sum_comp ((Fin.castOrderIso hk.symm).toEquiv)
      (fun j : Fin s.flag.length => s.wt j • QbarPD.posR (s.flag.get j)))
  rw [real_eq_chi]
  show chi k ((mbarEquiv k).symm (Quotient.mk (flagSetoid k)
      (c, simplexOfFlag s.flag hk s.isFlag))) (flagPtW s.flag hk s.wt s.wt_pos s.wt_sum) = _
  simp only [chi]
  rw [Equiv.apply_symm_apply]
  show chiRep (c, simplexOfFlag s.flag hk s.isFlag)
    (flagPtW s.flag hk s.wt s.wt_pos s.wt_sum) = _
  simp only [chiRep, chiPt]
  exact congrArg (fun z => Work.FoldInst.mk (c, z)) (Subtype.ext hpt)

/-- **Every point of `M̄` lies in an open simplex of the barycentric subdivision.** -/
theorem exists_openSimplex (hface : MbarFaceCompat) (p : Work.FoldInst.Mbar) :
    ∃ q : OpenSimplex (mbarSdOf hface), DeltaSimplexMap.real (chiSMap hface) q = p := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep p
  obtain ⟨c, y⟩ := a
  obtain ⟨yv, hyv⟩ := y
  have hyvq : yv ∈ QbarPD.Pset := QbarPD_Pset ▸ hyv
  have hmem : yv ∈ (fun s : QbarPD.FlagPt => s.toE') '' Set.univ :=
    (Work.MbarHomology.ConvexCells.sd_realization_of_basic QbarPD QbarPD_checksBasic
      Work.MbarHomology.Qbar.QbarPD_carriers).2.2 hyvq
  rw [Set.mem_image] at hmem
  obtain ⟨s, -, hs⟩ := hmem
  obtain ⟨k, hk⟩ : ∃ k, s.flag.length = k + 1 :=
    ⟨s.flag.length - 1, by
      have h1 := List.length_pos_of_ne_nil s.flag_ne_nil
      omega⟩
  refine ⟨openSimplexOf hface c k s hk, ?_⟩
  rw [real_openSimplexOf]
  rw [show (⟨s.toE', flagPt_mem_Qbar s⟩ : Work.FoldInst.Qbar) = ⟨yv, hyv⟩ from Subtype.ext hs]
  exact ha

/-- **The topology of `M̄` is the weak topology of the characteristic maps.** -/
theorem mbar_weak (hface : MbarFaceCompat) (s : Set Work.FoldInst.Mbar)
    (h : ∀ (k : ℕ) (σ : Fin (mbarCard k)), IsOpen ((chi k σ) ⁻¹' s)) : IsOpen s := by
  let Φ : (Σ k : Fin 5, Σ _σ : Fin (mbarCard (k : ℕ)), StdSimplex ℝ (Fin ((k : ℕ) + 1))) →
      Work.FoldInst.Mbar := fun x => chi (x.1 : ℕ) x.2.1 x.2.2
  have hcont : Continuous Φ := by
    apply continuous_sigma
    intro k
    apply continuous_sigma
    intro σ
    exact (chi (k : ℕ) σ).continuous
  have hsurj : Function.Surjective Φ := by
    intro p
    obtain ⟨q, hq⟩ := exists_openSimplex hface p
    have hdim : q.dim ≤ 4 := by
      by_contra h'
      have h0 : (mbarSdOf hface).card q.dim = 0 := by
        apply DeltaCx.card_eq_zero
        show 4 < q.dim
        omega
      exact Fin.elim0 (h0 ▸ q.idx)
    exact ⟨⟨⟨q.dim, by omega⟩, q.idx, q.pt⟩, by
      show chi q.dim q.idx q.pt = p
      rw [← hq, real_eq_chi]⟩
  refine ((Topology.isCoinducing_iff.mp
    (Topology.IsQuotientMap.of_surjective_continuous hsurj hcont).isCoinducing) s).mp ?_
  rw [isOpen_sigma_iff]
  intro k
  rw [isOpen_sigma_iff]
  intro σ
  exact h (k : ℕ) σ


/-- The characteristic map of an orbit is the class of a chosen representative. -/
theorem chi_eq_chiRep (k : ℕ) (σ : Fin (mbarCard k))
    (w : StdSimplex ℝ (Fin (k + 1))) :
    chi k σ w = chiRep (Quotient.out (mbarEquiv k σ)) w := by
  show chiQuot k (mbarEquiv k σ) w = chiRep (Quotient.out (mbarEquiv k σ)) w
  conv_lhs => rw [← Quotient.out_eq (mbarEquiv k σ)]
  rw [chiQuot_mk]
  rfl

/-- **The realization of an open simplex of `mbarSd` is injective.** -/
theorem real_injective (hface : MbarFaceCompat) :
    Function.Injective (DeltaSimplexMap.real (chiSMap hface)) := by
  intro q' q hq
  obtain ⟨k', σ', w', hw'⟩ := q'
  obtain ⟨k, σ, w, hw⟩ := q
  have hkk' : chi k' σ' w' = chi k σ w := by
    have h1 := real_eq_chi hface (⟨k', σ', w', hw'⟩ : OpenSimplex (mbarSdOf hface))
    have h2 := real_eq_chi hface (⟨k, σ, w, hw⟩ : OpenSimplex (mbarSdOf hface))
    exact h1.symm.trans (hq.trans h2)
  have h : chiRep (Quotient.out (mbarEquiv k' σ')) w' = chiRep (Quotient.out (mbarEquiv k σ)) w :=
    (chi_eq_chiRep k' σ' w').symm.trans (hkk'.trans (chi_eq_chiRep k σ w))
  set x' := Quotient.out (mbarEquiv k' σ') with hx'def
  set x := Quotient.out (mbarEquiv k σ) with hxdef
  simp only [chiRep, chiPt] at h
  obtain ⟨γ, hγ, hact⟩ := Quotient.exact h
  have h1 : x.1 = x'.1 + γ.2 := by
    have hh := congrArg (fun z : Work.FoldInst.Xbar => z.1) hact
    simp only [Work.FoldInst.actX_fst] at hh
    exact hh.symm
  have h2 : ptW x.2 (fun i => w.weights i)
      = Work.FoldInst.act γ.1 (ptW x'.2 (fun i => w'.weights i)) := by
    have hh := congrArg (fun z : Work.FoldInst.Xbar => z.2.1) hact
    exact hh.symm
  have h2' : ptW x.2 (fun i => w.weights i)
      = ptW (simplexAct γ.1 x'.2) (fun i => w'.weights i) := by
    rw [h2, ptW_simplexAct]
  have hdim : k = k' :=
    ptW_dim_eq x.2 (simplexAct γ.1 x'.2) (fun i => hw i)
      (Convexity.StdSimplex.total_of_fintype w) (fun i => hw' i)
      (Convexity.StdSimplex.total_of_fintype w') h2'
  subst hdim
  have hx : x.2 = simplexAct γ.1 x'.2 ∧ (fun i => w.weights i) = (fun i => w'.weights i) :=
    ptW_inj_same x.2 (simplexAct γ.1 x'.2) (fun i => hw i)
      (Convexity.StdSimplex.total_of_fintype w) (fun i => hw' i)
      (Convexity.StdSimplex.total_of_fintype w') h2'
  obtain ⟨hx2, hw2⟩ := hx
  have hwt : w = w' := by
    refine Convexity.StdSimplex.ext (Finsupp.ext fun i => ?_)
    exact congrFun hw2 i
  have hγbary : γ ∈ Work.FoldInst.Ksub (bary x'.2) := by
    rw [Ksub_eq_KsubF (bary_mem x'.2), bary_tightAt x'.2,
      ← Ksub_ptW_eq x'.2 (fun i => hw' i) (Convexity.StdSimplex.total_of_fintype w')]
    exact hγ
  have hrel : flagRel x' x := by
    refine ⟨γ, hγbary, ?_, ?_⟩
    · exact h1
    · rw [hx2, bary_simplexAct]
  have hσ : σ' = σ := by
    refine (mbarEquiv k).injective ?_
    rw [show mbarEquiv k σ' = Quotient.mk (flagSetoid k) x' from (Quotient.out_eq _).symm,
      Quotient.sound hrel,
      show Quotient.mk (flagSetoid k) x = mbarEquiv k σ from (Quotient.out_eq _)]
  subst hσ
  subst hwt
  rfl

/-- **The barycentric subdivision of `M̄` is realized in `M̄`.** -/
noncomputable def mbarRealData (hface : MbarFaceCompat) :
    DeltaRealization (mbarSdOf hface) (TopCat.of Work.FoldInst.Mbar) where
  toDeltaSimplexMap := chiSMap hface
  compact := inferInstance
  t2 := inferInstance
  bij := fun p => by
    obtain ⟨q, hq⟩ := exists_openSimplex hface p
    exact ⟨q, hq, fun q' hq' => real_injective hface (hq'.trans hq.symm)⟩
  weak := fun s => ⟨fun hs k σ => hs.preimage (chi k σ).continuous,
    fun h => mbar_weak hface s h⟩


/-- **The barycentric subdivision of `M̄` is realized in `M̄`** (work package W4 of
`Submission/Work/NOTES_LEAD_eA.md`, §2(b)).

The characteristic maps are `χ σ w := Quot.mk (c, Σ_i w_i • posR (F_i))` for a flag `(c,s)`
representing the orbit `σ` and `w : StdSimplex ℝ (Fin (k+1))`, using `Work.FoldInst.mk` and
`QbarPD.posR`.  The three point-set conditions are:

* *face compatibility*: two representatives of a face differ by `γ ∈ Ksub (bary (top s))`, which
  also lies in `Ksub` at every point of the closed simplex (where more sides are tight), so `mk`
  identifies the two values;
* *unique open simplex*: existence from `Work.MbarHomology.ConvexCells.sd_realization_of_basic`
  applied to `QbarPD` with `QbarPD_checksBasic` and `QbarPD_carriers`, uniqueness from its
  injectivity half together with `flagRel`;
* *weak topology*: `M̄` is compact and `T2` (`Work.FoldInst`), and the `χ σ` are finitely many
  continuous maps from compact simplices whose images cover `M̄`, so the image of a closed set is
  closed (the pattern of `Work.PieceHomology.torus2_weakTopology`).

The `hface` argument is `Work.MbarHomology.Mbar.flagRel_face`, whose statement is proved in
parallel. -/
theorem mbarReal_exists (hface : Work.MbarHomology.MbarFaceCompat) : Nonempty (Work.DeltaHomology.DeltaRealization (Work.MbarHomology.mbarSdOf hface) (TopCat.of Work.FoldInst.Mbar)) :=
  ⟨mbarRealData hface⟩

end

end Work.MbarHomology.Mbar
