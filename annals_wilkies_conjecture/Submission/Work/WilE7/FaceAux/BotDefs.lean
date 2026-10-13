/-
  WilE7 (`Submission.Work.WilE7.FaceAux.BotDefs`): the semi-Pfaffian presentation of the
  *bottom face* of a cell.

  Given a semi-Pfaffian base `Z : SemiPf (p + (m+1))` with base cell
  `C = π_p (connectedComponentIn Z.set u₀)`, the bottom face is

    `{y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = -1}`.

  It is presented here as the projection of a connected component of a semi-Pfaffian set in
  `ℝ^{(p+1)+(m+1)}`: the base set `Z` is zero-padded by one *vertical* coordinate `t` (placed at
  the last position, index `p + (m+1)`), the vertical coordinate is cut by the single equation
  `t + 1 = 0` (`botEq`), and the coordinates are then permuted (`botPerm`) so that `t` sits
  directly after the base coordinates, i.e. so that `projFirst (p+1) (m+1)` is exactly
  `(base, t)`.

  This file records the construction (`botY1`, `botPinPt`) and the elementary memberships; the
  two non-trivial inputs are

  * `Work.WilE7.FaceAux.botY1_component` — the connected component of the cut set through
    `botPinPt u₀`, which is the image of the component of `Z` through `u₀`,
  * `Work.WilE7.FaceAux.botPerm_proj` — the coordinate permutation identifying `(base, t)` with
    the first `p+1` coordinates,

  and the assembly is `Submission/Work/WilE7/FaceAux/faceBot_star`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE7.pad_component_proj
import Submission.Work.WilE7.BandAux.BandDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.FaceAux
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The dimensions and the vertical index -/

/-- The dimension `p + (m+1)` of the base set. -/
abbrev botN (p m : ℕ) : ℕ := p + (m + 1)

/-- The target dimension `(p+1) + (m+1)`; it is the successor of `botN p m`. -/
abbrev botK (p m : ℕ) : ℕ := (p + 1) + (m + 1)

theorem botN_le_botK (p m : ℕ) : botN p m ≤ botK p m := by
  simp only [botN, botK]; omega

theorem botK_eq_succ (p m : ℕ) : botK p m = botN p m + 1 := by
  simp only [botN, botK]; omega

/-- The index of the new vertical coordinate in `Fin (botK p m)`. -/
def botIdx (p m : ℕ) : Fin (botK p m) := ⟨botN p m, by simp only [botN, botK]; omega⟩

theorem botIdx_val (p m : ℕ) : (botIdx p m).val = botN p m := rfl

/-- `botIdx` is the last index of `Fin (botK p m)`. -/
theorem botIdx_isLast (p m : ℕ) : (botIdx p m).val = botK p m - 1 := by
  simp only [botIdx, botN, botK]; omega

/-- Every index which is not in the base block is the vertical index. -/
theorem eq_botIdx_of_not_lt {p m : ℕ} {i : Fin (botK p m)} (h : ¬ (i : ℕ) < botN p m) :
    i = botIdx p m := by
  apply Fin.ext
  simp only [botIdx, botN, botK] at h ⊢
  omega

/-! ## §2. The cut set `Z × {-1}` -/

/-- The single equation `t + 1 = 0` cutting the vertical coordinate to `-1`. -/
def botEq (p m r : ℕ) : EAPoly (botK p m) r :=
  MvPolynomial.X (Sum.inl (botIdx p m)) + 1

/-- The cut set: `Z` zero-padded by the vertical coordinate, cut by `t = -1`. -/
noncomputable def botY1 {p m : ℕ} (Z : SemiPf (p + (m + 1))) : SemiPf (botK p m) :=
  SemiPf.addConds (SemiPf.pad (botN_le_botK p m) Z)
    [botEq p m (SemiPf.pad (botN_le_botK p m) Z).r] []

/-- The canonical point of the cut set: `x` zero-padded, with vertical coordinate `-1`. -/
def botPinPt {p m : ℕ} (x : Fin (p + (m + 1)) → ℝ) : Fin (botK p m) → ℝ :=
  fun i => if h : (i : ℕ) < botN p m then x ⟨(i : ℕ), h⟩ else -1

theorem botPinPt_apply {p m : ℕ} (x : Fin (p + (m + 1)) → ℝ) (i : Fin (botK p m)) :
    botPinPt x i = if h : (i : ℕ) < botN p m then x ⟨(i : ℕ), h⟩ else -1 := rfl

theorem botPinPt_idx {p m : ℕ} (x : Fin (p + (m + 1)) → ℝ) :
    botPinPt x (botIdx p m) = -1 := by
  rw [botPinPt_apply, dif_neg (by rw [botIdx_val]; exact Nat.lt_irrefl _)]

theorem continuous_botPinPt (p m : ℕ) : Continuous (botPinPt (p := p) (m := m)) := by
  apply continuous_pi
  intro i
  by_cases h : (i : ℕ) < botN p m
  · have hf : (fun x : Fin (p + (m + 1)) → ℝ => botPinPt x i) = fun x => x ⟨(i : ℕ), h⟩ := by
      funext x
      rw [botPinPt_apply, dif_pos h]
    rw [hf]
    exact continuous_apply _
  · have hf : (fun x : Fin (p + (m + 1)) → ℝ => botPinPt x i) = fun _ => (-1 : ℝ) := by
      funext x
      rw [botPinPt_apply, dif_neg h]
    rw [hf]
    exact continuous_const

theorem takeZ_botPinPt {p m : ℕ} (x : Fin (p + (m + 1)) → ℝ) :
    takeZ (botN_le_botK p m) (botPinPt x) = x := by
  funext i
  show botPinPt x (Fin.castLE (botN_le_botK p m) i) = x i
  rw [botPinPt_apply, dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
  exact congrArg x (Fin.ext (by rw [Fin.val_castLE]))

/-! ## §3. The point set of `botY1` -/

theorem eaEval_botEq {p m r : ℕ} (c : EAChain (botK p m) r) (w : Fin (botK p m) → ℝ) :
    eaEval c (botEq p m r) w = w (botIdx p m) + 1 := by
  simp [botEq, eaEval]

theorem botEq_deg {p m r : ℕ} : atomDeg (botEq p m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_add
    (MvPolynomial.X (Sum.inl (botIdx p m)) : EAPoly (botK p m) r) (1 : EAPoly (botK p m) r)
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_one] at h
  simp only [atomDeg, botEq]
  omega

/-- **The point set of `botY1`.**  Membership is: the truncation of `u` lies in `Z.set` and the
vertical coordinate is `-1`.  (The cube constraint on the vertical coordinate is implied: it is
`-1`.) -/
theorem botY1_set {p m : ℕ} (Z : SemiPf (p + (m + 1))) :
    (botY1 Z).set = {u : Fin (botK p m) → ℝ |
      takeZ (botN_le_botK p m) u ∈ Z.set ∧ u (botIdx p m) = -1} := by
  have h1 : ∀ u : Fin (botK p m) → ℝ, u ∈ (botY1 Z).set ↔
      ((u ∈ cubeC (botK p m) ∧ takeZ (botN_le_botK p m) u ∈ Z.set) ∧
        u (botIdx p m) + 1 = 0) := by
    intro u
    rw [botY1, SemiPf.addConds_set, SemiPf.pad_set]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_singleton, forall_eq,
      List.not_mem_nil, forall_const, and_true, eaEval_botEq]
    tauto
  ext u
  rw [h1 u]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_, hZ⟩, hp⟩
    exact ⟨hZ, by linarith⟩
  · rintro ⟨hZ, ht⟩
    refine ⟨⟨?_, hZ⟩, by linarith⟩
    intro i
    by_cases h : (i : ℕ) < botN p m
    · exact hZ.1 ⟨(i : ℕ), h⟩
    · have hi : i = botIdx p m := eq_botIdx_of_not_lt h
      rw [hi, ht]
      norm_num

/-- **Membership in `botY1`.** -/
theorem mem_botY1 {p m : ℕ} (Z : SemiPf (p + (m + 1))) {u : Fin (botK p m) → ℝ} :
    u ∈ (botY1 Z).set ↔ takeZ (botN_le_botK p m) u ∈ Z.set ∧ u (botIdx p m) = -1 := by
  rw [botY1_set]
  simp only [Set.mem_ofPred_eq]

theorem botPinPt_mem {p m : ℕ} (Z : SemiPf (p + (m + 1))) {x : Fin (p + (m + 1)) → ℝ}
    (hx : x ∈ Z.set) : botPinPt x ∈ (botY1 Z).set := by
  rw [mem_botY1]
  exact ⟨by rw [takeZ_botPinPt]; exact hx, botPinPt_idx x⟩

/-- Every point of `botY1` is the pinned point of its truncation. -/
theorem botPinPt_takeZ {p m : ℕ} (Z : SemiPf (p + (m + 1))) {u : Fin (botK p m) → ℝ}
    (hu : u ∈ (botY1 Z).set) : botPinPt (takeZ (botN_le_botK p m) u) = u := by
  have ht : u (botIdx p m) = -1 := (mem_botY1 Z).mp hu |>.2
  funext i
  rw [botPinPt_apply]
  by_cases h : (i : ℕ) < botN p m
  · rw [dif_pos h]
    exact congrArg u (Fin.ext rfl)
  · rw [dif_neg h]
    have hi : i = botIdx p m := eq_botIdx_of_not_lt h
    rw [hi, ht]

theorem takeZ_mem_of_mem_botY1 {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    {u : Fin (botK p m) → ℝ} (hu : u ∈ (botY1 Z).set) :
    takeZ (botN_le_botK p m) u ∈ Z.set :=
  (mem_botY1 Z).mp hu |>.1

/-! ## §4. Format and degree of the cut set -/

theorem botY1_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) :
    (botY1 Z).fmt = Z.fmt + 1 := by
  rw [botY1, SemiPf.addConds_fmt]
  show (SemiPf.pad (botN_le_botK p m) Z).fmt = Z.fmt + 1
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.SemiPf.pad, botN, botK]
  omega

theorem botY1_deg {p m : ℕ} (Z : SemiPf (p + (m + 1))) :
    (botY1 Z).deg ≤ 3 * (Z.deg + 1) := by
  have hpad : (SemiPf.pad (botN_le_botK p m) Z).deg ≤ Z.deg := semipf_deg_pad_le _ Z
  have hadd := SemiPf.addConds_deg_le (SemiPf.pad (botN_le_botK p m) Z)
    [botEq p m (SemiPf.pad (botN_le_botK p m) Z).r] []
  have hsum : ((List.map atomDeg [botEq p m (SemiPf.pad (botN_le_botK p m) Z).r]).sum
      + (List.map atomDeg ([] : List (EAPoly (botK p m)
          (SemiPf.pad (botN_le_botK p m) Z).r))).sum) ≤ 2 := by
    simpa using botEq_deg (p := p) (m := m) (r := (SemiPf.pad (botN_le_botK p m) Z).r)
  have h1 : (botY1 Z).deg
      ≤ (SemiPf.pad (botN_le_botK p m) Z).deg
        + max 1 (SemiPf.pad (botN_le_botK p m) Z).deg * 2 := by
    rw [botY1]
    exact le_trans hadd (Nat.add_le_add_left (Nat.mul_le_mul_left _ hsum) _)
  have h2 : max 1 (SemiPf.pad (botN_le_botK p m) Z).deg ≤ Z.deg + 1 := by
    have h3 : max 1 (SemiPf.pad (botN_le_botK p m) Z).deg ≤ max 1 Z.deg :=
      max_le_max le_rfl hpad
    omega
  calc (botY1 Z).deg
      ≤ (SemiPf.pad (botN_le_botK p m) Z).deg
        + max 1 (SemiPf.pad (botN_le_botK p m) Z).deg * 2 := h1
    _ ≤ (Z.deg + 1) + (Z.deg + 1) * 2 :=
        Nat.add_le_add (by omega) (Nat.mul_le_mul_right 2 h2)
    _ = 3 * (Z.deg + 1) := by ring

/-! ## §5. The coordinate permutation moving the pinned coordinate to position `p` -/

/-- The permutation of `Fin (botK p m)` swapping the first coordinate *after* the base block
(index `p`) with the vertical coordinate (index `botN p m`). -/
def botPerm (p m : ℕ) : Equiv.Perm (Fin (botK p m)) :=
  Equiv.swap (⟨p, by simp only [botK]; omega⟩ : Fin (botK p m)) (botIdx p m)

end Work.WilE7.FaceAux
