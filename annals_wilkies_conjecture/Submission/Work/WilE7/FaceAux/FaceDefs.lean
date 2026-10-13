/-
  WilE7 (`Submission.Work.WilE7.FaceAux.FaceDefs`): the semi-Pfaffian presentation of the
  *top face* of the top cell.

  Given a semi-Pfaffian base `Z : SemiPf (p + (m+1))` with the base cell
  `C = π_p (connectedComponentIn Z.set u₀)`, the top face of the cell is

    `faceTop = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = 1}`.

  It is presented here as the projection of a connected component of a semi-Pfaffian set in
  `ℝ^{(p+1)+(m+1)}`: the base set `Z` is zero-padded by one *vertical* coordinate `t` (placed at
  the last position, index `p + (m+1)`), the vertical coordinate is cut by the single equation
  `t = 1` (`faceEq`), and the coordinates are then permuted so that `t` sits directly after the
  base coordinates, i.e. so that `projFirst (p+1) (m+1)` is exactly `(base, t)`.

  The file records the construction (`faceZp`, `faceY1`, `facePoint`, `faceExtract`) and the
  elementary memberships; the two non-trivial inputs are

  * `Work.WilE7.FaceAux.facePerm` — the coordinate permutation identifying `(base, t)` with the
    first `p+1` coordinates (`faceExtract`), and
  * `Work.WilE7.FaceAux.faceY1_component` — the connected component of the cut set through
    `facePoint u₀`, which is the homeomorphic image of the component of `Z` through `u₀`.

  The assembly is `Submission/Work/WilE7/FaceAux/faceTop_star`.
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

/-- The padded dimension `p + (m+1)`; the target dimension `(p+1) + (m+1)` is its successor. -/
abbrev faceN (p m : ℕ) : ℕ := p + (m + 1)

/-- The target dimension `(p+1) + (m+1)`. -/
abbrev faceK (p m : ℕ) : ℕ := (p + 1) + (m + 1)

theorem faceN_le_faceK (p m : ℕ) : faceN p m ≤ faceK p m := by
  simp only [faceN, faceK]; omega

/-- The index of the new vertical coordinate in `Fin (faceK p m)`. -/
def faceIdx (p m : ℕ) : Fin (faceK p m) := ⟨faceN p m, by simp only [faceN, faceK]; omega⟩

/-- The index of the vertical coordinate in the *target* order `(base, t, fibre)`, i.e. the last
base coordinate.  The coordinate permutation `facePerm` moves `faceIdx` (last) onto `facePermIdx`
(position `p`, directly after the base coordinates). -/
def facePermIdx (p m : ℕ) : Fin (faceK p m) := ⟨p, by simp only [faceK]; omega⟩

theorem facePermIdx_val (p m : ℕ) : (facePermIdx p m).val = p := rfl

theorem faceIdx_val (p m : ℕ) : (faceIdx p m).val = faceN p m := rfl

theorem facePermIdx_ne_faceIdx (p m : ℕ) : facePermIdx p m ≠ faceIdx p m := by
  intro h
  have := congrArg Fin.val h
  simp only [facePermIdx_val, faceIdx_val, faceN, faceK] at this
  omega

/-- `Z` zero-padded by the vertical coordinate (placed last). -/
noncomputable def faceZp {p m : ℕ} (Z : SemiPf (p + (m+1))) : SemiPf (faceK p m) :=
  SemiPf.pad (faceN_le_faceK p m) Z

/-- The single equation `t = 1` cutting the vertical coordinate. -/
def faceEq (p m r : ℕ) : EAPoly (faceK p m) r :=
  MvPolynomial.X (Sum.inl (faceIdx p m)) - 1

/-- The cut set: `Z` zero-padded, cut by `t = 1`. -/
noncomputable def faceY1 {p m : ℕ} (Z : SemiPf (p + (m+1))) : SemiPf (faceK p m) :=
  SemiPf.addConds (faceZp Z) [faceEq p m (faceZp Z).r] []

/-- The canonical point of the cut set: `u` zero-padded, with vertical coordinate `1`. -/
def facePoint {p m : ℕ} (u : Fin (p + (m+1)) → ℝ) : Fin (faceK p m) → ℝ :=
  fun i => if h : i.val < faceN p m then u ⟨i.val, h⟩ else 1

/-- The "base + vertical coordinate" projection of a padded point. -/
def faceExtract {p m : ℕ} (w : Fin (faceK p m) → ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc (projFirst p (m+1) (takeZ (faceN_le_faceK p m) w)) (w (faceIdx p m))

/-! ## The point set of `faceY1` -/

theorem eaEval_faceEq {p m r : ℕ} (c : EAChain (faceK p m) r) (w : Fin (faceK p m) → ℝ) :
    eaEval c (faceEq p m r) w = w (faceIdx p m) - 1 := by
  simp [faceEq, eaEval]

/-- **Membership in `faceY1`.** -/
theorem mem_faceY1 {p m : ℕ} (Z : SemiPf (p + (m+1))) {w : Fin (faceK p m) → ℝ} :
    w ∈ (faceY1 Z).set ↔
      takeZ (faceN_le_faceK p m) w ∈ Z.set ∧ w (faceIdx p m) = 1 := by
  constructor
  · intro hw
    rw [faceY1, SemiPf.addConds_set] at hw
    obtain ⟨⟨hX, he⟩, _⟩ := hw
    rw [faceZp, Work.WilE7.SemiPf.pad_set] at hX
    obtain ⟨_, hZ⟩ := hX
    refine ⟨hZ, ?_⟩
    have h1 := he (faceEq p m (faceZp Z).r) (by simp)
    rw [eaEval_faceEq, sub_eq_zero] at h1
    exact h1
  · rintro ⟨hZ, he⟩
    rw [faceY1, SemiPf.addConds_set, faceZp, Work.WilE7.SemiPf.pad_set]
    refine ⟨⟨⟨?_, hZ⟩, ?_⟩, ?_⟩
    · intro i
      by_cases h : (i : ℕ) < faceN p m
      · have hle := hZ.1 ⟨(i : ℕ), h⟩
        have heq : takeZ (faceN_le_faceK p m) w ⟨(i : ℕ), h⟩ = w i :=
          congrArg w (Fin.ext rfl)
        rwa [heq] at hle
      · have hi : i = faceIdx p m := by
          apply Fin.ext
          simp only [faceIdx, faceN, faceK] at h ⊢
          omega
        rw [hi, he]
        norm_num
    · intro f hf
      rw [List.mem_singleton] at hf
      subst hf
      rw [eaEval_faceEq, sub_eq_zero]
      exact he
    · intro g hg
      exact absurd hg List.not_mem_nil

/-- **Set of `faceY1`.** -/
theorem faceY1_set {p m : ℕ} (Z : SemiPf (p + (m+1))) :
    (faceY1 Z).set = {w : Fin (faceK p m) → ℝ |
      takeZ (faceN_le_faceK p m) w ∈ Z.set ∧ w (faceIdx p m) = 1} :=
  Set.ext fun _ => mem_faceY1 Z

/-! ## The canonical point -/

theorem facePoint_idx {p m : ℕ} (u : Fin (p + (m+1)) → ℝ) :
    facePoint u (faceIdx p m) = 1 := by
  show (if h : (faceIdx p m).val < faceN p m then u ⟨(faceIdx p m).val, h⟩ else 1) = 1
  rw [dif_neg (by simp only [faceIdx]; omega)]

theorem takeZ_facePoint {p m : ℕ} (u : Fin (p + (m+1)) → ℝ) :
    takeZ (faceN_le_faceK p m) (facePoint u) = u := by
  funext i
  show (if h : (i : ℕ) < faceN p m then u ⟨(i : ℕ), h⟩ else 1) = u i
  rw [dif_pos (by simp only [faceN]; exact i.isLt)]

theorem facePoint_mem {p m : ℕ} (Z : SemiPf (p + (m+1))) {u : Fin (p + (m+1)) → ℝ}
    (hu : u ∈ Z.set) : facePoint u ∈ (faceY1 Z).set := by
  rw [mem_faceY1]
  exact ⟨by rw [takeZ_facePoint]; exact hu, facePoint_idx u⟩

theorem takeZ_mem_of_mem_faceY1 {p m : ℕ} (Z : SemiPf (p + (m+1)))
    {w : Fin (faceK p m) → ℝ} (hw : w ∈ (faceY1 Z).set) :
    takeZ (faceN_le_faceK p m) w ∈ Z.set :=
  (mem_faceY1 Z).mp hw |>.1

theorem facePoint_takeZ_self {p m : ℕ} (Z : SemiPf (p + (m+1)))
    {w : Fin (faceK p m) → ℝ} (hw : w ∈ (faceY1 Z).set) :
    facePoint (takeZ (faceN_le_faceK p m) w) = w := by
  have ht : w (faceIdx p m) = 1 := (mem_faceY1 Z).mp hw |>.2
  funext i
  show (if h : (i : ℕ) < faceN p m then
      takeZ (faceN_le_faceK p m) w ⟨(i : ℕ), h⟩ else 1) = w i
  by_cases h : (i : ℕ) < faceN p m
  · rw [dif_pos h]
    show w (Fin.castLE (faceN_le_faceK p m) ⟨(i : ℕ), h⟩) = w i
    exact congrArg w (Fin.ext rfl)
  · rw [dif_neg h]
    have hi : i = faceIdx p m := by
      apply Fin.ext
      simp only [faceIdx, faceN, faceK] at h ⊢
      omega
    rw [hi, ht]

theorem facePoint_injective {p m : ℕ} :
    Function.Injective (facePoint (p := p) (m := m)) := by
  intro u v huv
  have := congrArg (takeZ (faceN_le_faceK p m)) huv
  rwa [takeZ_facePoint, takeZ_facePoint] at this

/-! ## The extraction map on the canonical points -/

theorem faceExtract_facePoint {p m : ℕ} (u : Fin (p + (m+1)) → ℝ) :
    faceExtract (facePoint u) = Fin.snoc (projFirst p (m+1) u) 1 := by
  rw [faceExtract, takeZ_facePoint, facePoint_idx]

end Work.WilE7.FaceAux
