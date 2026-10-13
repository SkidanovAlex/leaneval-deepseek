/-
  WilG4c — vocabulary for `Work.WilG4c.CellParamMain` (BNZ §2.2, cell parametrisation).

  Fix `p` (the parameter dimension) and `N` (the fibre dimension), and a cell `κ ⊆ ℝ^{p+N}`.
  The *levels* of `κ` are its projections to the first `p+m` coordinates

      `lvl p N κ m = {x : ℝ^{p+m} | ∃ w : ℝ^{N-m}, (x,w) ∈ κ}`   (`m = 0, …, N`),

  defined here by a downward recursion on `m` from `κ` itself (so that the base of the cylinder
  at level `m+1` is the level-`m` set, definitionally).  `gluePt` is the corresponding point
  constructor: it glues `x : ℝ^{p+m}` and `w : ℝ^{N-m}` into a point of `ℝ^{p+N}`.

  The tower `towerPt` parametrises the fibre of `κ` over a parameter `l` by the open cube:
  given the fibre-end functions `L m, H m` of level `m+1` (functions of the level-`m` point),
  it produces successively

      `towerPt 0 l t = l`,
      `towerPt (m+1) l t = Fin.snoc (towerPt m l t) (L m (towerPt m l t)
                            + t m * (H m (towerPt m l t) - L m (towerPt m l t)))`.

  The coordinate functions of `towerPt` are the `Ψ` of `CellParamMain`.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.YbddAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The gluing of a level-`m` point with the remaining coordinates -/

/-- The point of `ℝ^{p+N}` whose first `p+m` coordinates are `x` and whose last `N-m`
coordinates are `w`.  (Defined by an `if` on the index value, so that no arithmetic
identification of `Fin` types is needed.) -/
def gluePt (p N m : ℕ) (hm : m ≤ N) (x : Fin (p+m) → ℝ) (w : Fin (N-m) → ℝ) :
    Fin (p+N) → ℝ :=
  fun i => if h : i.val < p+m then x ⟨i.val, h⟩
           else w ⟨i.val - (p+m), by omega⟩

/-- The index of `ℝ^{p+N}` corresponding to a coordinate of `ℝ^{p+m}` (`m ≤ N`). -/
def idxL (p N m : ℕ) (hm : m ≤ N) (i : Fin (p+m)) : Fin (p+N) :=
  ⟨i.val, by omega⟩

/-- The indices of `ℝ^{p+N}` corresponding to the trailing `N-m` coordinates. -/
def idxR (p N m : ℕ) (hm : m ≤ N) (j : Fin (N-m)) : Fin (p+N) :=
  ⟨p+m + j.val, by omega⟩

@[simp] theorem gluePt_idxL (p N m : ℕ) (hm : m ≤ N) (x : Fin (p+m) → ℝ)
    (w : Fin (N-m) → ℝ) (i : Fin (p+m)) :
    gluePt p N m hm x w (idxL p N m hm i) = x i := by
  unfold gluePt idxL
  rw [dif_pos i.isLt]

@[simp] theorem gluePt_idxR (p N m : ℕ) (hm : m ≤ N) (x : Fin (p+m) → ℝ)
    (w : Fin (N-m) → ℝ) (j : Fin (N-m)) :
    gluePt p N m hm x w (idxR p N m hm j) = w j := by
  unfold gluePt idxR
  have h : ¬ ((p+m + j.val) < p+m) := by omega
  rw [dif_neg h]
  exact congrArg w (Fin.ext (by simp only [Fin.val_mk]; omega))

/-- At the top level, `gluePt` does not change the point. -/
theorem gluePt_self (p N : ℕ) (x : Fin (p+N) → ℝ) (w : Fin (N-N) → ℝ) :
    gluePt p N N (le_refl N) x w = x := by
  funext i
  unfold gluePt
  rw [dif_pos i.isLt]

/-! ## 2. The levels of `κ`

`lvl p N κ m` is the projection of `κ` to the first `p+m` coordinates; for `m ≥ N` it is the
"first `p+m` coordinates of `κ`" set, which for `m = N` is `κ` itself. -/

/-- The `m`-th level of `κ`: its projection to the first `p+m` coordinates. -/
def lvl (p N : ℕ) (κ : Set (Fin (p+N) → ℝ)) : (m : ℕ) → Set (Fin (p+m) → ℝ)
  | m => if h : m < N then projLast (lvl p N κ (m + 1))
         else {x | ∃ z : Fin (p+N) → ℝ, z ∈ κ ∧
                ∀ (i : Fin (p+m)) (h : i.val < p+N), x i = z ⟨i.val, h⟩}
termination_by m => N - m
decreasing_by omega

/-- The defining equation of `lvl` below the top level. -/
theorem lvl_succ {p N : ℕ} (κ : Set (Fin (p+N) → ℝ)) {m : ℕ} (h : m < N) :
    lvl p N κ m = projLast (lvl p N κ (m+1)) := by
  rw [lvl]
  simp only [dif_pos h]

/-- The top level is `κ` itself. -/
theorem lvl_self {p N : ℕ} (κ : Set (Fin (p+N) → ℝ)) : lvl p N κ N = κ := by
  rw [lvl]
  rw [dif_neg (lt_irrefl N)]
  ext x
  constructor
  · rintro ⟨z, hz, hxz⟩
    have hzx : z = x := by
      funext i
      have h := hxz i i.isLt
      rw [show (⟨i.val, i.isLt⟩ : Fin (p+N)) = i from Fin.ext rfl] at h
      exact h.symm
    rwa [← hzx]
  · intro hx
    exact ⟨x, hx, fun i h => by
      rw [show (⟨i.val, h⟩ : Fin (p+N)) = i from Fin.ext rfl]⟩

/-! ## 3. Prefixes of a point of `ℝ^{p+N}` -/

/-- The first `p+m` coordinates of `z`, as a point of `ℝ^{p+m}` (`m ≤ N`). -/
def prefl {p N : ℕ} (m : ℕ) (hm : m ≤ N) (z : Fin (p+N) → ℝ) : Fin (p+m) → ℝ :=
  fun i => z ⟨i.val, by omega⟩

theorem prefl_apply {p N : ℕ} (m : ℕ) (hm : m ≤ N) (z : Fin (p+N) → ℝ) (i : Fin (p+m)) :
    prefl m hm z i = z ⟨i.val, by omega⟩ := rfl

theorem prefl_self {p N : ℕ} (z : Fin (p+N) → ℝ) : prefl N (le_refl N) z = z := by
  funext i
  exact congrArg z (Fin.ext rfl)

/-- The level-`m` prefix is the `Fin.init` of the level-`m+1` prefix. -/
theorem prefl_init {p N : ℕ} (m : ℕ) (hm : m+1 ≤ N) (z : Fin (p+N) → ℝ) :
    Fin.init (prefl (m+1) hm z) = prefl m (by omega) z := by
  funext i
  exact congrArg z (Fin.ext rfl)

/-- The level-`m+1` prefix, extended by the next coordinate. -/
theorem prefl_succ {p N : ℕ} (m : ℕ) (hm : m+1 ≤ N) (z : Fin (p+N) → ℝ) :
    prefl (m+1) hm z = Fin.snoc (prefl m (by omega) z) (z ⟨p+m, by omega⟩) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    exact congrArg z (Fin.ext rfl)
  · intro j
    rw [Fin.snoc_castSucc]
    exact congrArg z (Fin.ext rfl)

/-! ## 4. The tower -/

/-- The new coordinate at level `m+1`: the interpolation of the level-`m` fibre ends with the
`m`-th coordinate of `t`.  Junk (`0`) for `m ≥ N`. -/
def tval (p N : ℕ) (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ)
    (m : ℕ) (x : Fin (p+m) → ℝ) (t : Fin N → ℝ) : ℝ :=
  if h : m < N then L ⟨m, h⟩ x + t ⟨m, h⟩ * (H ⟨m, h⟩ x - L ⟨m, h⟩ x) else 0

theorem tval_eq {p N : ℕ} {L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ} {m : ℕ} (h : m < N)
    (x : Fin (p+m) → ℝ) (t : Fin N → ℝ) :
    tval p N L H m x t = L ⟨m, h⟩ x + t ⟨m, h⟩ * (H ⟨m, h⟩ x - L ⟨m, h⟩ x) := by
  unfold tval
  simp only [dif_pos h]

/-- The tower of partial parametrisations of the fibre. -/
def towerPt (p N : ℕ) (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) :
    (m : ℕ) → (Fin p → ℝ) → (Fin N → ℝ) → (Fin (p+m) → ℝ) :=
  fun m => Nat.rec (fun l _ => l)
    (fun m ih => fun l t => Fin.snoc (ih l t) (tval p N L H m (ih l t) t)) m

@[simp] theorem towerPt_zero {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ)
    (l : Fin p → ℝ) (t : Fin N → ℝ) :
    towerPt p N L H 0 l t = l := rfl

theorem towerPt_succ {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ)
    (l : Fin p → ℝ) (t : Fin N → ℝ) :
    towerPt p N L H (m+1) l t =
      Fin.snoc (towerPt p N L H m l t) (tval p N L H m (towerPt p N L H m l t) t) := rfl

/-- The last coordinate of the level-`m+1` tower point. -/
theorem towerPt_last {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ)
    (l : Fin p → ℝ) (t : Fin N → ℝ) :
    towerPt p N L H (m+1) l t (Fin.last (p+m)) = tval p N L H m (towerPt p N L H m l t) t := by
  rw [towerPt_succ]
  exact Fin.snoc_last _ _

/-- The first `p+m` coordinates of the level-`m+1` tower point are those of the level-`m` one. -/
theorem towerPt_init {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ)
    (l : Fin p → ℝ) (t : Fin N → ℝ) :
    Fin.init (towerPt p N L H (m+1) l t) = towerPt p N L H m l t := by
  rw [towerPt_succ]
  exact Fin.init_snoc _ _

/-- The tower point does not depend on the coordinates of `t` beyond the first `m`. -/
theorem towerPt_congr {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) :
    ∀ m (l : Fin p → ℝ) (t t' : Fin N → ℝ), (∀ i : Fin N, i.val < m → t i = t' i) →
      towerPt p N L H m l t = towerPt p N L H m l t' := by
  intro m
  induction m with
  | zero => intro l t t' _; rfl
  | succ m ih =>
      intro l t t' h
      rw [towerPt_succ, towerPt_succ]
      have h1 : towerPt p N L H m l t = towerPt p N L H m l t' :=
        ih l t t' (fun i hi => h i (by omega))
      rw [h1]
      congr 1
      rw [tval, tval]
      by_cases hm : m < N
      · rw [dif_pos hm, dif_pos hm, h ⟨m, hm⟩ (Nat.lt_succ_self m)]
      · rw [dif_neg hm, dif_neg hm]

/-- The tower point, read as a function of the flattened parameter `z ∈ ℝ^{p+N}`. -/
def ptFlat (p N : ℕ) (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ) :
    (Fin (p+N) → ℝ) → (Fin (p+m) → ℝ) :=
  fun z => towerPt p N L H m (fun i => z (Fin.castAdd N i)) (fun i => z (Fin.natAdd p i))

theorem ptFlat_zero {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ)
    (z : Fin (p+N) → ℝ) :
    ptFlat p N L H 0 z = (fun i : Fin (p+0) => z (Fin.castAdd N i)) := rfl

theorem ptFlat_succ {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ)
    (z : Fin (p+N) → ℝ) :
    ptFlat p N L H (m+1) z =
      Fin.snoc (ptFlat p N L H m z)
        (tval p N L H m (ptFlat p N L H m z) (fun i => z (Fin.natAdd p i))) := rfl

/-- The last coordinate of `ptFlat (m+1)`. -/
theorem ptFlat_last {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ)
    (z : Fin (p+N) → ℝ) :
    ptFlat p N L H (m+1) z (Fin.last (p+m)) =
      tval p N L H m (ptFlat p N L H m z) (fun i => z (Fin.natAdd p i)) := by
  rw [ptFlat_succ]
  exact Fin.snoc_last _ _

/-- The first `p+m` coordinates of `ptFlat (m+1)`. -/
theorem ptFlat_init {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) (m : ℕ)
    (z : Fin (p+N) → ℝ) :
    Fin.init (ptFlat p N L H (m+1) z) = ptFlat p N L H m z := by
  rw [ptFlat_succ]
  exact Fin.init_snoc _ _

end Work.WilG4c
