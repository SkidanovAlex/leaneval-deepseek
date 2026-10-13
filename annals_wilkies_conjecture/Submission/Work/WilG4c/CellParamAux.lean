/-
  WilG4c — `Work.WilG4c.CellParamMain` (BNZ §2.2, cell parametrisation).

  Given a cell `κ` of a cylindrical decomposition of `ℝ^{p+N}` lying in the open cube in its
  `N` fibre coordinates, we parametrise the fibre of `κ` over a set `Λ` of parameters by the
  open cube `I^N`, with `Ω`-bounded coordinate graphs of a format independent of `D` and a
  degree polynomial in `D`.

  The construction is the tower of `CellParamDefs`: at level `m+1` the new coordinate
  interpolates between the fibre ends `L m`, `H m` of the level-`m+1` projection
  `lvl p N κ (m+1)` of `κ`, which are `Ω`-definable by `Work.WilG4c.StepFiberEnds`.  The `Ω`
  bookkeeping is done level by level, using the composition and combination lemmas
  `Work.WilG4c.graphOfCompGen` and `Work.WilG4c.graphOfLinComb_mem`.
-/
/-
  WilG4c — bookkeeping for `Work.WilG4c.CellParamMain`: coordinates of the tower points
  (`towerPt`), the comparison of the tower with `Fin.append`, and the description of the levels
  `lvl p N κ m` as the images of the gluing maps `gluePt`.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.CellParamDefs
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.lvl_omega
import Submission.Work.WilG4c.lvl_isCell
import Submission.Work.WilG4c.append_eq_gluePt
import Submission.Work.WilG4c.cellFibre_param
import Submission.Work.WilG4c.graphOfLinComb_mem
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Main
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_surjective

/-! ## Bookkeeping for the tower and the target points -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-! ## 1. Tower bookkeeping -/

/-- Coordinate access on the tower: below the parameter block the tower point is `l`. -/
theorem towerPt_first {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ) :
    ∀ m (l : Fin p → ℝ) (t : Fin N → ℝ) (z : Fin (p+m)) (i : Fin p), z.val = i.val →
      towerPt p N L H m l t z = l i := by
  intro m
  induction m with
  | zero => intro l t z i hi; exact congrArg l (Fin.ext hi)
  | succ m ih =>
      intro l t z i hi
      rw [towerPt_succ]
      rw [show z = Fin.castSucc (z.castLT (by omega : z.val < p + m)) from Fin.ext rfl]
      rw [Fin.snoc_castSucc]
      exact ih l t (z.castLT (by omega)) i (by simpa using hi)

theorem towerPt_first_apply {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ)
    (m : ℕ) (l : Fin p → ℝ) (t : Fin N → ℝ) (z : Fin (p+m)) (hz : z.val < p) :
    towerPt p N L H m l t z = l ⟨z.val, hz⟩ :=
  towerPt_first L H m l t z ⟨z.val, hz⟩ rfl

/-- The top tower point is the parameter block glued with its own tail. -/
theorem towerPt_gluePt {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ)
    (l : Fin p → ℝ) (t : Fin N → ℝ) :
    towerPt p N L H N l t = gluePt p N 0 (Nat.zero_le N) l
      (fun j : Fin N => towerPt p N L H N l t (Fin.natAdd p j)) := by
  funext z
  unfold gluePt
  by_cases hz : z.val < p+0
  · rw [dif_pos hz]
    exact towerPt_first_apply L H N l t z (by omega)
  · rw [dif_neg hz]
    refine congrArg (towerPt p N L H N l t) ?_
    exact Fin.ext (by simp [Fin.natAdd]; omega)

/-- The top tower point is `Fin.append` of the parameter block and the tail. -/
theorem towerPt_append {p N : ℕ} (L H : (m : Fin N) → (Fin (p+m.val) → ℝ) → ℝ)
    (l : Fin p → ℝ) (t : Fin N → ℝ) :
    towerPt p N L H N l t =
      Fin.append l (fun j : Fin N => towerPt p N L H N l t (Fin.natAdd p j)) := by
  conv_lhs => rw [towerPt_gluePt]
  exact (append_eq_gluePt p N l (fun j : Fin N => towerPt p N L H N l t (Fin.natAdd p j))).symm

/-! ## 2. The target point at each level -/

/-- A variant of `Fin.snoc` with a constant codomain, so that no type family has to be
inferred. -/
def finSnoc {n : ℕ} (x : Fin n → ℝ) (v : ℝ) : Fin (n+1) → ℝ :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else v

theorem finSnoc_castSucc {n : ℕ} (x : Fin n → ℝ) (v : ℝ) (i : Fin n) :
    finSnoc x v i.castSucc = x i := by
  unfold finSnoc
  simp only [Fin.val_castSucc]
  rw [dif_pos i.isLt]

theorem finSnoc_last {n : ℕ} (x : Fin n → ℝ) (v : ℝ) :
    finSnoc x v (Fin.last n) = v := by
  unfold finSnoc
  rw [dif_neg (by simp)]

/-- `Fin.snoc` agrees with `finSnoc` (constant codomain). -/
theorem snoc_eq_finSnoc {n : ℕ} (x : Fin n → ℝ) (v : ℝ) :
    (Fin.snoc x v : Fin (n+1) → ℝ) = finSnoc x v := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last (α := fun _ => ℝ), finSnoc_last]
  · intro j
    rw [Fin.snoc_castSucc, finSnoc_castSucc]

/-- The level-`m` target: the parameter block `l` followed by the first `m` coordinates of `y`
(junk `0` beyond `N`). -/
def targ (p N : ℕ) : (m : ℕ) → (Fin p → ℝ) → (Fin N → ℝ) → (Fin (p+m) → ℝ)
  | 0, l, _ => l
  | m+1, l, y => (Fin.snoc (targ p N m l y) (if h : m < N then y ⟨m, h⟩ else 0) :
      Fin ((p+m)+1) → ℝ)

@[simp] theorem targ_zero {p N : ℕ} (l : Fin p → ℝ) (y : Fin N → ℝ) :
    targ p N 0 l y = l := rfl

theorem targ_succ' {p N : ℕ} (m : ℕ) (l : Fin p → ℝ) (y : Fin N → ℝ) :
    targ p N (m+1) l y = (Fin.snoc (targ p N m l y)
      (if h : m < N then y ⟨m, h⟩ else 0) : Fin ((p+m)+1) → ℝ) := rfl

theorem targ_succ {p N : ℕ} {m : ℕ} (h : m < N) (l : Fin p → ℝ) (y : Fin N → ℝ) :
    targ p N (m+1) l y = (Fin.snoc (targ p N m l y) (y ⟨m, h⟩) : Fin ((p+m)+1) → ℝ) := by
  rw [targ_succ']
  rw [dif_pos h]

theorem targ_first {p N : ℕ} (m : ℕ) (l : Fin p → ℝ) (y : Fin N → ℝ) (i : Fin p) :
    targ p N m l y (Fin.castAdd m i) = l i := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [targ_succ']
      rw [show Fin.castAdd (m+1) i = (Fin.castAdd m i).castSucc from Fin.ext rfl]
      rw [Fin.snoc_castSucc]
      exact ih

theorem targ_tail {p N : ℕ} (m : ℕ) (l : Fin p → ℝ) (y : Fin N → ℝ) (j : Fin m)
    (hj : j.val < N) : targ p N m l y (Fin.natAdd p j) = y ⟨j.val, hj⟩ := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
      rw [targ_succ']
      by_cases hlast : j.val = m
      · have hjlast : j = Fin.last m := Fin.ext hlast
        subst hjlast
        rw [show Fin.natAdd p (Fin.last m) = Fin.last (p+m) from Fin.ext rfl]
        rw [Fin.snoc_last (α := fun _ => ℝ)]
        have hmN : m < N := by simpa using hj
        rw [dif_pos hmN]
        exact congrArg y (Fin.ext rfl)
      · have hlt : j.val < m := by omega
        rw [show Fin.natAdd p j = (Fin.natAdd p (⟨j.val, hlt⟩ : Fin m)).castSucc
          from Fin.ext rfl]
        rw [Fin.snoc_castSucc]
        exact ih ⟨j.val, hlt⟩ hj

/-- The top target point is `Fin.append l y`. -/
theorem targ_append {p N : ℕ} (l : Fin p → ℝ) (y : Fin N → ℝ) :
    targ p N N l y = Fin.append l y := by
  rw [append_eq_gluePt]
  funext z
  unfold gluePt
  by_cases hz : z.val < p+0
  · rw [dif_pos hz]
    conv_lhs => rw [show z = Fin.castAdd N ⟨z.val, by omega⟩ from Fin.ext rfl]
    rw [targ_first]
  · rw [dif_neg hz]
    have hidx : z = Fin.natAdd p ⟨z.val - p, by omega⟩ :=
      Fin.ext (by simp only [Fin.natAdd]; omega)
    conv_lhs => rw [hidx]
    rw [targ_tail]
    try rfl

/-! ## 3. The levels of `κ` as the images of the gluing maps -/

end Work.WilG4c
