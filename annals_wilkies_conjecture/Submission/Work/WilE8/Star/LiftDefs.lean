/-
  WilE8 / Star — vocabulary for the left-lift of a `Star`-set.

  `Star F D n Z` is a finite union of `StarPiece n`, i.e. of projections of connected
  components of semi-Pfaffian sets.  `lift_left_cube` says that the cylinder over a
  `Star`-set, cut down by the cube, is again a `Star`-set of format `F+1` and the same
  degree.

  The cylinder is taken over the coordinates `1, …, n` (the target uses `Fin.tail`), so the
  new coordinate sits at position `0`.  The two operations that this requires are

  * `tailM n m`  : drop the first coordinate, `Fin ((n+1)+m) → Fin (n+m)`;
  * `consV n m t w` : insert the value `t` at position `0`, the remaining coordinates being
    those of `w`.

  (These are the `Fin.tail`/`Fin.cons` operations, written with the *additive* index
  arithmetic `(n+1)+m` that the `StarPiece` fields force; `Fin.tail`/`Fin.cons` themselves
  are stated for `k+1`, and `(n+m)+1` is not the same numeral expression as `(n+1)+m`.)
-/
import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Extend

set_option autoImplicit false
noncomputable section
namespace Work.WilE8.Star

open WilkiesDesign

/-- Drop the first coordinate: `Fin ((n+1)+m) → ℝ` to `Fin (n+m) → ℝ`. -/
def tailM (n m : ℕ) (x : Fin ((n + 1) + m) → ℝ) : Fin (n + m) → ℝ :=
  fun i => x ⟨i.val + 1, by omega⟩

/-- Insert the value `t` at coordinate `0`, the other coordinates being those of `w`. -/
def consV (n m : ℕ) (t : ℝ) (w : Fin (n + m) → ℝ) : Fin ((n + 1) + m) → ℝ :=
  fun i => if h : (i : ℕ) = 0 then t else w ⟨i.val - 1, by omega⟩

/-- `consV` with value `0`, the base point of the cylinder over `w`. -/
def liftPt (n m : ℕ) (w : Fin (n + m) → ℝ) : Fin ((n + 1) + m) → ℝ := consV n m 0 w

lemma tailM_apply (n m : ℕ) (x : Fin ((n + 1) + m) → ℝ) (i : Fin (n + m)) :
    tailM n m x i = x ⟨i.val + 1, by omega⟩ := rfl

@[simp] lemma consV_zero (n m : ℕ) (t : ℝ) (w : Fin (n + m) → ℝ) :
    consV n m t w 0 = t := by
  simp only [consV]
  rw [dif_pos (show (((0 : Fin ((n + 1) + m)) : ℕ)) = 0 from rfl)]

@[simp] lemma consV_succ (n m : ℕ) (t : ℝ) (w : Fin (n + m) → ℝ) (i : Fin (n + m)) :
    consV n m t w ⟨i.val + 1, by omega⟩ = w i := by
  simp only [consV]
  rw [dif_neg (show ¬ (((⟨i.val + 1, by omega⟩ : Fin ((n + 1) + m)) : ℕ)) = 0 by simp)]
  congr 1

@[simp] lemma tailM_consV (n m : ℕ) (t : ℝ) (w : Fin (n + m) → ℝ) :
    tailM n m (consV n m t w) = w := by
  funext i
  rw [tailM_apply]
  exact consV_succ n m t w i

@[simp] lemma tailM_liftPt (n m : ℕ) (w : Fin (n + m) → ℝ) :
    tailM n m (liftPt n m w) = w := by
  simp only [liftPt]
  exact tailM_consV n m 0 w

lemma consV_tailM (n m : ℕ) (x : Fin ((n + 1) + m) → ℝ) :
    consV n m (x 0) (tailM n m x) = x := by
  funext i
  by_cases h : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by simpa using h)
    subst hi
    simp only [consV_zero]
  · have hcoe : consV n m (x 0) (tailM n m x) i
        = tailM n m x ⟨i.val - 1, by omega⟩ := by
      simp only [consV]
      rw [dif_neg h]
    rw [hcoe, tailM_apply]
    exact congrArg x (Fin.ext (Nat.sub_add_cancel (by omega)))

lemma consV_mem_cubeC (n m : ℕ) (t : ℝ) (w : Fin (n + m) → ℝ) :
    consV n m t w ∈ WilkiesDesign.E.cubeC ((n + 1) + m) ↔
      t ∈ Set.Icc (-1 : ℝ) 1 ∧ w ∈ WilkiesDesign.E.cubeC (n + m) := by
  constructor
  · intro h
    refine ⟨abs_le.mp ?_, fun i => ?_⟩
    · simpa using h 0
    · simpa using h ⟨i.val + 1, by omega⟩
  · rintro ⟨ht, hw⟩ i
    by_cases h : (i : ℕ) = 0
    · have hi : i = 0 := Fin.ext (by simpa using h)
      subst hi
      simpa using (abs_le.mpr ht)
    · have hcoe : consV n m t w i = w ⟨i.val - 1, by omega⟩ := by
        simp only [consV]
        rw [dif_neg h]
      rw [hcoe]
      simpa using hw ⟨i.val - 1, by omega⟩

lemma liftPt_mem_cubeC {n m : ℕ} {w : Fin (n + m) → ℝ}
    (hw : w ∈ WilkiesDesign.E.cubeC (n + m)) :
    liftPt n m w ∈ WilkiesDesign.E.cubeC ((n + 1) + m) := by
  rw [liftPt, consV_mem_cubeC]
  exact ⟨⟨by norm_num, by norm_num⟩, hw⟩

theorem continuous_tailM (n m : ℕ) : Continuous (tailM n m) :=
  continuous_pi fun i => continuous_apply _

theorem continuous_consV (n m : ℕ) (w : Fin (n + m) → ℝ) :
    Continuous (fun t : ℝ => consV n m t w) := by
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext (by simpa using h)
    subst hi
    have hfun : (fun t : ℝ => consV n m t w 0) = id := by
      funext t
      exact consV_zero n m t w
    rw [hfun]
    exact continuous_id
  · have hcoe : (fun t : ℝ => consV n m t w i) = fun _ => w ⟨i.val - 1, by omega⟩ := by
      funext t
      simp only [consV]
      rw [dif_neg h]
    rw [hcoe]
    exact continuous_const

/-- The projection of `consV t w` is `Fin.cons t (projFirst n m w)`. -/
theorem projFirst_consV (n m : ℕ) (t : ℝ) (w : Fin (n + m) → ℝ) :
    WilkiesDesign.E.projFirst (n + 1) m (consV n m t w) =
      Fin.cons t (WilkiesDesign.E.projFirst n m w) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [WilkiesDesign.E.projFirst]
    rw [show Fin.castAdd m (0 : Fin (n + 1)) = (0 : Fin ((n + 1) + m)) from Fin.ext (by simp)]
    rw [consV_zero, Fin.cons_zero]
  · intro j
    simp only [WilkiesDesign.E.projFirst]
    rw [show Fin.castAdd m (Fin.succ j) = (⟨(Fin.castAdd m j).val + 1, by omega⟩ :
      Fin ((n + 1) + m)) from Fin.ext (by simp)]
    rw [consV_succ, Fin.cons_succ]
    rfl

/-- The bridge between the target's `Fin.tail` and `tailM`. -/
theorem tail_projFirst (n m : ℕ) (x : Fin ((n + 1) + m) → ℝ) :
    Fin.tail (WilkiesDesign.E.projFirst (n + 1) m x) =
      WilkiesDesign.E.projFirst n m (tailM n m x) := by
  funext i
  show x (Fin.castAdd m (Fin.succ i)) = x ⟨(Fin.castAdd m i).val + 1, by omega⟩
  exact congrArg x (Fin.ext (by simp))

/-- The injection `Fin (n+m) → Fin ((n+1)+m)` that skips coordinate `0`. -/
theorem comp_shiftInj (n m : ℕ) (x : Fin ((n + 1) + m) → ℝ) :
    (fun i : Fin (n + m) => x (Work.WilE8.shiftInj n m i)) = tailM n m x := by
  funext i
  show x (Work.WilE8.shiftInj n m i) = x ⟨i.val + 1, by omega⟩
  exact congrArg x (Fin.ext (by simp [Work.WilE8.shiftInj]))

theorem shiftInj_injective (n m : ℕ) : Function.Injective (Work.WilE8.shiftInj n m) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [Work.WilE8.shiftInj] at h'
  exact Fin.ext (by omega)

/-- The left lift of a `*`-piece: the semi-Pfaffian data is extended along `shiftInj`,
which inserts the new coordinate at position `0`. -/
def liftPiece {n : ℕ} (P : WilkiesDesign.E.StarPiece n) : WilkiesDesign.E.StarPiece (n + 1) :=
  ⟨P.m, Work.WilE8.SemiPf.extend (Work.WilE8.shiftInj n P.m) P.X, liftPt n P.m P.p⟩

end Work.WilE8.Star
