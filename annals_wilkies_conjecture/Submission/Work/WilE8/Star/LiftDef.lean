/-
  WilE8 / Star — the coordinate-insertion map `insCoord` used to lift `*`-pieces from `ℝⁿ` to
  `ℝⁿ⁺¹`.

  `Work.WilE8.skipInj n m : Fin (n+m) → Fin (n+1+m)` inserts the new coordinate at position `n`
  (it is the injection underlying `prod_right`).  `insCoord n m w t` is a *section* of the
  forgetting map `x ↦ x ∘ skipInj`: it inserts the real number `t` at position `n` into the
  tuple `w : Fin (n+m) → ℝ`, shifting the fibre coordinates up by one.

  The API below is what the lifting of `Star`-pieces needs:
  * `insCoord_skipInj` : `(insCoord n m w t) ∘ skipInj = w`;
  * `insCoord_self`    : `x = insCoord n m (x ∘ skipInj) (x (new coordinate))`, i.e.
                         `insCoord` is a right inverse of `x ↦ (x ∘ skipInj, x n)`;
  * `continuous_insCoord`;
  * `insCoord_cube` / `insCoord_cube_of_mem` : the closed cube.
-/
import Mathlib
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8.Star

open WilkiesDesign WilkiesDesign.E

/-- Insert `t` at position `n` of the tuple `w : Fin (n+m) → ℝ`, shifting the fibre
coordinates (`n, …, n+m-1`) up by one. -/
def insCoord (n m : ℕ) (w : Fin (n+m) → ℝ) (t : ℝ) : Fin (n + 1 + m) → ℝ :=
  Fin.append (Fin.snoc (fun i : Fin n => w (Fin.castAdd m i)) t)
    (fun j : Fin m => w (Fin.natAdd n j))

/-- `insCoord` at the new coordinate is `t`. -/
lemma insCoord_new (n m : ℕ) (w : Fin (n+m) → ℝ) (t : ℝ) :
    insCoord n m w t (Fin.castAdd m (Fin.last n)) = t := by
  simp [insCoord, Fin.append_left]

/-- The value of `skipInj` on the trailing (fibre) part, in terms of `Fin.natAdd`. -/
lemma skipInj_castAdd_castSucc {n m : ℕ} (i : Fin n) :
    Work.WilE8.skipInj n m (Fin.castAdd m i) = Fin.castAdd m (Fin.castSucc i) := by
  unfold Work.WilE8.skipInj
  rw [dite_eq_left (by simp)]
  apply Fin.ext
  simp

/-- The value of `skipInj` on the fibre coordinates, in terms of `Fin.natAdd`. -/
lemma skipInj_natAdd {n m : ℕ} (j : Fin m) :
    Work.WilE8.skipInj n m (Fin.natAdd n j) = Fin.natAdd (n+1) j := by
  unfold Work.WilE8.skipInj
  rw [dite_eq_right (by simp)]
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

lemma skipInj_val_lt {n m : ℕ} {k : Fin (n+m)} (h : (k:ℕ) < n) :
    (Work.WilE8.skipInj n m k : ℕ) = k := by
  unfold Work.WilE8.skipInj
  rw [dite_eq_left h]

lemma skipInj_val_ge {n m : ℕ} {k : Fin (n+m)} (h : n ≤ (k:ℕ)) :
    (Work.WilE8.skipInj n m k : ℕ) = k + 1 := by
  unfold Work.WilE8.skipInj
  rw [dite_eq_right (by omega)]

/-- `skipInj` is injective. -/
lemma skipInj_injective (n m : ℕ) : Function.Injective (Work.WilE8.skipInj n m) := by
  intro i j hij
  have hv : (Work.WilE8.skipInj n m i : ℕ) = (Work.WilE8.skipInj n m j : ℕ) := by rw [hij]
  rcases lt_or_ge (i:ℕ) n with hi | hi <;> rcases lt_or_ge (j:ℕ) n with hj | hj
  · rw [skipInj_val_lt hi, skipInj_val_lt hj] at hv
    exact Fin.ext hv
  · rw [skipInj_val_lt hi, skipInj_val_ge hj] at hv
    omega
  · rw [skipInj_val_ge hi, skipInj_val_lt hj] at hv
    omega
  · rw [skipInj_val_ge hi, skipInj_val_ge hj] at hv
    exact Fin.ext (by omega)

/-- `insCoord` is a section of `x ↦ x ∘ skipInj`. -/
lemma insCoord_skipInj (n m : ℕ) (w : Fin (n+m) → ℝ) (t : ℝ) (i : Fin (n+m)) :
    insCoord n m w t (Work.WilE8.skipInj n m i) = w i := by
  refine Fin.addCases (motive := fun i => insCoord n m w t (Work.WilE8.skipInj n m i) = w i)
    ?_ ?_ i
  · intro i₀
    rw [skipInj_castAdd_castSucc]
    simp [insCoord, Fin.append_left]
  · intro j
    rw [skipInj_natAdd]
    simp [insCoord, Fin.append_right]

/-- Every tuple is the insertion of its new coordinate into its `skipInj`-restriction. -/
lemma insCoord_self (n m : ℕ) (x : Fin (n + 1 + m) → ℝ) :
    insCoord n m (fun i => x (Work.WilE8.skipInj n m i))
        (x (Fin.castAdd m (Fin.last n))) = x := by
  funext k
  refine Fin.addCases (motive := fun k => insCoord n m (fun i => x (Work.WilE8.skipInj n m i))
      (x (Fin.castAdd m (Fin.last n))) k = x k) ?_ ?_ k
  · intro k'
    rw [insCoord, Fin.append_left]
    refine Fin.lastCases ?_ ?_ k'
    · simp [Fin.snoc_last]
    · intro i₀
      simp only [Fin.snoc_castSucc]
      rw [skipInj_castAdd_castSucc]
  · intro j
    simp [insCoord, Fin.append_right, skipInj_natAdd]

/-- Continuity of `insCoord` in `(w, t)`. -/
lemma continuous_insCoord (n m : ℕ) :
    Continuous fun p : (Fin (n+m) → ℝ) × ℝ => insCoord n m p.1 p.2 := by
  change Continuous fun p : (Fin (n+m) → ℝ) × ℝ =>
    (Fin.append (Fin.snoc (fun i : Fin n => p.1 (Fin.castAdd m i)) p.2)
      (fun j : Fin m => p.1 (Fin.natAdd n j)) : Fin (n + 1 + m) → ℝ)
  fun_prop

/-- `insCoord` lands in the closed cube as soon as `w` does and `|t| ≤ 1`. -/
lemma insCoord_cube (n m : ℕ) {w : Fin (n+m) → ℝ} {t : ℝ}
    (hw : w ∈ WilkiesDesign.E.cubeC (n+m)) (ht : |t| ≤ 1) :
    insCoord n m w t ∈ WilkiesDesign.E.cubeC (n + 1 + m) := by
  intro k
  refine Fin.addCases (motive := fun k => |insCoord n m w t k| ≤ 1) ?_ ?_ k
  · intro k'
    rw [insCoord, Fin.append_left]
    refine Fin.lastCases ?_ ?_ k'
    · simpa [Fin.snoc_last] using ht
    · intro i₀
      simp only [Fin.snoc_castSucc]
      exact hw _
  · intro j
    rw [insCoord, Fin.append_right]
    exact hw _

/-- Conversely, a cube-membership of `insCoord n m w t` forces `w` in the cube (and `|t| ≤ 1`). -/
lemma insCoord_cube_of_mem (n m : ℕ) {w : Fin (n+m) → ℝ} {t : ℝ}
    (h : insCoord n m w t ∈ WilkiesDesign.E.cubeC (n + 1 + m)) :
    w ∈ WilkiesDesign.E.cubeC (n+m) ∧ |t| ≤ 1 := by
  constructor
  · intro x
    refine Fin.addCases (motive := fun x => |w x| ≤ 1) ?_ ?_ x
    · intro i₀
      have := h (Fin.castAdd m (Fin.castSucc i₀))
      rw [insCoord, Fin.append_left, Fin.snoc_castSucc] at this
      exact this
    · intro j
      have := h (Fin.natAdd (n+1) j)
      rw [insCoord, Fin.append_right] at this
      exact this
  · have := h (Fin.castAdd m (Fin.last n))
    rwa [insCoord, Fin.append_left, Fin.snoc_last] at this

end Work.WilE8.Star
