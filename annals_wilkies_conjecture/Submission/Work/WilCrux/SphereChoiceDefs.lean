/-
  WilCrux/SphereChoiceDefs — index vocabulary for node N4c3 (`SphereChoice`).

  A point of `ℝ^{(a+1)+b}` in the sphere-choice problem carries a parameter block
  `w : ℝ^a` (the first `a` coordinates), a radius `τ : ℝ` (coordinate `a`) and a fibre block
  `z : ℝ^b` (the last `b` coordinates).  This file fixes the three projections

  * `blockW x` — the first `a` coordinates,
  * `blockT x` — the coordinate `a` (the radius),
  * `blockZ x` — the last `b` coordinates,

  together with the two coordinate maps that realise the *inclusions*

  * `tauSkip a b : Fin (a+b) → Fin ((a+1)+b)`, `i ↦ i` for `i < a` and `i ↦ i+1` otherwise
    (so that `Fin.append (blockW x) (blockZ x) = x ∘ tauSkip a b`), and
  * `tauZMap a b : Fin (b+1) → Fin ((a+1)+b)` sending `0 ↦ a` and `k+1 ↦ a+1+k`
    (so that `Fin.tail (x ∘ tauZMap a b) = blockZ x` and `(x ∘ tauZMap a b) 0 = blockT x`).

  The choice set itself is `sphereSet E`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 1. The `τ`-skipping injection `Fin (a+b) → Fin ((a+1)+b)` -/

/-- The injection `Fin (a+b) → Fin ((a+1)+b)` that skips the radius coordinate `a`. -/
def tauSkip (a b : ℕ) : Fin (a + b) → Fin ((a + 1) + b) :=
  fun i => if h : (i : ℕ) < a then ⟨i, by omega⟩
    else ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩

@[simp] theorem tauSkip_castAdd {a b : ℕ} (i : Fin a) :
    tauSkip a b (Fin.castAdd b i) = Fin.castAdd b (Fin.castSucc i) := by
  rw [tauSkip]
  simp only [Fin.val_castAdd]
  rw [dite_eq_left i.isLt]
  rfl

@[simp] theorem tauSkip_natAdd {a b : ℕ} (i : Fin b) :
    tauSkip a b (Fin.natAdd a i) = Fin.natAdd (a + 1) i := by
  rw [tauSkip]
  simp only [Fin.val_natAdd]
  rw [dite_eq_right (by have := i.isLt; omega)]
  exact Fin.ext (by simp only [Fin.val_natAdd]; omega)

/-! ## 2. The two coordinate maps `Fin (b+1) → Fin ((a+1)+b)` -/

/-- `0 ↦ a` (the radius coordinate) and `k+1 ↦ a+1+k` (the fibre coordinates). -/
def tauZMap (a b : ℕ) : Fin (b + 1) → Fin ((a + 1) + b) :=
  Fin.cases (Fin.castAdd b (Fin.last a)) (fun k => Fin.natAdd (a + 1) k)

@[simp] theorem tauZMap_zero (a b : ℕ) : tauZMap a b 0 = Fin.castAdd b (Fin.last a) := by
  rw [tauZMap, Fin.cases_zero]

@[simp] theorem tauZMap_succ (a b : ℕ) (k : Fin b) :
    tauZMap a b (Fin.succ k) = Fin.natAdd (a + 1) k := by
  rw [tauZMap, Fin.cases_succ]

/-! ## 3. The three projections of `ℝ^{(a+1)+b}` -/

/-- The parameter block `w` of a point of `ℝ^{(a+1)+b}`. -/
def blockW {a b : ℕ} (x : Fin ((a + 1) + b) → ℝ) : Fin a → ℝ :=
  fun i => x (Fin.castAdd b (Fin.castSucc i))

/-- The radius coordinate `τ` of a point of `ℝ^{(a+1)+b}`. -/
def blockT {a b : ℕ} (x : Fin ((a + 1) + b) → ℝ) : ℝ :=
  x (Fin.castAdd b (Fin.last a))

/-- The fibre block `z` of a point of `ℝ^{(a+1)+b}`. -/
def blockZ {a b : ℕ} (x : Fin ((a + 1) + b) → ℝ) : Fin b → ℝ :=
  fun k => x (Fin.natAdd (a + 1) k)

/-! ## 4. The index identities -/

/-- Forgetting the radius coordinate is `tauSkip`. -/
theorem comp_tauSkip {a b : ℕ} (x : Fin ((a + 1) + b) → ℝ) :
    x ∘ tauSkip a b = Fin.append (blockW x) (blockZ x) := by
  funext i
  refine Fin.addCases (m := a) (n := b)
    (motive := fun i => x (tauSkip a b i) = Fin.append (blockW x) (blockZ x) i) ?_ ?_ i
  · intro i
    rw [tauSkip_castAdd, Fin.append_left]
    rfl
  · intro i
    rw [tauSkip_natAdd, Fin.append_right]
    rfl

/-- The fibre block of `x ∘ tauZMap` is the fibre block of `x`. -/
theorem tail_tauZMap {a b : ℕ} (x : Fin ((a + 1) + b) → ℝ) :
    Fin.tail (x ∘ tauZMap a b) = blockZ x := by
  funext k
  show x (tauZMap a b (Fin.succ k)) = blockZ x k
  rw [tauZMap_succ]
  rfl

/-- The zeroth coordinate of `x ∘ tauZMap` is the radius coordinate of `x`. -/
theorem zero_tauZMap {a b : ℕ} (x : Fin ((a + 1) + b) → ℝ) :
    (x ∘ tauZMap a b) 0 = blockT x := by
  show x (tauZMap a b 0) = blockT x
  rw [tauZMap_zero]
  rfl

/-! ## 5. The block projections of an appended point -/

theorem blockW_append {a b : ℕ} (w : Fin a → ℝ) (τ : ℝ) (z : Fin b → ℝ) :
    blockW (Fin.append (Fin.snoc w τ) z) = w := by
  funext i
  show Fin.append (Fin.snoc w τ) z (Fin.castAdd b (Fin.castSucc i)) = w i
  rw [Fin.append_left, Fin.snoc_castSucc]

theorem blockT_append {a b : ℕ} (w : Fin a → ℝ) (τ : ℝ) (z : Fin b → ℝ) :
    blockT (Fin.append (Fin.snoc w τ) z) = τ := by
  show Fin.append (Fin.snoc w τ) z (Fin.castAdd b (Fin.last a)) = τ
  rw [Fin.append_left, Fin.snoc_last]

theorem blockZ_append {a b : ℕ} (w : Fin a → ℝ) (τ : ℝ) (z : Fin b → ℝ) :
    blockZ (Fin.append (Fin.snoc w τ) z) = z := by
  funext k
  show Fin.append (Fin.snoc w τ) z (Fin.natAdd (a + 1) k) = z k
  rw [Fin.append_right]

/-! ## 6. The choice set -/

/-- The set of points `(w,τ,z) ∈ ℝ^{(a+1)+b}` with `z ≠ 0`, `‖z‖ ≤ τ` and `(w,z) ∈ E`: the
domain of the definable choice of `SphereChoice`. -/
def sphereSet {a b : ℕ} (E : Set (Fin (a + b) → ℝ)) : Set (Fin ((a + 1) + b) → ℝ) :=
  {x | 0 < ‖blockZ x‖ ∧ ‖blockZ x‖ ≤ blockT x ∧ Fin.append (blockW x) (blockZ x) ∈ E}

theorem mem_sphereSet {a b : ℕ} {E : Set (Fin (a + b) → ℝ)} {x : Fin ((a + 1) + b) → ℝ} :
    x ∈ sphereSet E ↔
      0 < ‖blockZ x‖ ∧ ‖blockZ x‖ ≤ blockT x ∧ Fin.append (blockW x) (blockZ x) ∈ E :=
  Iff.rfl

end Work.WilCrux
