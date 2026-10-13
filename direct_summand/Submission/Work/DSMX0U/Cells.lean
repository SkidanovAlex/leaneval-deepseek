import Mathlib
import Submission.Work.DSMX0U.Cell

/-!
# DSMX0U — the tower of cells

This file defines the recursion producing the tower of cells from a base cell and a step function,
and the resulting tower `tower hstep M s₀ : (k : ℕ) → Cell A C c₀ (levelDeg M k)`.

## The degree bookkeeping

`levelDeg M k` is the *upper* degree of the `k`-th level of the tower (see the discussion in
`Submission/Work/DSMX0U/Cell.lean`: a `Cell A C c₀ q` occupies the degrees `[q - 1, q]`).  It is
defined by recursion

  `levelDeg M 0 = M + 1`,  `levelDeg M (k + 1) = levelDeg M k - 1`,

so that `levelDeg M (k + 1)` is *definitionally* `levelDeg M k - 1`, i.e. the predecessor degree of
level `k + 1` is definitionally the current degree of level `k`.  This is what makes the step
`Work.DSMX0U.stepCell` applicable without any `eqToHom`-transport.  The level `k` term of the model
therefore sits in cohomological degree `levelDeg M k - 1 = M - k` (`levelDeg_cur`), which is proved
separately and used only when a concrete degree has to be recognised.

## The tower

`tower hstep M s₀` is the sequence of cells whose `k`-th term lives in degree `levelDeg M k - 1`.
The step function `hstep` is an argument (rather than being produced by an existential): this keeps
the construction free of `Classical.choice`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

/-- The upper degree of the `k`-th level of the tower based at `M`: `M + 1`, `M`, `M - 1`, …  It is
defined by recursion, so that `levelDeg M (k + 1)` is definitionally `levelDeg M k - 1`.

It is marked `@[reducible]` so that degree expressions such as `levelDeg M (k + 1)` and
`levelDeg M k - 1` (or `levelDeg M k` and `levelDeg M (k+1) + 1`) are interchangeable for the
elaborator. -/
@[reducible]
def levelDeg (M : ℤ) : ℕ → ℤ := fun k => Nat.rec (M + 1) (fun _ d => d - 1) k

@[simp]
theorem levelDeg_zero (M : ℤ) : levelDeg M 0 = M + 1 := rfl

@[simp]
theorem levelDeg_succ (M : ℤ) (k : ℕ) : levelDeg M (k + 1) = levelDeg M k - 1 := rfl

/-- The upper degree of the `k`-th level of the tower, as a subtraction. -/
theorem levelDeg_eq (M : ℤ) (k : ℕ) : levelDeg M k = M + 1 - (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [levelDeg_succ, ih]; push_cast; ring

/-- The degree of the *term* of the model at level `k`: `M - k`. -/
theorem levelDeg_cur (M : ℤ) (k : ℕ) : levelDeg M k - 1 = M - (k : ℤ) := by
  rw [levelDeg_eq]; ring

/-- The level whose current degree is `0` is the `M`-th one. -/
@[simp]
theorem levelDeg_cur_eq_zero_iff (M : ℤ) (k : ℕ) : levelDeg M k - 1 = 0 ↔ (k : ℤ) = M := by
  rw [levelDeg_cur, sub_eq_zero, eq_comm]

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- **The tower of cells.**  Given a base cell `s₀` whose current degree is `M` (i.e.
`s₀ : Cell A C c₀ (M + 1)`) and a step function producing a `StepData` for every cell, this is the
sequence of cells of the model, the `k`-th one having current degree `levelDeg M k - 1 = M - k`. -/
noncomputable def tower (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : (k : ℕ) → Cell A C c₀ (levelDeg M k) :=
  Nat.rec s₀ (fun k s => stepCell A s (hstep (levelDeg M k) s))

variable {hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s} {M : ℤ} {s₀ : Cell A C c₀ (M + 1)}

@[simp]
theorem tower_zero : tower hstep M s₀ 0 = s₀ := rfl

theorem tower_succ (k : ℕ) :
    tower hstep M s₀ (k + 1) =
      stepCell A (tower hstep M s₀ k) (hstep (levelDeg M k) (tower hstep M s₀ k)) :=
  rfl

/-! ## The definitional links between consecutive levels

These are the identities (all by `rfl`, from the definition of `stepCell`) which make the tower a
complex: the term of level `k + 1` in degree `levelDeg M k` is the term of level `k`, and the same
holds for the excess kernel `Kprev` and the map `φprev` into `C`. -/

@[simp]
theorem tower_Gprev (k : ℕ) : (tower hstep M s₀ (k + 1)).Gprev = (tower hstep M s₀ k).G A := rfl

@[simp]
theorem tower_Kprev (k : ℕ) : (tower hstep M s₀ (k + 1)).Kprev = (tower hstep M s₀ k).K A := rfl

@[simp]
theorem tower_φprev (k : ℕ) : (tower hstep M s₀ (k + 1)).φprev = (tower hstep M s₀ k).φ A := rfl

@[simp]
theorem tower_gen (k : ℕ) :
    (tower hstep M s₀ (k + 1)).gen = (hstep (levelDeg M k) (tower hstep M s₀ k)).gen := rfl

@[simp]
theorem tower_rel (k : ℕ) :
    (tower hstep M s₀ (k + 1)).rel = (hstep (levelDeg M k) (tower hstep M s₀ k)).rel := rfl

/-- The differential of the tower, from level `k + 1` to level `k`.  Its target is the term of
level `k` definitionally (`tower_Gprev`). -/
noncomputable abbrev towerD (k : ℕ) : (tower hstep M s₀ (k + 1)).G A ⟶ (tower hstep M s₀ k).G A :=
  (tower hstep M s₀ (k + 1)).d A

end Work.DSMX0U
