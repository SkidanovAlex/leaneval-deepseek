/-
  Area G4b: index bookkeeping for the `Ω`-membership of the augmented choice set
  `StarSet f c d M ⊆ ℝ^{n+3}`.

  `StarSet` is the set of `(x, y, w, u)` with `x ∈ (c,d)`, `y` in the open cube, `w = f(x,y)`,
  `u ≥ 0`, `|∂₀ f(x,y)| > M (1 + n u)` and `|∂_{y_j} f(x,y)| ≤ u` for every `j ≥ 1`.  To exhibit
  it as an `Ω`-set the existential quantifier over the partial `p = ∂ᵢ f(x,y)` is realised by
  putting `p` in a fresh coordinate and projecting it out.  With `(x,y,w,u) ∈ ℝ^{n+3}` and `p`
  added as the fresh last coordinate of `ℝ^{n+4}`, the point `(x, y, p)` (in that order!) must
  lie in `derivGraph f i ⊆ ℝ^{n+2}`; the index map `eEig n` selects exactly the coordinates
  `0, …, n` (that is `x` and `y`) together with the fresh one, skipping `w` and `u`.

  * `iU n` is the index of `u` inside `Fin (n+4)` (value `n+2`),
  * `iP n` is the index of the fresh partial (value `n+3`).
-/
import Mathlib
import Submission.Work.WilG4b.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4b

/-- The index map `Fin (n+2) → Fin (n+4)` sending `0,…,n` to `0,…,n` and the last index to
the last index; the coordinates `n+1, n+2` are skipped. -/
def eEig (n : ℕ) : Fin (n + 2) → Fin (n + 4) :=
  Fin.lastCases (Fin.last (n + 3)) (fun j : Fin (n + 1) => Fin.castAdd 3 j)

/-- The index of `u` in `Fin (n+4)` (value `n+2`). -/
def iU (n : ℕ) : Fin (n + 4) := Fin.castSucc (Fin.last (n + 2))

/-- The index of the fresh partial `p` in `Fin (n+4)` (value `n+3`, the last index). -/
def iP (n : ℕ) : Fin (n + 4) := Fin.last (n + 3)

@[simp] theorem eEig_last (n : ℕ) : eEig n (Fin.last (n + 1)) = Fin.last (n + 3) := by
  simp [eEig]

@[simp] theorem eEig_castSucc (n : ℕ) (j : Fin (n + 1)) :
    eEig n j.castSucc = Fin.castAdd 3 j := by
  simp [eEig]

@[simp] theorem iU_val (n : ℕ) : (iU n).val = n + 2 := rfl

@[simp] theorem iP_val (n : ℕ) : (iP n).val = n + 3 := rfl

/-- The pullback identity of the index map `eEig`. -/
theorem snoc_comp_eEig (n : ℕ) (y : Fin (n + 3) → ℝ) (t : ℝ) :
    (Fin.snoc y t) ∘ (eEig n) = Fin.snoc (Fin.init (Fin.init y)) t := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · rw [Function.comp_apply, eEig_last, Fin.snoc_last, Fin.snoc_last]
  · intro j
    show (Fin.snoc y t : Fin (n + 4) → ℝ) (eEig n j.castSucc)
        = (Fin.snoc (Fin.init (Fin.init y)) t : Fin (n + 2) → ℝ) j.castSucc
    rw [eEig_castSucc]
    rw [show Fin.castAdd 3 j = (Fin.castAdd 2 j).castSucc from Fin.ext rfl]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    simp only [Fin.init]
    exact congrArg y (Fin.ext rfl)

/-- The `u`-coordinate of `Fin.snoc y t`. -/
@[simp] theorem snoc_iU (n : ℕ) (y : Fin (n + 3) → ℝ) (t : ℝ) :
    (Fin.snoc y t : Fin (n + 4) → ℝ) (iU n) = y (Fin.last (n + 2)) := by
  simp [iU]

/-- The fresh-coordinate of `Fin.snoc y t`. -/
@[simp] theorem snoc_iP (n : ℕ) (y : Fin (n + 3) → ℝ) (t : ℝ) :
    (Fin.snoc y t : Fin (n + 4) → ℝ) (iP n) = t := by
  simp [iP]

end Work.WilG4b
