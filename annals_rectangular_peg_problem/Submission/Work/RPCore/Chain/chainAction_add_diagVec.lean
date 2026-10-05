import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.ChainDefs

/-!
# The diagonal `2π`-shift acts trivially on the chain action

`diagVec n` shifts the angular coordinate `q₂` of every vertex by `1`, so
`z + (2π) • diagVec n` is the chain whose positions have all their `q₂`-coordinates translated
by `2π` (and whose momenta are unchanged).  Since the kinetic part of `chainAction` only sees
differences `q_{j+1} - q_j` of consecutive positions and every generating function `W j` is
`2π`-periodic in `q₂`, the chain action is invariant under this shift.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

/-- `Tk 1` acts on the pair `(q, p)` by adding `(0, 2π)` to the position `q`. -/
theorem Tk_one_mk (x p : ℝ × ℝ) : Tk 1 (x, p) = (x + (0, 2 * Real.pi), p) := by
  ext <;> simp [Tk]

/-- Adding the constant `(0, 2π)` to the angular coordinate of every vertex leaves the
broken-geodesic action unchanged: the kinetic part is a sum of differences of consecutive
positions, where the shift cancels, and every `W j` is `2π`-periodic in `q₂`. -/
theorem chainAction_shift_angle (n : ℕ) (W : Fin (n + 1) → PS → ℝ)
    (hWper : ∀ j x, W j (Tk 1 x) = W j x) (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ) :
    chainAction n W (fun j => q j + (0, 2 * Real.pi)) P = chainAction n W q P := by
  unfold chainAction
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp [Prod.fst_add, Prod.snd_add]
  · apply Finset.sum_congr rfl
    intro j _
    have hx : (q j + (0, 2 * Real.pi), if h : (j : ℕ) < n then P ⟨j, h⟩ else 0)
        = Tk 1 (q j, if h : (j : ℕ) < n then P ⟨j, h⟩ else 0) := by
      rw [Tk_one_mk]
    rw [hx, hWper]

theorem chainAction_add_diagVec (n : ℕ) (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWper : ∀ j x, W j (Work.RPV.Tk 1 x) = W j x) (z : ChainSp n) :
    Work.RPV.chainAction n W (z + (2 * Real.pi) • diagVec n).1
        (z + (2 * Real.pi) • diagVec n).2
      = Work.RPV.chainAction n W z.1 z.2 := by
  have hfst : (z + (2 * Real.pi) • diagVec n).1 = fun j => z.1 j + (0, 2 * Real.pi) := by
    funext j
    simp [diagVec]
  have hsnd : (z + (2 * Real.pi) • diagVec n).2 = z.2 := by
    funext j
    simp [diagVec]
  rw [hfst, hsnd]
  exact chainAction_shift_angle n W hWper z.1 z.2

end

end Work.RPCore.Chain
