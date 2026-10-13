/-
  Auxiliary lemmas about `iterDir` (the iterated directional derivative of `Engine.lean`).

  * `iterDir_contDiffAt` — smoothness: if `G` is `C^{|L| + k}` at `z` then `iterDir L G` is
    `C^k` at `z`.  In particular `iterDir L G` is `C^{|L| - |L'|}` whenever `G` is smooth
    enough, which is what the commuting-partials argument needs.
-/
import Mathlib
import Submission.Work.WilG4c.Engine

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open Work.WilkG4c

/-- **Smoothness of the iterated directional derivative.**  If `G` is `C^{|L| + k}` at `z`,
then its iterated directional derivative `iterDir L G` is `C^k` at `z`. -/
theorem iterDir_contDiffAt {m : ℕ} (G : (Fin m → ℝ) → ℝ) :
    ∀ (L : List (Fin m)) (k : ℕ) (z : Fin m → ℝ),
      ContDiffAt ℝ (L.length + k) G z → ContDiffAt ℝ k (iterDir L G) z := by
  intro L
  induction L with
  | nil => intro k z hG; simpa using hG
  | cons i M ih =>
    intro k z hG
    rw [iterDir_cons]
    apply ContDiffAt.clm_apply
    · apply ContDiffAt.fderiv_right
      · exact ih (k + 1) z (by
          have e : (↑M.length + ↑(k + 1) : WithTop ℕ∞) = ↑(i :: M).length + ↑k := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]
          rw [e]; exact hG)
      · exact le_refl _
    · exact contDiffAt_const

end Work.WilG4c
