import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basin_basic

namespace Work.Parab.Eends

/-- **The orbit stays in the basin and the Abel equation iterates.**  If `z` is a point of the uniform parabolic basin at which `f` is analytic and not locally constant along the first `n` iterates, then those iterates are again in the basin (by `Work.Parab.basin_forward`), and `Φ (f^[n] z) = Φ z + n` for every `Φ` satisfying the Abel equation on the basin. -/
theorem basin_iterate_Phi {f : ℂ → ℂ} {D : Set ℂ} {Φ : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΦ : ∀ z ∈ MandelDim.ParabolicBasin f D, Φ (f z) = Φ z + 1)
    (hz : z ∈ MandelDim.ParabolicBasin f D)
    (han : ∀ k ≤ n, AnalyticAt ℂ f (f^[k] z))
    (hnc : ∀ k ≤ n, ¬ ∀ᶠ w in nhds (f^[k] z), f w = f (f^[k] z)) :
    (∀ k ≤ n, f^[k] z ∈ MandelDim.ParabolicBasin f D) ∧ Φ (f^[n] z) = Φ z + (n : ℂ) := by
  -- membership of all iterates up to `n`, by forward invariance of the basin
  have hmem : ∀ k ≤ n, f^[k] z ∈ MandelDim.ParabolicBasin f D := by
    intro k
    induction k with
    | zero => intro _; simpa using hz
    | succ j ih =>
        intro hk
        have hj : j ≤ n := le_trans (Nat.le_succ j) hk
        rw [Function.iterate_succ_apply']
        exact basin_forward (han j hj) (hnc j hj) (ih hj)
  refine ⟨hmem, ?_⟩
  -- the Abel equation iterated along the orbit
  have hiter : ∀ k ≤ n, Φ (f^[k] z) = Φ z + (k : ℂ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ j ih =>
        intro hk
        have hj : j ≤ n := le_trans (Nat.le_succ j) hk
        rw [Function.iterate_succ_apply']
        rw [hΦ (f^[j] z) (hmem j hj), ih hj]
        push_cast
        ring
  exact hiter n le_rfl

end Work.Parab.Eends
