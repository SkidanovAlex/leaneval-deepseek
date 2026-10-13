import Mathlib
import Submission.Work.WilG4c.Defs

namespace Work.WilG4c

open Work.WilkG4c

theorem CdpSliceContDiffAt {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {x : ℝ} {y : Fin n → ℝ} {m : ℕ}
    (h : ContDiffAt ℝ m g (Work.WilkG4c.pt x y)) :
    ContDiffAt ℝ m (Work.WilkG4c.slice g x) y := by
  -- `slice g x = g ∘ pt x`, and `pt x` is (the underlying function of) a continuous linear
  -- map `(Fin n → ℝ) → (Fin (n+1) → ℝ)`, hence smooth; compose with `h`.
  have hpt : ContDiffAt ℝ m (pt x) y := by
    rw [contDiffAt_pi]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (contDiffAt_const (x := y) (c := x) (n := m) (𝕜 := ℝ))
    · simpa [pt_succ] using (contDiffAt_apply ℝ ℝ (n := m) (ι := Fin n) j y)
  exact h.comp y hpt

end Work.WilG4c
