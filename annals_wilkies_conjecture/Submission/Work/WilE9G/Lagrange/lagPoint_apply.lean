import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum

namespace Work.WilE9G.Lagrange

/-- `lagPoint` on the base-and-fibre indices is the projection back to `z`. -/
theorem lagPoint_apply {n m j : ℕ} (hk : n + (1 + m) ≤ n + (1 + (m + j + 1)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ) :
    (Work.WilE7.takeZ hk (Work.WilE9G.lagPoint z mu mu0) = z) ∧
      (∀ i : Fin (n + (1 + m)),
        Work.WilE9G.lagPoint z mu mu0 (Fin.castLE hk i) = z i) ∧
      (∀ a : Fin j, Work.WilE9G.lagPoint z mu mu0 (Work.WilE9G.Lagrange.muIdx n m a) = mu a) ∧
      (Work.WilE9G.lagPoint z mu mu0 (Work.WilE9G.Lagrange.mu0Idx n m j) = mu0) := by
  -- The base-and-fibre block of `lagPoint` sits in the first `n + (1+m)` coordinates.
  have hcast : ∀ (e : n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1)) (i : Fin (n + (1 + m))),
      Fin.cast e (Fin.castLE hk i) = Fin.castAdd (j + 1) i := fun e i => Fin.ext rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    show Work.WilE9G.lagPoint z mu mu0 (Fin.castLE hk i) = z i
    simp only [Work.WilE9G.lagPoint, finCongr_apply]
    rw [hcast]
    rw [Fin.append_left]
  · intro i
    simp only [Work.WilE9G.lagPoint, finCongr_apply]
    rw [hcast]
    rw [Fin.append_left]
  · intro a
    simp only [Work.WilE9G.lagPoint, finCongr_apply]
    have hidx : ∀ (e : n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1)),
        Fin.cast e (Work.WilE9G.Lagrange.muIdx n m a)
          = Fin.natAdd (n + (1 + m)) (Fin.castAdd 1 a) := fun e => Fin.ext rfl
    rw [hidx]
    rw [Fin.append_right]
    rw [Fin.append_left]
  · simp only [Work.WilE9G.lagPoint, finCongr_apply]
    have hidx : ∀ (e : n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1)),
        Fin.cast e (Work.WilE9G.Lagrange.mu0Idx n m j)
          = Fin.natAdd (n + (1 + m)) (Fin.last j) := fun e => Fin.ext rfl
    rw [hidx]
    rw [Fin.append_right]
    rw [show Fin.last j = Fin.natAdd j (0 : Fin 1) from Fin.ext (by simp)]
    rw [Fin.append_right]

end Work.WilE9G.Lagrange
