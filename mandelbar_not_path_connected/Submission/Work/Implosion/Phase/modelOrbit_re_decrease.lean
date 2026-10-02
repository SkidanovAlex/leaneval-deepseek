import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Phase

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Phase

/-- The real part of the model orbit decreases linearly between two times `m ≤ n`:
each of the `n − m` intermediate steps moves the real part by at most `-(1-δ)`. -/
theorem modelOrbit_re_decrease (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ) {m n : ℕ} (hmn : m ≤ n)
    (hδ : ∀ k : ℕ, k < n → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ) :
    (modelOrbit a h n u).re ≤ (modelOrbit a h m u).re - (n - m : ℕ) * (1 - δ) := by
  have hmn' : m + (n - m) = n := Nat.add_sub_of_le hmn
  -- the orbit is an iterate, so starting at time `m` and iterating `k` times
  -- is the same as the orbit at time `m + k`
  have hiter : ∀ k : ℕ, modelOrbit a h k (modelOrbit a h m u) = modelOrbit a h (m + k) u := by
    intro k
    simp only [modelOrbit]
    rw [← Function.iterate_add_apply, Nat.add_comm k m]
  have hcond : ∀ k : ℕ, k < n - m →
      ‖modelDisp a h (modelOrbit a h k (modelOrbit a h m u)) + 1‖ ≤ δ := by
    intro k hk
    rw [hiter k]
    exact hδ (m + k) (by omega)
  have hle := re_modelOrbit_le a h (modelOrbit a h m u) δ (n - m) hcond
  have heq : modelOrbit a h (n - m) (modelOrbit a h m u) = modelOrbit a h n u := by
    rw [hiter (n - m), hmn']
  rwa [heq] at hle

end Work.Implosion.Phase
