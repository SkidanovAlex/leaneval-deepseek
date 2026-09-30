import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- For a nonnegative continuous `p`-periodic function `φ`, the integral over any window of
length `L ≤ p` is at most the integral over one full period. -/
theorem periodic_window_integral_le {φ : ℝ → ℝ} {p L a : ℝ} (hp : 0 < p)
    (hper : Function.Periodic φ p) (hnn : ∀ x, 0 ≤ φ x) (hL : 0 ≤ L) (hLp : L ≤ p)
    (hcont : Continuous φ) :
    (∫ x in a..(a+L), φ x) ≤ ∫ x in (0)..p, φ x := by
  -- The integral over any full period equals the integral over `[0, p]`.
  have hshift : ∫ x in a..(a+p), φ x = ∫ x in (0)..p, φ x := by
    have h := hper.intervalIntegral_add_eq a 0
    simpa using h
  rw [← hshift]
  -- Enlarge the window `[a, a+L]` to the full period `[a, a+p]`; `φ ≥ 0`.
  exact intervalIntegral.integral_mono_interval (le_refl a) (by linarith) (by linarith)
    (Filter.Eventually.of_forall hnn) (hcont.intervalIntegrable a (a+p))

end Work.BMF.mrlas
