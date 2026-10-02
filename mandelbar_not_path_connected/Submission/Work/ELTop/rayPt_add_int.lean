import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- The point `t * exp (2πiθ)` of the exterior of the unit disc depends on the angle `θ` only
modulo `ℤ`: the rays are `1`-periodic in the angle, hence invariant under `θ ↦ θ + k`. -/
theorem rayPoint_add_int (θ t : ℝ) (k : ℤ) :
    Work.Top.NakaneData.rayPoint (θ + k) t = Work.Top.NakaneData.rayPoint θ t := by
  have h1 : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  have harg : (2 * (Real.pi : ℂ) * ((θ + k : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I
        + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, harg, Complex.exp_add, h1,
    mul_one]

/-- The points of the rays of the dynamical plane of `T_c` depend on the angle only modulo `ℤ`:
`rayPt` is invariant under `θ ↦ θ + k` for `k : ℤ`. -/
theorem rayPt_add_int {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ t : ℝ) (k : ℤ) :
    Work.EL.rayPt hN (θ + k) t = Work.EL.rayPt hN θ t := by
  by_cases ht : 1 < t
  · refine Work.Top.NakaneData.injOn_Phi hN (Work.Top.NakaneData.rayPt_notMem hN ht)
      (Work.Top.NakaneData.rayPt_notMem hN ht) ?_
    rw [Work.Top.NakaneData.Phi_rayPt hN ht, Work.Top.NakaneData.Phi_rayPt hN ht]
    exact rayPoint_add_int θ t k
  · simp only [Work.Top.NakaneData.rayPt, dite_eq_right ht]

end Work.ELTop
