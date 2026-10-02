import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- The map `θ ↦ t * exp (2πiθ)` is injective in the angle modulo `ℤ`: two angles give the same
point of the circle of radius `t > 0` iff they differ by an integer. -/
theorem rayPoint_angle_eq_int {θ θ' t : ℝ} (ht : 1 < t)
    (h : Work.Top.NakaneData.rayPoint θ t = Work.Top.NakaneData.rayPoint θ' t) :
    ∃ k : ℤ, θ' = θ + k := by
  have ht0 : (t : ℂ) ≠ 0 := by
    have : (0 : ℝ) < t := by linarith
    exact_mod_cast ne_of_gt this
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * (θ' : ℂ) * Complex.I) := by
    have hh := h
    rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint] at hh
    exact mul_left_cancel₀ ht0 hh
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have him := congrArg Complex.im hn
  simp at him
  refine ⟨-n, ?_⟩
  have : θ - θ' = (n : ℝ) := by nlinarith [Real.pi_pos]
  push_cast
  linarith

/-- Two points of the dynamical plane at the same level `R > 1` whose rays have angles `θ` and
`θ'` coincide only if the angles differ by an integer: the Böttcher coordinate `dynPhi c φ`
is injective on the complement of `K c` and sends `rayPt hN θ R` to `R * exp (2πiθ)`. -/
theorem rayPt_inj {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) {θ θ' : ℝ}
    (h : Work.EL.rayPt hN θ R = Work.EL.rayPt hN θ' R) : ∃ k : ℤ, θ' = θ + k := by
  refine rayPoint_angle_eq_int hR ?_
  have hh := congrArg (Work.EL.dynPhi c φ) h
  rwa [Work.Top.NakaneData.Phi_rayPt hN hR, Work.Top.NakaneData.Phi_rayPt hN hR] at hh

end Work.ELTop
