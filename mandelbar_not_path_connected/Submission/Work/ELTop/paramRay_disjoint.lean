import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ParamRays.MbDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- The topologist's point `rayPoint θ t = t * exp (2πiθ)` of the ray of angle `θ` at level `t`
is the level times the unit direction `Work.ParamRays.rayDir θ = exp (2πiθ)`. -/
theorem rayPoint_eq_mul_rayDir (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * Work.ParamRays.rayDir θ := by
  have harg : (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Work.Top.NakaneData.rayPoint, Work.ParamRays.rayDir, harg]

/-- Dynamical parameter rays of different external angles are disjoint.

Route: a point `z` lying on both rays satisfies
`Φ z = t * exp(2πiθ) = t' * exp(2πiθ')` with `t, t' > 1`. Taking norms and using
`norm_rayPoint` gives `t = t'`, hence after cancelling the non-zero scalar
`exp(2πiθ) = exp(2πiθ')`; then `rayDir_eq_iff` produces `k : ℤ` with `θ' = θ + k`,
contradicting the hypothesis. -/
theorem paramRay_disjoint {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ θ' : ℝ}
    (h : ∀ k : ℤ, θ' ≠ θ + k) : Disjoint (Work.EL.paramRay hN θ) (Work.EL.paramRay hN θ') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [Work.Top.NakaneData.mem_paramRay_iff] at hz hz'
  obtain ⟨-, t, ht, htz⟩ := hz
  obtain ⟨-, t', ht', ht'z⟩ := hz'
  -- the two ray points coincide
  have hraypt : Work.Top.NakaneData.rayPoint θ t = Work.Top.NakaneData.rayPoint θ' t' := htz.symm.trans ht'z
  have htpos : 0 < t := lt_trans one_pos ht
  have ht'pos : 0 < t' := lt_trans one_pos ht'
  -- the levels agree, being the norms of the common value
  have htt : t = t' := by
    have e1 : ‖Work.Top.NakaneData.rayPoint θ t‖ = t := by
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos htpos]
    have e2 : ‖Work.Top.NakaneData.rayPoint θ' t'‖ = t' := by
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos ht'pos]
    rw [← e1, ← e2, hraypt]
  -- cancel the non-zero scalar to compare the directions
  have hdir : Work.ParamRays.rayDir θ = Work.ParamRays.rayDir θ' := by
    have h1 : (t : ℂ) * Work.ParamRays.rayDir θ = (t' : ℂ) * Work.ParamRays.rayDir θ' := by
      rw [← rayPoint_eq_mul_rayDir θ t, ← rayPoint_eq_mul_rayDir θ' t', hraypt]
    rw [htt] at h1
    exact mul_left_cancel₀ (by exact_mod_cast ne_of_gt ht'pos) h1
  obtain ⟨k, hk⟩ := Work.ParamRays.rayDir_eq_iff.mp hdir
  exact h k hk

end Work.ELTop
