/-
# The `α`-relative Böttcher argument of a point of a dynamical ray

`Work.EL.paramRay hN ϑ` is the dynamical ray of angle `ϑ` of the parameter `c` (the ray of the
Böttcher coordinate `dynPhi c φ`), and `Work.GATE.deviation φ α z` is the displacement of the
Böttcher argument of `z` from the direction `α`, measured in the lift of the argument into
`(α - 1/2, α + 1/2]`.

This module proves that on a ray the deviation is the *honest* angle difference: a point of the
ray of angle `ϑ` has Böttcher argument `ϑ + k` for an integer `k`, hence its `α`-relative lift is
`ϑ` itself — and so its deviation is `ϑ - α` — as soon as `|ϑ - α| < 1/2`, i.e. as soon as the
ray angle `ϑ` lies in the interval on which the lift is taken.

The point is that the lift `liftAngle φ α z` is *defined* by an integer shift
`bAngle φ z + ⌊α - bAngle φ z + 1/2⌋`, so the argument of the ray point only has to be identified
modulo `2π`: from `φ z = t * exp (2πiϑ)` (`t > 1`) one gets
`arg (φ z) = toIocMod (-π) (2πϑ) = 2πϑ - toIocDiv (-π) (2πϑ) • 2π`, i.e.
`bAngle φ z = ϑ + k` for the integer `k = -toIocDiv (-π) (2πϑ)`.
-/
import Mathlib
import Submission.Work.GATE.Gate.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE.Nest

theorem deviation_eq_of_mem_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {α ϑ : ℝ} (hα : |ϑ - α| < 1 / 2) {z : ℂ} (hz : z ∈ Work.EL.paramRay hN ϑ) :
    Work.GATE.deviation φ α z = ϑ - α := by
  obtain ⟨hzK, t, ht, hΦ⟩ := hz
  have hφz : φ z = Work.Top.NakaneData.rayPoint ϑ t :=
    (Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hzK).symm.trans hΦ
  have htpos : (0 : ℝ) < t := by linarith
  -- the Böttcher coordinate of `z` is `t * exp (2πiϑ)` with `t > 0`
  have hpt : φ z = (t : ℂ) * Complex.exp (((2 * Real.pi * ϑ : ℝ) : ℂ) * Complex.I) := by
    rw [hφz, Work.Top.NakaneData.rayPoint]; push_cast; ring
  -- so its argument is the `(-π, π]`-representative of `2πϑ`
  have harg : (φ z).arg = toIocMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * ϑ) := by
    rw [hpt, Complex.arg_real_mul _ htpos, Complex.arg_exp_mul_I]
  have hcongr : toIocMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * ϑ)
      = 2 * Real.pi * ϑ
        - (toIocDiv Real.two_pi_pos (-Real.pi) (2 * Real.pi * ϑ)) • (2 * Real.pi) :=
    eq_sub_of_add_eq (toIocMod_add_toIocDiv_zsmul (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi)
      (2 * Real.pi * ϑ))
  -- hence the Böttcher argument is `ϑ` up to an integer
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Work.GATE.bAngle φ z = ϑ + k := by
    refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) (2 * Real.pi * ϑ), ?_⟩
    rw [Work.GATE.bAngle, harg, hcongr, zsmul_eq_mul]
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  -- the `α`-relative lift picks the representative in `(α - 1/2, α + 1/2]`, which is `ϑ`
  rw [Work.GATE.deviation_def]
  have hlift : Work.GATE.liftAngle φ α z = ϑ := by
    rw [Work.GATE.liftAngle, hk]
    have h2 : ⌊α - ϑ + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      rw [abs_lt] at hα
      exact ⟨by linarith [hα.2], by linarith [hα.1]⟩
    have hfloor : ⌊α - (ϑ + (k : ℝ)) + 1 / 2⌋ = -k := by
      have h1 : α - (ϑ + (k : ℝ)) + 1 / 2 = (α - ϑ + 1 / 2) - (k : ℝ) := by ring
      rw [h1, Int.floor_sub_intCast, h2]
      ring
    rw [hfloor]
    push_cast
    ring
  rw [hlift]

end Work.GATE.Nest
