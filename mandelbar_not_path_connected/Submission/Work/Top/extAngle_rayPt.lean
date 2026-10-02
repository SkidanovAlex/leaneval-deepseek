import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- The external angle of the point of the parameter ray of angle `θ` at level `t > 1` is `θ`.

The Böttcher coordinate of that point is the point `t * exp (2πiθ)` of the exterior disc,
whose argument is congruent to `2πθ` modulo `2π`; normalizing by `2π` and reducing modulo `1`
lands on `θ` itself whenever `0 ≤ θ < 1`. -/
theorem extAngle_rayPt {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {θ t : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (ht : 1 < t) :
    Work.Top.NakaneData.extAngle Φ (Work.Top.NakaneData.rayPt hN θ t) = θ := by
  have ht0 : (0 : ℝ) < t := by linarith
  rw [Work.Top.NakaneData.extAngle, hN.Phi_rayPt ht]
  -- the Böttcher image of the ray point is `t * exp (2πiθ)` with `t > 0`
  have hpt : Work.Top.NakaneData.rayPoint θ t
      = (t : ℂ) * Complex.exp ((↑(2 * Real.pi * θ) : ℂ) * Complex.I) := by
    rw [Work.Top.NakaneData.rayPoint]; push_cast; ring
  -- its argument is the `(-π, π]`-representative of `2πθ`
  have harg : (Work.Top.NakaneData.rayPoint θ t).arg
      = toIocMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * θ) := by
    rw [hpt, Complex.arg_real_mul _ ht0, Complex.arg_exp_mul_I]
  rw [harg]
  -- `toIcoMod` is characterized by membership in `[0,1)` plus congruence mod `1`
  rw [toIcoMod_eq_iff]
  refine ⟨⟨hθ₀, by linarith⟩, -toIocDiv Real.two_pi_pos (-Real.pi) (2 * Real.pi * θ), ?_⟩
  have h := toIocMod_add_toIocDiv_zsmul (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi)
    (2 * Real.pi * θ)
  have hcongr : toIocMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * θ)
      = 2 * Real.pi * θ
        - (toIocDiv Real.two_pi_pos (-Real.pi) (2 * Real.pi * θ)) • (2 * Real.pi) :=
    eq_sub_of_add_eq h
  rw [hcongr, zsmul_eq_mul]
  field_simp
  ring

end Work.Top
