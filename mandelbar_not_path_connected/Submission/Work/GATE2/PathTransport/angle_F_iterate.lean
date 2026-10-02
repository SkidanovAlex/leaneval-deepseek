import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.varphiCrit_F_iterate
import Submission.Work.GATE2.phase_gap_integrality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport

/-! # GATE2 / PathTransport — the `1024`-fold angle equation along the high iterate

The Böttcher coordinate of the critical point is multiplied by `1024` under the high return map
`F_c = (T_c)^{10}` (`Work.GATE2.varphiCrit_F_iterate`), and the *angle* of a product of complex
numbers is the sum of the angles (`Complex.arg_pow_coe_angle`).  The `α`-relative angle
`A z := (arg (φ_c z) : Real.Angle) − (2π α : Real.Angle)` is therefore multiplied by `1024^j`
under `(F_c)^[j]` **provided the twist `1024^j · 2π α` of the root angle returns to `2π α` in
`Real.Angle`**, i.e. `(1024^j − 1) α ∈ ℤ`.  That is exactly the arithmetic of the root angle
`1023 α = 371` together with `1023 ∣ 1024^j − 1`
(`Work.GATE2.PhaseGap.exists_int_pow_sub_one_mul`).

The two ingredients are the auxiliary `nsmul_coe_two_pi_mul_eq_self` (the triviality of the
twist) and `Work.GATE2.varphiCrit_F_iterate` composed with `Complex.arg_pow_coe_angle`. -/

/-- **The twist of the root angle is trivial under the `1024`-fold iteration.**  For a root angle
`α` with `1023 α = 371`, the angle `2π α` is fixed by the `1024^j`-fold multiple:
`(1024^j) • (2π α : Real.Angle) = (2π α : Real.Angle)`.

Indeed `(1024^j − 1) · 2π α = 2π · (1024^j − 1) α` with `(1024^j − 1) α ∈ ℤ`, since
`1023 ∣ 1024^j − 1`. -/
theorem nsmul_coe_two_pi_mul_eq_self {α : ℝ} (hα : 1023 * α = 371) (j : ℕ) :
    (1024 ^ j) • ((2 * Real.pi * α : ℝ) : Real.Angle)
      = ((2 * Real.pi * α : ℝ) : Real.Angle) := by
  rw [← sub_eq_zero]
  -- rewrite the multiple as a single angle and the difference as the angle of the difference
  have h1 : (1024 ^ j) • ((2 * Real.pi * α : ℝ) : Real.Angle)
      = ((((1024 ^ j : ℕ) : ℝ) * (2 * Real.pi * α)) : Real.Angle) :=
    (Real.Angle.natCast_mul_eq_nsmul _ _).symm
  rw [h1, ← Real.Angle.coe_sub, Real.Angle.coe_eq_zero_iff]
  -- the resulting real number is an integer multiple of `2π`, by the integrality of the twist
  obtain ⟨t, ht⟩ := Work.GATE2.PhaseGap.exists_int_pow_sub_one_mul hα j
  refine ⟨t, ?_⟩
  rw [zsmul_eq_mul]
  have hX : (((1024 ^ j : ℕ)) : ℝ) * (2 * Real.pi * α) - 2 * Real.pi * α
      = ((t : ℝ)) * (2 * Real.pi) := by
    rw [← ht]; ring
  rw [hX]

/-- **The `1024`-fold angle equation along the high iterate.**  For a point `z` of the critical
domain of `c`, the `α`-relative Böttcher angle
`A z := (arg (φ_c z) : Real.Angle) − (2π α : Real.Angle)` is multiplied by `1024^j` under
`(F_c)^[j]`, for a root angle `α` with `1023 α = 371` (so that `(1024^j − 1) · 2π α ∈ 2π ℤ`).

This is item (A1) of the design `NOTES_LEAD_mandelbar_gate2transport.md` §3. -/
theorem angle_F_iterate {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) {α : ℝ}
    (hα : 1023 * α = 371) (j : ℕ) :
    (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)
      = (1024 ^ j) • ((Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)) := by
  -- the twist of the root angle is fixed by `1024^j`
  have hβfix : (1024 ^ j) • ((2 * Real.pi * α : ℝ) : Real.Angle)
      = ((2 * Real.pi * α : ℝ) : Real.Angle) := nsmul_coe_two_pi_mul_eq_self hα j
  -- the Böttcher equation `(φ_c z)^(1024^j) = φ_c ((F_c)^[j] z)` gives the angle equation
  have hang : (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
      = (1024 ^ j) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle) := by
    rw [← Work.GATE2.varphiCrit_F_iterate hz j]
    exact Complex.arg_pow_coe_angle _ _
  calc (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)
      = (1024 ^ j) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle) := by rw [hang]
    _ = (1024 ^ j) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle)
        - (1024 ^ j) • ((2 * Real.pi * α : ℝ) : Real.Angle) := by rw [hβfix]
    _ = (1024 ^ j) • ((Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)) := by rw [nsmul_sub]

end Work.GATE2.PathTransport
