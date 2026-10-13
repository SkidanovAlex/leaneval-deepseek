import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces

/-- The elementary trigonometric comparison behind the `s ∈ [π/4, π/2)` half of the power
toolkit: writing `t = π/2 - s ∈ (0, π/4]`, both `cos s = sin t` and `sin (2 s) = sin (2 t)`
are the sines of angles in `[0, π/2]`, so Jordan's inequality `2 x / π ≤ sin x` gives
`sin t ≥ 2t/π` and `sin (2t) ≥ 4t/π`, whence
`sin t · sin(2t)² ≥ (2t/π)(4t/π)² = 32 t³/π³`, i.e.
`1/(cos s · sin(2s)²) ≤ π³/(32 t³)`. -/
theorem trigRight :
    ∀ s ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) ≤
        (Real.pi ^ 3 / 32) / (Real.pi / 2 - s) ^ 3 := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  -- substitute the distance to the right endpoint
  set t := Real.pi / 2 - s with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htle : t ≤ Real.pi / 4 := by rw [ht]; linarith
  have htlt : t < Real.pi := by linarith [Real.pi_pos]
  have hcos : Real.cos s = Real.sin t := by
    rw [show s = Real.pi / 2 - t from by rw [ht]; ring, Real.cos_pi_div_two_sub]
  have hsin : Real.sin (2 * s) = Real.sin (2 * t) := by
    rw [show 2 * s = Real.pi - 2 * t from by rw [ht]; ring, Real.sin_pi_sub]
  rw [hcos, hsin]
  -- Jordan's inequality for `t` and `2t`
  have hA : 2 / Real.pi * t ≤ Real.sin t :=
    Real.mul_le_sin htpos.le (by linarith [htle, Real.pi_pos])
  have hB : 2 / Real.pi * (2 * t) ≤ Real.sin (2 * t) :=
    Real.mul_le_sin (by linarith) (by linarith [htle, Real.pi_pos])
  have hB2 : (2 / Real.pi * (2 * t)) ^ 2 ≤ (Real.sin (2 * t)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hB 2
  have hprod : (2 / Real.pi * t) * (2 / Real.pi * (2 * t)) ^ 2 ≤
      Real.sin t * (Real.sin (2 * t)) ^ 2 :=
    mul_le_mul hA hB2 (by positivity) (Real.sin_pos_of_pos_of_lt_pi htpos htlt).le
  have harith : (2 / Real.pi * t) * (2 / Real.pi * (2 * t)) ^ 2 = 32 * t ^ 3 / Real.pi ^ 3 := by
    field_simp; ring
  have hprod' : 32 * t ^ 3 / Real.pi ^ 3 ≤ Real.sin t * (Real.sin (2 * t)) ^ 2 := by
    rw [← harith]; exact hprod
  -- multiply the lower bound by the positive constant `π³/32`
  have h1 : (Real.pi ^ 3 / 32) * (32 * t ^ 3 / Real.pi ^ 3) = t ^ 3 := by field_simp
  have hmain : t ^ 3 ≤ (Real.pi ^ 3 / 32) * (Real.sin t * (Real.sin (2 * t)) ^ 2) := by
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hprod' (by positivity)
  -- convert `t³ ≤ C · sin t · sin(2t)²` into the displayed division inequality
  have hden : 0 < Real.sin t * (Real.sin (2 * t)) ^ 2 :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi htpos htlt)
      (pow_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) 2)
  have ht3 : 0 < t ^ 3 := by positivity
  rw [div_le_div_iff₀ hden ht3]
  simpa using hmain

end Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces
