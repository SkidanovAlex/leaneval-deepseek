/-
# Off-support tail decay of a Schwartz function

`Work.KMTAreas.A4.offTail` is the elementary tail estimate underlying the "off-diagonal" (far
from the origin) analysis of Area A4: for a Schwartz function `f : 𝓢(ℝ, ℂ)` and every `N : ℕ`
there is a constant `C > 0` with

  `∫⁻ y in {y | R ≤ |y|}, ‖f y‖ₑ ≤ C * (max R 1) ^ (-(N : ℝ))`   for all `R ≥ 0`.

The proof does not need any sharp information about the tail integral.  Writing the Schwartz
decay of `f` in the form `‖f y‖ ≤ A (1 + |y|)^{-(N+2)}` (`schwartz_decay_rpow` below), the
integrand splits as

  `(1 + |y|)^{-(N+2)} = (1 + |y|)^{-N} · (1 + |y|)^{-2}`,

and on the region `|y| ≥ R` the first factor is at most `(max R 1)^{-N}` while the second one is
integrable over all of `ℝ` (`finite_integral_one_add_norm` for `r = 2`, since `finrank ℝ ℝ = 1`).
The single constant `C = A * (∫⁻ (1+|y|)^{-2}) + 1` therefore works for every `R ≥ 0`; no case
distinction between `R ≤ 1` and `R ≥ 1` is needed, because `(max R 1)^{-N} ≥ 1` exactly when
`R ≤ 1`.
-/
import Mathlib

namespace Work.KMTAreas.A4

open MeasureTheory

/-- Schwartz decay with an arbitrary power: for every `m : ℕ` there is `A ≥ 0` with
`‖f y‖ ≤ A * (1 + |y|) ^ (-(m : ℝ))` for all `y`. -/
theorem schwartz_decay_rpow (f : SchwartzMap ℝ ℂ) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, ‖f y‖ ≤ A * (1 + |y|) ^ (-(m : ℝ)) := by
  obtain ⟨C₀, _hC₀pos, hC₀⟩ := f.decay 0 0
  obtain ⟨Cₘ, _hCₘpos, hCₘ⟩ := f.decay m 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hC₀
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hCₘ
  refine ⟨2 ^ m * (C₀ + Cₘ), by positivity, fun y => ?_⟩
  have h := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := m) (C₁ := C₀) (C₂ := Cₘ)
    (abs_nonneg y) (norm_nonneg (f y)) (hC₀ y) (by simpa using hCₘ y)
  simpa using h

theorem offTail (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      ∫⁻ y : ℝ in {y | R ≤ |y|}, ‖f y‖ₑ ≤ ENNReal.ofReal (C * (max R 1) ^ (-(N : ℝ))) := by
  obtain ⟨A, hA0, hA⟩ := schwartz_decay_rpow f (N + 2)
  -- finiteness of `∫⁻ (1 + |y|)^{-2}`, the only quantitative input besides the decay of `f`
  have hfin : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + |y|) ^ (-(2 : ℝ)))) < ⊤ := by
    have h := finite_integral_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
    simpa [Real.norm_eq_abs] using h
  set M : ENNReal := ∫⁻ y : ℝ, ENNReal.ofReal ((1 + |y|) ^ (-(2 : ℝ))) with hM
  have hMne : M ≠ ⊤ := by rw [hM]; exact ne_of_lt hfin
  set D : ℝ := M.toReal with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hMof : ENNReal.ofReal D = M := by rw [hD, ENNReal.ofReal_toReal hMne]
  refine ⟨A * D + 1, by positivity, fun R _hR => ?_⟩
  have hx0 : 0 ≤ (max R 1 : ℝ) ^ (-(N : ℝ)) := by positivity
  have hc0 : 0 ≤ A * (max R 1 : ℝ) ^ (-(N : ℝ)) := mul_nonneg hA0 hx0
  -- pointwise bound on the region `{|y| ≥ R}`
  have hpt : ∀ y : ℝ, R ≤ |y| →
      ‖f y‖ₑ ≤ ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ))) *
        ENNReal.ofReal ((1 + |y|) ^ (-(2 : ℝ))) := by
    intro y hy
    have hfac : (1 + |y|) ^ (-(((N + 2 : ℕ) : ℝ)))
        = (1 + |y|) ^ (-(N : ℝ)) * (1 + |y|) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |y|)]
      congr 1
      push_cast
      ring
    have hpow1 : (1 + |y|) ^ (-(N : ℝ)) ≤ (max R 1 : ℝ) ^ (-(N : ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos
      · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      · exact max_le (by linarith) (by have := abs_nonneg y; linarith)
      · simp
    have hreal : ‖f y‖ ≤ A * (max R 1 : ℝ) ^ (-(N : ℝ)) * (1 + |y|) ^ (-(2 : ℝ)) := by
      calc ‖f y‖ ≤ A * (1 + |y|) ^ (-(((N + 2 : ℕ) : ℝ))) := hA y
        _ = A * ((1 + |y|) ^ (-(N : ℝ)) * (1 + |y|) ^ (-(2 : ℝ))) := by rw [hfac]
        _ ≤ A * ((max R 1 : ℝ) ^ (-(N : ℝ)) * (1 + |y|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpow1 (by positivity)) hA0
        _ = A * (max R 1 : ℝ) ^ (-(N : ℝ)) * (1 + |y|) ^ (-(2 : ℝ)) := by ring
    calc ‖f y‖ₑ = ENNReal.ofReal ‖f y‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ)) * (1 + |y|) ^ (-(2 : ℝ))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ))) *
            ENNReal.ofReal ((1 + |y|) ^ (-(2 : ℝ))) :=
          ENNReal.ofReal_mul hc0
  calc ∫⁻ y : ℝ in {y | R ≤ |y|}, ‖f y‖ₑ
      ≤ ∫⁻ y : ℝ in {y | R ≤ |y|}, ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ))) *
          ENNReal.ofReal ((1 + |y|) ^ (-(2 : ℝ))) :=
        setLIntegral_mono (by fun_prop) hpt
    _ = ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ))) *
          ∫⁻ y : ℝ in {y | R ≤ |y|}, ENNReal.ofReal ((1 + |y|) ^ (-(2 : ℝ))) :=
        lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ))) * M := by
        apply mul_le_mul_right
        rw [hM]
        exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (A * (max R 1 : ℝ) ^ (-(N : ℝ)) * D) := by
        rw [← hMof, ENNReal.ofReal_mul hc0]
    _ ≤ ENNReal.ofReal ((A * D + 1) * (max R 1 : ℝ) ^ (-(N : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc A * (max R 1 : ℝ) ^ (-(N : ℝ)) * D
            = (A * D) * (max R 1 : ℝ) ^ (-(N : ℝ)) := by ring
          _ ≤ (A * D + 1) * (max R 1 : ℝ) ^ (-(N : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith) hx0

end Work.KMTAreas.A4
