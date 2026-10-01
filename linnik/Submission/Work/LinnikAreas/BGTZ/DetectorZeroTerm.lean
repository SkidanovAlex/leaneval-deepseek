import Mathlib

open MeasureTheory

namespace Work.LinnikAreas.BGTZ

/-- The `n = 0` summand of the BGTZ detector series is integrable along the vertical line
`Re s = c`; `0 ^ z` is `0` for `z ≠ 0` and `1` for `z = 0`, so the summand vanishes except at
the single point where the exponent `ρ + (c + i t)` is zero. -/
lemma DetectorZeroTerm {c : ℝ} (hc : 0 < c) (ρ : ℂ) {N : ℕ} (hN : 0 < N) (f : ℕ → ℂ)
    (hK : MeasureTheory.Integrable (fun t : ℝ => ‖(N : ℂ) ^ (c + t * Complex.I) /
      ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖)) :
    MeasureTheory.Integrable (fun t : ℝ => (f 0 / (0 : ℂ) ^ (ρ + (c + t * Complex.I))) *
      ((N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I)))) := by
  -- The exponent `ρ + (c + t*I)` vanishes for at most one `t`, namely `t = (-ρ).im`.
  have hS : volume {t : ℝ | ρ + (c + t * Complex.I) = 0} = 0 := by
    apply measure_mono_null _ (measure_singleton (-ρ).im)
    intro t ht
    have h1 : (c : ℂ) + (t : ℂ) * Complex.I = -ρ := eq_neg_of_add_eq_zero_right ht
    have h2 := congrArg Complex.im h1
    simpa using h2
  -- hence the exponent is a.e. nonzero
  have hae : ∀ᵐ t : ℝ, ρ + (c + t * Complex.I) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using hS
  -- and the whole summand is a.e. zero
  have hge : (fun t : ℝ => (f 0 / (0 : ℂ) ^ (ρ + (c + t * Complex.I))) *
      ((N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I))))
      =ᵐ[volume] 0 := by
    filter_upwards [hae] with t ht
    rw [Complex.zero_cpow ht]
    simp
  exact (MeasureTheory.integrable_zero ℝ ℂ volume).congr hge.symm

end Work.LinnikAreas.BGTZ
