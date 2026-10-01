import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs

namespace Work.ZeroDensity.Ingham

open Work.ZeroDensity.Ingham
open Complex MeasureTheory Set
open scoped Topology BigOperators Real

/-- The completed `Γ`-factor `Γℝ` commutes with complex conjugation:
`Γℝ (conj z) = conj (Γℝ z)`.  Indeed `Γℝ s = π ^ (-s/2) * Γ (s/2)`, and both factors
are manifestly conjugation-equivariant (`cpow_conj` for the base `π > 0`, and
`Complex.Gamma_conj`). -/
lemma Gammaℝ_conj (s : ℂ) : Gammaℝ (star s) = star (Gammaℝ s) := by
  have harg : (π : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
    exact Real.pi_ne_zero.symm
  have hpow : (π : ℂ) ^ (-(star s) / 2) = star ((π : ℂ) ^ (-s / 2)) := by
    have h := Complex.cpow_conj (π : ℂ) (-s / 2) harg
    simpa [Complex.conj_ofReal, map_div₀, map_neg, map_ofNat] using h
  have hdiv : star s / 2 = star (s / 2) := by simp
  have hGam : Gamma (star (s / 2)) = star (Gamma (s / 2)) := Complex.Gamma_conj (s / 2)
  calc Gammaℝ (star s) = (π : ℂ) ^ (-(star s) / 2) * Gamma (star s / 2) := by
        rw [Gammaℝ_def]
    _ = (π : ℂ) ^ (-(star s) / 2) * Gamma (star (s / 2)) := by rw [hdiv]
    _ = star ((π : ℂ) ^ (-s / 2)) * star (Gamma (s / 2)) := by rw [hpow, hGam]
    _ = star ((π : ℂ) ^ (-s / 2) * Gamma (s / 2)) := by rw [star_mul, mul_comm]
    _ = star (Gammaℝ s) := by rw [Gammaℝ_def]

/-- The root-number factor `χ(z) = Γℝ(1-z)/Γℝ z` has modulus one on the critical line:
`‖χ(1/2 + iT)‖ = 1`.  (Indeed `1 - z = conj z` there and `Γℝ(conj w) = conj (Γℝ w)`.) -/
theorem norm_zetaChi_critical (T : ℝ) :
    ‖zetaChi ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ = 1 := by
  have hconj : (1 : ℂ) - ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) =
      star ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) := by
    simp; ring
  have hne : Gammaℝ ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  have hnorm : ‖star (Gammaℝ ((1 / 2 : ℂ) + (T : ℂ) * Complex.I))‖ =
      ‖Gammaℝ ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ := Complex.norm_conj _
  rw [zetaChi, hconj, Gammaℝ_conj, norm_div, hnorm,
    div_self (norm_ne_zero_iff.mpr hne)]

end Work.ZeroDensity.Ingham
