import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

/-!
# The level scale `c_n` and the fundamental bump transform `rho` of the MST level bump

`Work.BourgainPlan.Maximal.mstEta d χ η n` is the level bump `ξ ↦ η (c_n · iwRep ξ)` with the level
scale `c_n = 2^{n (d − χ)}`.  This file fixes the two objects the `ℓ¹` estimate for its Fourier
coefficients is phrased in terms of:

* `mstScale d χ n = 2^{n (d − χ)}` — the level scale (`≥ 1` as soon as `χ + 1 ≤ d`);
* `mstHat η t = ∫_{−1/2}^{1/2} η u · e^{−2 π i t u} du` — the `ℝ`-Fourier transform of the fixed
  bump `η` in the period-`1` convention.

The dilation `x = u / c_n` in the coefficient integral gives the dictionary

`fourierCoeff (mstEta d χ η n) m = c_n⁻¹ · mstHat η (m / c_n)`
(`Work.BourgainPlan.Maximal.fourierCoeff_mstEta`), and all the analysis is then done on the single
scale-free function `mstHat`: it is bounded by `M` when `η` is (`mstHat_bound`), and it decays like
`t⁻²` when the fundamental-domain lift of `η` is `C²` (`mstHat_decay`).
-/

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- The MST level scale `c_n = 2^{n (d − χ)}`. -/
def mstScale (d : ℕ) (χ : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ))

/-- The `ℝ`-Fourier transform of the MST bump `η` in the period-`1` convention,
`mstHat η t = ∫_{−1/2}^{1/2} η u · e^{−2 π i t u} du` (the integral is over the fundamental
interval; no support hypothesis on `η` is needed for the definition). -/
def mstHat (η : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u in (-(1/2))..(1/2), η u * Complex.exp ((((-(2 * Real.pi * t * u)) : ℝ) : ℂ) * Complex.I)

@[simp] lemma mstScale_apply (d : ℕ) (χ : ℝ) (n : ℕ) :
    mstScale d χ n = (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) := rfl

@[simp] lemma mstHat_apply (η : ℝ → ℂ) (t : ℝ) :
    mstHat η t
      = ∫ u in (-(1/2))..(1/2), η u * Complex.exp ((((-(2 * Real.pi * t * u)) : ℝ) : ℂ) * Complex.I) :=
  rfl

lemma mstScale_pos (d : ℕ) (χ : ℝ) (n : ℕ) : 0 < mstScale d χ n :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma mstScale_ne_zero (d : ℕ) (χ : ℝ) (n : ℕ) : mstScale d χ n ≠ 0 :=
  (mstScale_pos d χ n).ne'

/-- The hypothesis `χ + 1 ≤ d` makes the level scale at least `1` (and hence the level bump
`η(c_n ·)` no wider than the fundamental interval). -/
lemma one_le_mstScale {d : ℕ} {χ : ℝ} (hχ : χ + 1 ≤ (d : ℝ)) (n : ℕ) : 1 ≤ mstScale d χ n := by
  have hd : (0 : ℝ) ≤ (d : ℝ) - χ := by linarith
  have hexp : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) - χ) := mul_nonneg (Nat.cast_nonneg n) hd
  have h2 : (1 : ℝ) ≤ 2 := by norm_num
  exact Real.one_le_rpow h2 hexp

end

end Work.BourgainPlan.Maximal
