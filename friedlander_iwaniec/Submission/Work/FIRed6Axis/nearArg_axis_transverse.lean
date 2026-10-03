import Mathlib
import Submission.Work.FIRed6Axis.Defs6Axis

namespace Work.FIRed6Axis

/-! ## Trigonometric core

Two elementary facts converting an angular distance from the lattice `(π/2)ℤ` into a bound on
`|sin|` resp. `|cos|`.  They are the analytic content of `nearArg_axis_transverse`: an argument
close to an *even* multiple of `π/2` has small `|sin|`, and one close to an *odd* multiple of
`π/2` has small `|cos|`. -/

/-- If `θ` is within `c` of an integer multiple of `π`, then `|sin θ| ≤ c`.
(`|sin|` has period `π`, up to sign, and `|sin x| ≤ |x|`.) -/
lemma abs_sin_le_of_dist_int_mul_pi {θ c : ℝ} {k : ℤ}
    (h : |θ - (k : ℝ) * Real.pi| ≤ c) : |Real.sin θ| ≤ c := by
  have h1 : |Real.sin θ| = |Real.sin (θ - (k : ℝ) * Real.pi)| := by
    rw [Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    simp
  rw [h1]
  exact le_trans Real.abs_sin_le_abs h

/-- If `θ` is within `c` of `π/2` modulo an integer multiple of `π`, then `|cos θ| ≤ c`. -/
lemma abs_cos_le_of_dist_int_mul_pi_add_half_pi {θ c : ℝ} {k : ℤ}
    (h : |θ - ((k : ℝ) * Real.pi + Real.pi / 2)| ≤ c) : |Real.cos θ| ≤ c := by
  have h1 : |Real.cos θ| = |Real.sin (θ - ((k : ℝ) * Real.pi + Real.pi / 2))| := by
    have he : θ - ((k : ℝ) * Real.pi + Real.pi / 2)
        = (θ - Real.pi / 2) - (k : ℝ) * Real.pi := by ring
    rw [he, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    simp [Real.sin_sub_pi_div_two]
  rw [h1]
  exact le_trans Real.abs_sin_le_abs h

/-- **The near zone is axis-aligned.**  If `arg z` is within `c` of a multiple of `π/2`
(`Work.FIRed6Axis.nearArg c z`), then one of the two coordinates of `z` is at most `c|z|`:
`|Im z| ≤ c‖z‖` or `|Re z| ≤ c‖z‖`.

Writing `m` for the relevant integer and `θ = arg z`:
* if `m` is even, `|Im z| = ‖z‖·|sin θ| = ‖z‖·|sin (θ - mπ/2)| ≤ ‖z‖·|θ - mπ/2| ≤ c‖z‖`;
* if `m` is odd, `|Re z| = ‖z‖·|cos θ| = ‖z‖·|sin (θ - mπ/2)|`, the same bound;
* if `|m| ≥ 3`, then `c ≥ |θ - mπ/2| ≥ |m|π/2 - π ≥ π/2 > 1/√2`, so `min(|Re z|,|Im z|) ≤ ‖z‖/√2 ≤ c‖z‖`.

Uses `Complex.norm_mul_sin_arg`, `Complex.norm_mul_cos_arg`, `Real.sin_sub_pi`,
`Real.abs_sin_le_abs` (cf. `Work.FITop6.Sector.arg_dist_implies_axisFree`). -/
theorem nearArg_axis_transverse {c : ℝ} (hc : 0 ≤ c) {z : GaussianInt} (h : nearArg c z) :
    |((z.im : ℤ) : ℝ)| ≤ c * ‖z.toComplex‖ ∨ |((z.re : ℤ) : ℝ)| ≤ c * ‖z.toComplex‖ := by
  obtain ⟨m, hm⟩ := h
  -- the two coordinates in polar form
  have him : |((z.im : ℤ) : ℝ)| = ‖z.toComplex‖ * |Real.sin (Complex.arg z.toComplex)| := by
    rw [GaussianInt.intCast_im, ← Complex.norm_mul_sin_arg, abs_mul,
      abs_of_nonneg (norm_nonneg _)]
  have hre : |((z.re : ℤ) : ℝ)| = ‖z.toComplex‖ * |Real.cos (Complex.arg z.toComplex)| := by
    rw [GaussianInt.intCast_re, ← Complex.norm_mul_cos_arg, abs_mul,
      abs_of_nonneg (norm_nonneg _)]
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩
  · -- `m = 2k`: the argument is close to `kπ`, so `|sin|` is small
    left
    rw [hk] at hm
    have hcast : ((2 * k : ℤ) : ℝ) * (Real.pi / 2) = (k : ℝ) * Real.pi := by
      push_cast; ring
    rw [hcast] at hm
    have hs := abs_sin_le_of_dist_int_mul_pi hm
    rw [him]
    calc ‖z.toComplex‖ * |Real.sin (Complex.arg z.toComplex)|
        ≤ ‖z.toComplex‖ * c := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = c * ‖z.toComplex‖ := by ring
  · -- `m = 2k+1`: the argument is close to `kπ + π/2`, so `|cos|` is small
    right
    rw [hk] at hm
    have hcast : ((2 * k + 1 : ℤ) : ℝ) * (Real.pi / 2) = (k : ℝ) * Real.pi + Real.pi / 2 := by
      push_cast; ring
    rw [hcast] at hm
    have hs := abs_cos_le_of_dist_int_mul_pi_add_half_pi hm
    rw [hre]
    calc ‖z.toComplex‖ * |Real.cos (Complex.arg z.toComplex)|
        ≤ ‖z.toComplex‖ * c := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = c * ‖z.toComplex‖ := by ring

end Work.FIRed6Axis
