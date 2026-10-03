import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FITop6.Sector.TrigAux.abs_cos_gt_of_arg_dist

namespace Work.FITop6.Sector

/-- **Angular distance from the axes forces axis-freedom.**

If `|z|² = gnorm z` exceeds the inner scale `Pa.N`, and the argument of `z` is at angular
distance `> πϑ/2` from every multiple of `π/2` (the paper's §5 exclusion, weakened by the
factor `2` used in `Work.FITop6.Sector.sector_free_arg_dist`), then `z` is axis-free at the
sector-scale threshold `ϑ√N`:

`|Re z| = |z|·|cos (arg z)| > ϑ·√N`,  `|Im z| = |z|·|sin (arg z)| > ϑ·√N`.

The only analytic input is that an angle at distance `> πϑ/2` from `(π/2)ℤ` satisfies
`|cos| > ϑ` and `|sin| > ϑ`; the rest is `‖z‖ = √(|z|²)`. -/
theorem arg_dist_implies_axisFree {Pa : Work.FITop.Params} {z : GaussianInt}
    (hN : Pa.N < (Work.FIPlan.gnorm z : ℝ))
    (harg : ∀ m : ℤ, Real.pi * Pa.ϑ / 2 < |Complex.arg z.toComplex - (m : ℝ) * (Real.pi / 2)|)
    (hϑ : Pa.ϑ ≤ 1) :
    Work.FITop4.IsAxisFree Pa z := by
  -- `‖z‖² = |z|² = gnorm z`
  have hNsq : Pa.N < ‖z.toComplex‖ ^ 2 := by
    rw [Work.FIArea4.normSq_toComplex_gnorm z]; exact hN
  -- `‖z‖ > 0`, hence `√N < ‖z‖`
  have hnorm_sq_pos : 0 < ‖z.toComplex‖ ^ 2 := by
    linarith [Pa.hN1, hNsq]
  have hznorm_pos : 0 < ‖z.toComplex‖ := by
    have hne : ‖z.toComplex‖ ≠ 0 := sq_pos_iff.mp hnorm_sq_pos
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hsqrt_lt : Real.sqrt Pa.N < ‖z.toComplex‖ :=
    (Real.sqrt_lt' hznorm_pos).2 hNsq
  -- the two angular facts: `arg z` is at distance `> πϑ/2 > 0` from `(π/2)ℤ`, so `|cos|` and
  -- `|sin|` both exceed `ϑ`
  have hcos : Pa.ϑ < |Real.cos (Complex.arg z.toComplex)| :=
    Work.FITop6.Sector.TrigAux.abs_cos_gt_of_arg_dist harg
  have hsin : Pa.ϑ < |Real.sin (Complex.arg z.toComplex)| := by
    -- `|sin φ| = |cos (φ - π/2)|`, and the hypothesis is invariant under `φ ↦ φ - π/2`
    have h' : ∀ m : ℤ, Real.pi * Pa.ϑ / 2 <
        |(Complex.arg z.toComplex - Real.pi / 2) - (m : ℝ) * (Real.pi / 2)| := by
      intro m
      have h1 := harg (m + 1)
      have he : Complex.arg z.toComplex - Real.pi / 2 - (m : ℝ) * (Real.pi / 2) =
          Complex.arg z.toComplex - (((m + 1 : ℤ)) : ℝ) * (Real.pi / 2) := by
        push_cast; ring
      rwa [he]
    have h2 := Work.FITop6.Sector.TrigAux.abs_cos_gt_of_arg_dist h'
    rwa [Real.cos_sub_pi_div_two] at h2
  -- `|Re z| = ‖z‖·|cos arg z|`, `|Im z| = ‖z‖·|sin arg z|`
  have hre : |(z.re : ℝ)| = ‖z.toComplex‖ * |Real.cos (Complex.arg z.toComplex)| := by
    rw [GaussianInt.intCast_re, ← Complex.norm_mul_cos_arg, abs_mul,
      abs_of_nonneg (norm_nonneg _)]
  have him : |(z.im : ℝ)| = ‖z.toComplex‖ * |Real.sin (Complex.arg z.toComplex)| := by
    rw [GaussianInt.intCast_im, ← Complex.norm_mul_sin_arg, abs_mul,
      abs_of_nonneg (norm_nonneg _)]
  constructor
  · calc Pa.ϑ * Real.sqrt Pa.N < Pa.ϑ * ‖z.toComplex‖ :=
          mul_lt_mul_of_pos_left hsqrt_lt Pa.hϑ0
      _ < |Real.cos (Complex.arg z.toComplex)| * ‖z.toComplex‖ :=
          mul_lt_mul_of_pos_right hcos hznorm_pos
      _ = |(z.re : ℝ)| := by rw [hre]; ring
  · calc Pa.ϑ * Real.sqrt Pa.N < Pa.ϑ * ‖z.toComplex‖ :=
          mul_lt_mul_of_pos_left hsqrt_lt Pa.hϑ0
      _ < |Real.sin (Complex.arg z.toComplex)| * ‖z.toComplex‖ :=
          mul_lt_mul_of_pos_right hsin hznorm_pos
      _ = |(z.im : ℝ)| := by rw [him]; ring

end Work.FITop6.Sector
