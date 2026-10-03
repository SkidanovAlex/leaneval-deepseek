import Mathlib
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.logFac_sin

namespace Work.FIArea4

open Work.FIPlan

/-- `θ ≤ 1/8` for every admissible set-up: `θ = (log x)^{-A'}` with `A' ≥ 2^20 ≥ 32` and
`log x ≥ log 3 > 1.09`, so `θ ≤ 1.09^{-32} < 1/8`. -/
lemma theta_le_eighth (Pa : Work.FITop.Params) : Pa.θ ≤ 1 / 8 := by
  have ht1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := le_of_lt (Work.FIArea4.log_x_gt_one Pa)
  have ht09 : (1.09 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h3x : Real.log 3 ≤ Real.log (Pa.x : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast Pa.hx)
    linarith [Real.log_three_gt_d9]
  have hA'32 : (32 : ℝ) ≤ Pa.A' := by
    have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by nlinarith [Pa.hA', Pa.hA]
    norm_num at h; linarith
  have hlogx_pos : 0 < Real.log (Pa.x : ℝ) := by linarith
  rw [Pa.hθ]
  have hle1 : (Real.log (Pa.x : ℝ)) ^ (-Pa.A') ≤ (Real.log (Pa.x : ℝ)) ^ (-(32 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hpow8 : (8 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ (32 : ℕ) := by
    have h109 : (8 : ℝ) ≤ (1.09 : ℝ) ^ (32 : ℕ) := by norm_num
    have hmono : (1.09 : ℝ) ^ (32 : ℕ) ≤ (Real.log (Pa.x : ℝ)) ^ (32 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) ht09 32
    linarith
  have hle2 : (Real.log (Pa.x : ℝ)) ^ (-(32 : ℝ)) ≤ (8 : ℝ)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hlogx_pos)]
    have h32 : (Real.log (Pa.x : ℝ)) ^ (32 : ℝ) = (Real.log (Pa.x : ℝ)) ^ (32 : ℕ) :=
      Real.rpow_natCast _ 32
    rw [h32]
    exact (inv_le_inv₀ (pow_pos hlogx_pos 32) (by norm_num)).mpr hpow8
  calc (Real.log (Pa.x : ℝ)) ^ (-Pa.A') ≤ (Real.log (Pa.x : ℝ)) ^ (-(32 : ℝ)) := hle1
    _ ≤ (8 : ℝ)⁻¹ := hle2
    _ = 1 / 8 := by norm_num

/-- `2πθ ≤ 1` for every admissible set-up (with room to spare): `θ ≤ 1/8` and `π ≤ 4`. -/
lemma two_pi_theta_le_one (Pa : Work.FITop.Params) : 2 * Real.pi * Pa.θ ≤ 1 := by
  have hθ : Pa.θ ≤ 1 / 8 := theta_le_eighth Pa
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have h1 : Real.pi * Pa.θ ≤ 4 * (1 / 8) := by
    calc Real.pi * Pa.θ ≤ 4 * Pa.θ := mul_le_mul_of_nonneg_right hπ hθ0
      _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hθ (by norm_num)
  nlinarith [h1]

/-- **The angular separation of two points of the polar box.**  If `z₁, z₂` lie in the same polar
box (5.14) and `4dX < |Δ(z₁,z₂)|` with `d, X ≥ 1`, then their principal arguments differ by
between `2/N` and `1`.

The upper bound is the box itself: both arguments lie in the interval `(φ, φ + 2πθ]` of length
`2πθ ≤ 1`.  The lower bound uses `|Δ| = |z₁||z₂|·|sin(α₂-α₁)|`, the box bound `|zᵢ| ≤ √((1+θ)N)`,
the cut `|Δ| > 4dX ≥ 4` and `|sin u| ≤ |u|`: `|α₂-α₁| ≥ |sin(α₂-α₁)| > 4/((1+θ)N) ≥ 2/N`
as `θ ≤ 1`. -/
theorem arg_sub_bounds (Pa : Work.FITop.Params) (φ : ℝ) (X d : ℕ) (hX : 1 ≤ X) (hd : 1 ≤ d)
    {z1 z2 : GaussianInt} (h1 : Work.FITop3.InPolarBox Pa φ z1)
    (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hcut : 4 * d * X < Work.FIPlan.absDelta z1 z2) :
    2 / (Pa.N : ℝ) ≤ |Complex.arg z2.toComplex - Complex.arg z1.toComplex| ∧
      |Complex.arg z2.toComplex - Complex.arg z1.toComplex| ≤ 1 := by
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hπθ : 2 * Real.pi * Pa.θ ≤ 1 := two_pi_theta_le_one Pa
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hDpos : 0 < (1 + Pa.θ) * Pa.N := by
    have : 0 < 1 + Pa.θ := by linarith [Pa.hθ0]
    positivity
  -- norms of the two points
  have hgn1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h1.2.2.1
  have hgn2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h2.2.2.1
  have hs1 : ‖z1.toComplex‖ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    rw [← Work.FIArea4.sqrt_gnorm z1]; exact Real.sqrt_le_sqrt hgn1
  have hs2 : ‖z2.toComplex‖ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    rw [← Work.FIArea4.sqrt_gnorm z2]; exact Real.sqrt_le_sqrt hgn2
  have hprod : ‖z1.toComplex‖ * ‖z2.toComplex‖ ≤ (1 + Pa.θ) * Pa.N := by
    have hsq : Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N)
        = (1 + Pa.θ) * Pa.N := by
      rw [← sq, Real.sq_sqrt (le_of_lt hDpos)]
    calc ‖z1.toComplex‖ * ‖z2.toComplex‖
        ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N) :=
          mul_le_mul hs1 hs2 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = (1 + Pa.θ) * Pa.N := hsq
  have hz1pos : 0 < ‖z1.toComplex‖ := by
    rw [← Work.FIArea4.sqrt_gnorm z1]
    exact Real.sqrt_pos.mpr (by linarith [h1.2.1, hN1])
  have hz2pos : 0 < ‖z2.toComplex‖ := by
    rw [← Work.FIArea4.sqrt_gnorm z2]
    exact Real.sqrt_pos.mpr (by linarith [h2.2.1, hN1])
  -- the determinant identity
  have hDelta : (Work.FIPlan.Delta z1 z2 : ℝ)
      = ‖z1.toComplex‖ * ‖z2.toComplex‖
        * Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex) := by
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
        GaussianInt.toComplex_star]
    exact Work.FIArea4.im_starRingEnd_mul z1.toComplex z2.toComplex
  have habs : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = ‖z1.toComplex‖ * ‖z2.toComplex‖
        * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs, hDelta,
        abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  -- the cut forces `|Δ| > 4`
  have hA_gt4 : (4 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    have hcast : ((4 * d * X : ℕ) : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      exact_mod_cast hcut
    have h4 : (4 : ℝ) ≤ 4 * (d : ℝ) * (X : ℝ) := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      nlinarith [hd1, hX1]
    have hcast' : ((4 * d * X : ℕ) : ℝ) = 4 * (d : ℝ) * (X : ℝ) := by push_cast; ring
    rw [hcast'] at hcast
    linarith
  -- `|sin| ≥ |Δ|/((1+θ)N)`
  have hsin_ge : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) / ((1 + Pa.θ) * Pa.N)
      ≤ |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| := by
    rw [habs, div_le_iff₀ hDpos]
    have hcomm : ‖z1.toComplex‖ * ‖z2.toComplex‖
          * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|
        = |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|
          * (‖z1.toComplex‖ * ‖z2.toComplex‖) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_left hprod
      (abs_nonneg (Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
  have hsin_gt : (4 : ℝ) / ((1 + Pa.θ) * Pa.N)
      < |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| :=
    lt_of_lt_of_le (div_lt_div_of_pos_right hA_gt4 hDpos) hsin_ge
  -- `4/((1+θ)N) ≥ 2/N`
  have hfour : (2 : ℝ) / Pa.N ≤ 4 / ((1 + Pa.θ) * Pa.N) := by
    rw [le_div_iff₀ hDpos]
    have heq : (2 : ℝ) / Pa.N * ((1 + Pa.θ) * Pa.N) = 2 * (1 + Pa.θ) := by
      field_simp
    rw [heq]
    linarith
  refine ⟨?_, ?_⟩
  · -- lower bound
    have hsin_le := Real.abs_sin_le_abs (x := Complex.arg z2.toComplex - Complex.arg z1.toComplex)
    linarith
  · -- upper bound
    have hlt : |Complex.arg z2.toComplex - Complex.arg z1.toComplex| < 2 * Real.pi * Pa.θ := by
      rw [abs_lt]
      constructor <;> linarith [h1.2.2.2.1, h1.2.2.2.2, h2.2.2.2.1, h2.2.2.2.2]
    linarith

end Work.FIArea4
