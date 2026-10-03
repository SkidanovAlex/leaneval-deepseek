import Mathlib
import Submission.Work.FIArea3.JointCount.sharp_defs

set_option maxHeartbeats 1000000

namespace Work.FIArea3.JointCount

noncomputable section

/-! ## Diameter of an annular sector

The region `annSector a b φ Δ` is contained in the annulus `a < |z| ≤ b` and in a sector of
angular width `Δ`.  With `b = a √(1+θ)` and `Δ = 2πθ` (and `0 ≤ θ ≤ 1`) the two contributions
to the diameter add up to at most `8 θ a`: the radial thickness is at most `a θ / 2`, and two
points at the same radius with angular separation `≤ 2πθ` are at distance at most `2 b θ π`.

The proof below uses the exact formula for the squared distance in polar coordinates,
`|z - w|² = (|z| - |w|)² + 2|z||w|(1 - cos(α - β))`, and bounds `1 - cos u ≤ u²/2`
(for `θ ≤ 1/2`) resp. `1 - cos u ≤ 2` (for `θ ≥ 1/2`). -/

/-- **Squared distance in polar coordinates.**  For complex numbers `z, w` the squared distance
of `z` and `w` equals `‖z‖² + ‖w‖² - 2‖z‖‖w‖cos(arg z - arg w)`. -/
theorem norm_sub_sq_eq_arg (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * ‖z‖ * ‖w‖ *
      Real.cos (Complex.arg z - Complex.arg w) := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
      ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq (Complex.arg z), Real.sin_sq_add_cos_sq (Complex.arg w)]

/-- `√(1+θ) ≤ 1 + θ/2` for `θ ≥ 0`. -/
theorem sqrt_one_add_le_one_add_half (θ : ℝ) (hθ : 0 ≤ θ) :
    Real.sqrt (1 + θ) ≤ 1 + θ / 2 := by
  rw [Real.sqrt_le_iff]
  constructor <;> nlinarith

theorem diam_annSector_le (a θ φ : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Metric.diam (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
      ≤ 8 * θ * a := by
  have hC : 0 ≤ 8 * θ * a := by positivity
  refine Metric.diam_le_of_forall_dist_le hC ?_
  intro z hz w hw
  obtain ⟨hza, hzb, hzφ, hzφ'⟩ := hz
  obtain ⟨hwa, hwb, hwφ, hwφ'⟩ := hw
  rw [Complex.dist_eq]
  -- write `√(1+θ)` as `s`
  set s : ℝ := Real.sqrt (1 + θ) with hs_def
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hs2 : s ^ 2 = 1 + θ := by rw [hs_def]; exact Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hs_def]; rw [Real.one_le_sqrt]; linarith
  have hsle : s ≤ 1 + θ / 2 := by rw [hs_def]; exact sqrt_one_add_le_one_add_half θ hθ0
  have has0 : 0 ≤ a * s := by positivity
  -- angular separation of the two points
  have hΔ0 : 0 ≤ 2 * Real.pi * θ := by positivity
  have hδle : |Complex.arg z - Complex.arg w| ≤ 2 * Real.pi * θ := by
    rw [abs_le]
    constructor <;> linarith
  -- the polar description of the squared distance
  have hexp : ‖z - w‖ ^ 2
      = (‖z‖ - ‖w‖) ^ 2
        + 2 * ‖z‖ * ‖w‖ * (1 - Real.cos (Complex.arg z - Complex.arg w)) := by
    rw [norm_sub_sq_eq_arg]; ring
  have hcos0 : 0 ≤ 1 - Real.cos (Complex.arg z - Complex.arg w) := by
    have := Real.cos_le_one (Complex.arg z - Complex.arg w); linarith
  -- radial part
  have hrad : (‖z‖ - ‖w‖) ^ 2 ≤ (a * s - a) ^ 2 := by
    rw [sq_le_sq]
    have hba : 0 ≤ a * s - a := by nlinarith
    rw [abs_of_nonneg hba, abs_le]
    constructor <;> linarith
  -- angular part, before using a bound for `1 - cos`
  have hang : 2 * ‖z‖ * ‖w‖ * (1 - Real.cos (Complex.arg z - Complex.arg w))
      ≤ 2 * (a * s) ^ 2 * (1 - Real.cos (Complex.arg z - Complex.arg w)) := by
    have hzw : ‖z‖ * ‖w‖ ≤ (a * s) * (a * s) := by
      have h := mul_le_mul hzb hwb (norm_nonneg w) has0
      nlinarith [h]
    nlinarith [hzw, hcos0]
  rcases lt_or_ge θ (1 / 2) with hθ | hθ
  · -- ## small angular width: `1 - cos u ≤ u²/2 ≤ 2π²θ²`
    have hcos : 1 - Real.cos (Complex.arg z - Complex.arg w)
        ≤ (Complex.arg z - Complex.arg w) ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := Complex.arg z - Complex.arg w); linarith
    have hδsq : (Complex.arg z - Complex.arg w) ^ 2 ≤ (2 * Real.pi * θ) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rwa [abs_of_nonneg hΔ0]
    have hang2 : 2 * (a * s) ^ 2 * (1 - Real.cos (Complex.arg z - Complex.arg w))
        ≤ (a * s) ^ 2 * (2 * Real.pi * θ) ^ 2 := by
      have h34 : 1 - Real.cos (Complex.arg z - Complex.arg w)
          ≤ (2 * Real.pi * θ) ^ 2 / 2 := by linarith
      nlinarith [h34, sq_nonneg (a * s)]
    have hkey : Real.pi ^ 2 * (1 + θ) ≤ 15 := by
      have h1 : Real.pi ^ 2 * (1 + θ) ≤ 10 * (1 + θ) :=
        mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_lt_d4, Real.pi_pos]) (by linarith)
      linarith
    have hnum : (a * s - a) ^ 2 + (a * s) ^ 2 * (2 * Real.pi * θ) ^ 2
        ≤ 64 * θ ^ 2 * a ^ 2 := by
      have hrad' : (a * s - a) ^ 2 ≤ a ^ 2 * θ ^ 2 / 4 := by
        have e : (a * s - a) ^ 2 = a ^ 2 * (s - 1) ^ 2 := by ring
        rw [e]
        have h : (s - 1) ^ 2 ≤ θ ^ 2 / 4 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ a ^ 2)]
      have hang' : (a * s) ^ 2 * (2 * Real.pi * θ) ^ 2 ≤ 60 * θ ^ 2 * a ^ 2 := by
        have e : (a * s) ^ 2 * (2 * Real.pi * θ) ^ 2
            = 4 * (Real.pi ^ 2 * (1 + θ)) * (θ ^ 2 * a ^ 2) := by rw [mul_pow, hs2]; ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ θ ^ 2 * a ^ 2)]
      nlinarith [hrad', hang', sq_nonneg θ, sq_nonneg a]
    have hsq : ‖z - w‖ ^ 2 ≤ (8 * θ * a) ^ 2 := by
      calc ‖z - w‖ ^ 2
          = (‖z‖ - ‖w‖) ^ 2
            + 2 * ‖z‖ * ‖w‖ * (1 - Real.cos (Complex.arg z - Complex.arg w)) := hexp
        _ ≤ (a * s - a) ^ 2 + (a * s) ^ 2 * (2 * Real.pi * θ) ^ 2 := by linarith
        _ ≤ 64 * θ ^ 2 * a ^ 2 := hnum
        _ = (8 * θ * a) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hC] at hsqrt
  · -- ## wide angular width: `1 - cos u ≤ 2`
    have hθ' : 1 / 2 ≤ θ := hθ
    have hcos : 1 - Real.cos (Complex.arg z - Complex.arg w) ≤ 2 := by
      have := Real.neg_one_le_cos (Complex.arg z - Complex.arg w); linarith
    have hang2 : 2 * (a * s) ^ 2 * (1 - Real.cos (Complex.arg z - Complex.arg w))
        ≤ 4 * (a * s) ^ 2 := by nlinarith [hcos, sq_nonneg (a * s)]
    have hnum : (a * s - a) ^ 2 + 4 * (a * s) ^ 2 ≤ 64 * θ ^ 2 * a ^ 2 := by
      have hrad' : (a * s - a) ^ 2 ≤ a ^ 2 / 4 := by
        have e : (a * s - a) ^ 2 = a ^ 2 * (s - 1) ^ 2 := by ring
        rw [e]
        have h : (s - 1) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ a ^ 2)]
      have hang' : 4 * (a * s) ^ 2 ≤ 8 * a ^ 2 := by
        have e : 4 * (a * s) ^ 2 = 4 * a ^ 2 * (1 + θ) := by rw [mul_pow, hs2]; ring
        rw [e]; nlinarith
      have hθsq : (1 / 4 : ℝ) ≤ θ ^ 2 := by nlinarith
      nlinarith [sq_nonneg a]
    have hsq : ‖z - w‖ ^ 2 ≤ (8 * θ * a) ^ 2 := by
      calc ‖z - w‖ ^ 2
          = (‖z‖ - ‖w‖) ^ 2
            + 2 * ‖z‖ * ‖w‖ * (1 - Real.cos (Complex.arg z - Complex.arg w)) := hexp
        _ ≤ (a * s - a) ^ 2 + 4 * (a * s) ^ 2 := by linarith
        _ ≤ 64 * θ ^ 2 * a ^ 2 := hnum
        _ = (8 * θ * a) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hC] at hsqrt

end

end Work.FIArea3.JointCount
