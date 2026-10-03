import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea3.logFac_le

namespace Work.FIArea3

/-! ### Elementary complex-analytic and geometric helpers

The counting ingredient of *FI* Lemma 10.1 rests on a purely geometric fact: the polar box
(5.14) is an annulus sector of angular width `2πθ` and of outer radius `≤ √((1+θ)N)`, so two of
its points are at distance `< √N`.  We prove this here, together with the two elementary
lemmas it needs:

* `norm_exp_mul_I_sub_one_le`: `‖exp(iδ) - 1‖ ≤ |δ|` (`= 2|sin(δ/2)| ≤ |δ|`);
* `norm_sub_le_arg`: the "polar" triangle inequality
  `‖u - v‖ ≤ |‖u‖ - ‖v‖| + ‖v‖ · |arg u - arg v|`, which turns the angular width of the sector
  and the radial width of the annulus into a distance bound.
-/

/-- `‖exp(i x) - 1‖ ≤ |x|`.  Indeed `‖exp(ix) - 1‖ = ‖2 sin(x/2)‖ = 2|sin(x/2)| ≤ |x|`. -/
lemma norm_exp_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have h1 : (x : ℂ) * Complex.I = Complex.I * (x : ℂ) := mul_comm _ _
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : |Real.sin (x / 2)| ≤ |x| / 2 := by
    have := Real.abs_sin_le_abs (x := x / 2)
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at this
    linarith
  linarith

/-- **The polar triangle inequality.**  Writing `u = ‖u‖ exp(i arg u)`,
`v = ‖v‖ exp(i arg v)`,
`u - v = (‖u‖ - ‖v‖) exp(i arg u) + ‖v‖ (exp(i arg u) - exp(i arg v))`, and the second factor is
`‖exp(i(arg u - arg v)) - 1‖ ≤ |arg u - arg v|`. -/
lemma norm_sub_le_arg (u v : ℂ) :
    ‖u - v‖ ≤ |‖u‖ - ‖v‖| + ‖v‖ * |Complex.arg u - Complex.arg v| := by
  have hu : (‖u‖ : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I) = u :=
    Complex.norm_mul_exp_arg_mul_I u
  have hv : (‖v‖ : ℂ) * Complex.exp ((Complex.arg v : ℂ) * Complex.I) = v :=
    Complex.norm_mul_exp_arg_mul_I v
  have key : u - v = (((‖u‖ - ‖v‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I)
      + (‖v‖ : ℂ) * (Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          - Complex.exp ((Complex.arg v : ℂ) * Complex.I)) := by
    conv_lhs => rw [← hu, ← hv]
    push_cast
    ring
  have h1 : ‖(((‖u‖ - ‖v‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I)‖
      = |‖u‖ - ‖v‖| := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(‖v‖ : ℂ) * (Complex.exp ((Complex.arg u : ℂ) * Complex.I)
        - Complex.exp ((Complex.arg v : ℂ) * Complex.I))‖
      = ‖v‖ * ‖Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          - Complex.exp ((Complex.arg v : ℂ) * Complex.I)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hB : ‖Complex.exp ((Complex.arg u : ℂ) * Complex.I)
        - Complex.exp ((Complex.arg v : ℂ) * Complex.I)‖ ≤ |Complex.arg u - Complex.arg v| := by
    have h2' : Complex.exp ((Complex.arg u : ℂ) * Complex.I)
        = Complex.exp ((Complex.arg v : ℂ) * Complex.I)
          * Complex.exp (((Complex.arg u - Complex.arg v : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfac : Complex.exp ((Complex.arg v : ℂ) * Complex.I)
          * Complex.exp (((Complex.arg u - Complex.arg v : ℝ) : ℂ) * Complex.I)
          - Complex.exp ((Complex.arg v : ℂ) * Complex.I)
        = Complex.exp ((Complex.arg v : ℂ) * Complex.I)
          * (Complex.exp (((Complex.arg u - Complex.arg v : ℝ) : ℂ) * Complex.I) - 1) := by ring
    rw [h2', hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_exp_mul_I_sub_one_le _
  rw [key]
  calc ‖(((‖u‖ - ‖v‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          + (‖v‖ : ℂ) * (Complex.exp ((Complex.arg u : ℂ) * Complex.I)
              - Complex.exp ((Complex.arg v : ℂ) * Complex.I))‖
      ≤ ‖(((‖u‖ - ‖v‖ : ℝ)) : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I)‖
        + ‖(‖v‖ : ℂ) * (Complex.exp ((Complex.arg u : ℂ) * Complex.I)
            - Complex.exp ((Complex.arg v : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = |‖u‖ - ‖v‖| + ‖v‖ * ‖Complex.exp ((Complex.arg u : ℂ) * Complex.I)
          - Complex.exp ((Complex.arg v : ℂ) * Complex.I)‖ := by rw [h1, h2]
    _ ≤ |‖u‖ - ‖v‖| + ‖v‖ * |Complex.arg u - Complex.arg v| := by
        have := mul_le_mul_of_nonneg_left hB (norm_nonneg v)
        linarith

/-- `|z|² = ‖z.toComplex‖²` for a Gaussian integer (`gnorm z` is the square of the complex
modulus of `z`). -/
lemma gnorm_eq_normSq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = Complex.normSq (z : ℂ) := by
  simp [Work.FIPlan.gnorm]

/-- **Two points of the polar box are at distance `< √N`.**  Both `z`, `z'` lie in the annulus
`√N < |·| ≤ √((1+θ)N)`, so their moduli differ by at most `√N·θ`, and their arguments differ by
at most `2πθ ≤ 8θ` (as `π < 4`); the polar triangle inequality gives
`|z - z'| ≤ √N·θ + (11/10)√N·8θ = 9.8 θ√N ≤ 0.98√N < √N` (using `θ ≤ 1/10`). -/
lemma polar_box_dist {Pa : Work.FITop.Params} {φ : ℝ} {z z' : GaussianInt}
    (h : Work.FITop3.InPolarBox Pa φ z) (h' : Work.FITop3.InPolarBox Pa φ z') :
    ‖(z : ℂ) - (z' : ℂ)‖ < Real.sqrt Pa.N := by
  obtain ⟨-, hzlo, hzhi, hza, hzb⟩ := h
  obtain ⟨-, hz'lo, hz'hi, hz'a, hz'b⟩ := h'
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  set r : ℝ := Real.sqrt Pa.N with hr
  have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hNpos
  have hnormz : ‖(z : ℂ)‖ ^ 2 = (Work.FIPlan.gnorm z : ℝ) := by
    rw [Complex.sq_norm, ← gnorm_eq_normSq]
  have hnormz' : ‖(z' : ℂ)‖ ^ 2 = (Work.FIPlan.gnorm z' : ℝ) := by
    rw [Complex.sq_norm, ← gnorm_eq_normSq]
  have hzpos : 0 < ‖(z : ℂ)‖ := by
    have hpos : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
    nlinarith [norm_nonneg (z : ℂ), hnormz]
  have hz'pos : 0 < ‖(z' : ℂ)‖ := by
    have hpos : (0 : ℝ) < (Work.FIPlan.gnorm z' : ℝ) := by linarith
    nlinarith [norm_nonneg (z' : ℂ), hnormz']
  have hzr : r < ‖(z : ℂ)‖ := by
    rw [hr, Real.sqrt_lt' hzpos, hnormz]
    exact hzlo
  have hz'r : r < ‖(z' : ℂ)‖ := by
    rw [hr, Real.sqrt_lt' hz'pos, hnormz']
    exact hz'lo
  have hzup : ‖(z : ℂ)‖ ≤ Real.sqrt (1 + Pa.θ) * r := by
    rw [hr, ← Real.sqrt_mul (by linarith [Pa.hθ0] : (0:ℝ) ≤ 1 + Pa.θ)]
    rw [← Real.sqrt_sq (norm_nonneg (z : ℂ)), hnormz]
    exact Real.sqrt_le_sqrt hzhi
  have hz'up : ‖(z' : ℂ)‖ ≤ Real.sqrt (1 + Pa.θ) * r := by
    rw [hr, ← Real.sqrt_mul (by linarith [Pa.hθ0] : (0:ℝ) ≤ 1 + Pa.θ)]
    rw [← Real.sqrt_sq (norm_nonneg (z' : ℂ)), hnormz']
    exact Real.sqrt_le_sqrt hz'hi
  have hs : Real.sqrt (1 + Pa.θ) ≤ 1 + Pa.θ := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith [Pa.hθ0], by nlinarith [Pa.hθ0]⟩
  have hdiff : |‖(z : ℂ)‖ - ‖(z' : ℂ)‖| ≤ r * Pa.θ := by
    have hle : |‖(z : ℂ)‖ - ‖(z' : ℂ)‖| ≤ Real.sqrt (1 + Pa.θ) * r - r :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    calc |‖(z : ℂ)‖ - ‖(z' : ℂ)‖| ≤ Real.sqrt (1 + Pa.θ) * r - r := hle
      _ = r * (Real.sqrt (1 + Pa.θ) - 1) := by ring
      _ ≤ r * Pa.θ := by nlinarith [hrpos, hs]
  have harg : |Complex.arg (z : ℂ) - Complex.arg (z' : ℂ)| ≤ 8 * Pa.θ := by
    have hlt : |Complex.arg (z : ℂ) - Complex.arg (z' : ℂ)| < 2 * Real.pi * Pa.θ :=
      abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have hpi : 2 * Real.pi * Pa.θ ≤ 8 * Pa.θ := by nlinarith [Real.pi_lt_four, Pa.hθ0]
    linarith
  have hvup : ‖(z' : ℂ)‖ ≤ (11/10) * r := by
    have hs' : Real.sqrt (1 + Pa.θ) ≤ 11/10 := by linarith [hs, theta_le_tenth Pa]
    calc ‖(z' : ℂ)‖ ≤ Real.sqrt (1 + Pa.θ) * r := hz'up
      _ ≤ (11/10) * r := mul_le_mul_of_nonneg_right hs' hrpos.le
  have hmain := norm_sub_le_arg (z : ℂ) (z' : ℂ)
  have hfin : ‖(z : ℂ) - (z' : ℂ)‖ < r := by
    have hb : ‖(z' : ℂ)‖ * |Complex.arg (z : ℂ) - Complex.arg (z' : ℂ)| ≤ (11/10) * r * (8 * Pa.θ) :=
      mul_le_mul hvup harg (abs_nonneg _) (by positivity)
    have hstep : ‖(z : ℂ) - (z' : ℂ)‖ ≤ r * Pa.θ + (11/10) * r * (8 * Pa.θ) := by
      linarith [hmain, hdiff, hb]
    have : r * Pa.θ + (11/10) * r * (8 * Pa.θ) < r := by
      nlinarith [hrpos, Pa.hθ0, theta_le_tenth Pa]
    linarith
  exact hfin

/-- **The fibre of the sesquilinear form `Δ(z₁,·) = Im(z̄₁·)` over the polar box is a singleton.**
If `z₁` is primitive with `|z₁|² > N` and `z₂, z₂'` both lie in the polar box (5.14), then
`Im(z̄₁z₂) = Im(z̄₁z₂')` forces `z₂ = z₂'`.

Proof: the solutions of `Im(z̄₁w) = δ` form a coset of `ℤz₁`; since `z₁` is primitive, the
difference `z₂ − z₂'` is an *integer* multiple of `z₁`, so either it vanishes or
`|z₂−z₂'| ≥ |z₁| > √N`; but two points of the polar box are at distance `≤ 9θ√N < √N` (the sector
has width `2πθ` and `Params` forces `θ ≤ 1/10`, e.g. via `theta_le_tenth`).

This is the elementary counting ingredient of *FI* Lemma 10.1: it makes the map
`z₂ ↦ Δ(z₁,z₂)` injective on the box, i.e. every value of `Δ` is attained `≤ 1` time per `z₁`. -/
theorem delta_fibre_injective {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 z2' : GaussianInt}
    (hz1n : (Pa.N : ℝ) < (Work.FIPlan.gnorm z1 : ℝ)) (hz1p : Work.FIPlan.IsPrimitive z1)
    (h2 : Work.FITop3.InPolarBox Pa φ z2) (h2' : Work.FITop3.InPolarBox Pa φ z2')
    (heq : Work.FIPlan.Delta z1 z2 = Work.FIPlan.Delta z1 z2') : z2 = z2' := by
  by_contra hne
  have hd : z2 - z2' ≠ 0 := sub_ne_zero.mpr hne
  -- (1) `Im(z̄₁(z₂ - z₂')) = 0`
  have hD : (star z1 * (z2 - z2')).im = 0 := by
    have he : (star z1 * z2).im = (star z1 * z2').im := by
      have h := heq
      rw [Work.FIPlan.Delta] at h
      exact h
    rw [show star z1 * (z2 - z2') = star z1 * z2 - star z1 * z2' by ring]
    simp only [Zsqrtd.im_sub]
    rw [he, sub_self]
  -- (2) hence `z̄₁(z₂ - z₂')` is real, i.e. `z̄₁·d = z₁·d̄`
  have hzw : star z1 * (z2 - z2') = z1 * star (z2 - z2') := by
    have hw : star (star z1 * (z2 - z2')) = star z1 * (z2 - z2') := by
      apply Zsqrtd.ext
      · rw [Zsqrtd.re_star]
      · rw [Zsqrtd.im_star, hD, neg_zero]
    rw [← hw, star_mul, star_star]
    ring
  -- (3) primitivity (Bézout) gives `z₁ ∣ z₂ - z₂'`
  obtain ⟨a, b, hab⟩ := hz1p
  have hdvd : z1 ∣ z2 - z2' := by
    have h1 : z1 ∣ a * z1 * (z2 - z2') := ⟨a * (z2 - z2'), by ring⟩
    have h2 : z1 ∣ b * (star z1 * (z2 - z2')) := ⟨b * star (z2 - z2'), by rw [hzw]; ring⟩
    have hsum : z2 - z2' = a * z1 * (z2 - z2') + b * (star z1 * (z2 - z2')) := by
      have h := congrArg (fun t => t * (z2 - z2')) hab
      rw [add_mul, one_mul] at h
      conv_lhs => rw [← h]
      ring
    rw [hsum]
    exact dvd_add h1 h2
  obtain ⟨e, he⟩ := hdvd
  have he0 : e ≠ 0 := by
    intro h0
    exact hd (by rw [he, h0, mul_zero])
  have hge1 : 1 ≤ Work.FIPlan.gnorm e := by
    have hne : Work.FIPlan.gnorm e ≠ 0 := by
      intro h0
      apply he0
      have h1 : e.norm.natAbs = 0 := h0
      exact GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp h1)
    omega
  have hnorm_de : Work.FIPlan.gnorm (z2 - z2')
      = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm e := by
    rw [he, gnorm_mul']
  have hgd : (Work.FIPlan.gnorm z1 : ℝ) ≤ (Work.FIPlan.gnorm (z2 - z2') : ℝ) := by
    rw [hnorm_de, Nat.cast_mul]
    have h1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm e : ℝ) := by exact_mod_cast hge1
    have h0 : (0 : ℝ) ≤ (Work.FIPlan.gnorm z1 : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- (4) the geometric bound `|z₂ - z₂'|² < N`
  have hgeo : (Work.FIPlan.gnorm (z2 - z2') : ℝ) < Pa.N := by
    have hb := polar_box_dist h2 h2'
    have hsq : (Work.FIPlan.gnorm (z2 - z2') : ℝ) = ‖(z2 : ℂ) - (z2' : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, ← GaussianInt.toComplex_sub, gnorm_eq_normSq]
    rw [hsq]
    have hr2 : (Real.sqrt Pa.N) ^ 2 = (Pa.N : ℝ) := Real.sq_sqrt (by linarith [Pa.hN1])
    nlinarith [hb, norm_nonneg ((z2 : ℂ) - (z2' : ℂ)), Real.sqrt_nonneg Pa.N, hr2]
  linarith [hz1n, hgd, hgeo]

end Work.FIArea3
