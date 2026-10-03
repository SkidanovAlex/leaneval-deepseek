import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.sin_sq_pi_ge_of_lattice
import Submission.Work.Pert.norm_sq_one_sub_exp_two_pi_I_mul
import Submission.Work.Pert.iInf_dist_eq_norm_sub_round

/-!
# PERT · `Work.Pert.tauC_sub_sigma_norm_le`

The pointwise "distance to the fixed point" bound for the universal cover
`τ_f = tauC σ α w = σ / (1 - exp (-2πi α w))` of (A.1.5):

  `‖τ_f w - σ‖ ≤ ‖σ‖ · (2 + (9/25) / dist (α w, ℤ))`.

**Why it is the right shape.**  Writing `s = α w` and `E = exp (-2πi s)`,
`τ_f w = σ / (1 - E)`.  In the non-degenerate case `E ≠ 1` one has the exact algebraic identity
`τ_f w - σ = σ · E / (1 - E)`, so

  `‖τ_f w - σ‖ = ‖σ‖ · ‖E / (1 - E)‖ = ‖σ‖ / ‖1 - exp (2πi s)‖`.

The whole content of the lemma is therefore the *lower* bound

  `‖1 - exp (2πi s)‖ ≥ d / (2 d + 9/25)`,  `d = dist (s, ℤ) ⊂ ℂ`,   (★)

for the denominator, which is the sharp "simple pole at the lattice" estimate: near the lattice
the denominator behaves like `2π d`, and `1/(2π) < 9/25` leaves room.  Equivalently (★) reads
`d ≤ (2 d + 9/25) ‖1 - exp (2πi s)‖`, the form in which it is proved below.

**Proof of (★) (the crux, `one_sub_exp_two_pi_I_mul_ge`).**  By periodicity of the exponential
one may first reduce to `r = s - m` with `m` an integer and `|Re r| ≤ 1/2`
(`iInf_dist_eq_norm_sub_round`: the nearest integer realises the infimum, so that in fact
`d = ‖r‖`).  Then, with `x = Re r`, `y = Im r`, `u = e^{-2πy}` and the exact modulus identity
(`norm_sq_one_sub_exp_two_pi_I_mul`)

  `‖1 - exp (2πi r)‖² = (1 - u)² + 4 u sin²(π x)`,

one argues on `F := ‖1 - exp (2πi r)‖`:

* `y ≤ 0`: `1 - u = 1 - e^{2π|y|} ≤ 0`, so `(1 - u)² ≥ (2πy)² ≥ 16 y²`, while Jordan's
  inequality `sin²(πx) ≥ 4x²` on `[-1/2,1/2]` and `u ≥ 1` give `4u sin²(πx) ≥ 16 x²`.  Hence
  `F² ≥ 16 ‖r‖²`, and `(9/25)² · 16 = 1296/625 > 1` finishes.
* `y > 0` and `u ≤ 1/2`: then `F ≥ 1 - u ≥ 1/2 ≥ ‖r‖/(2‖r‖ + 9/25)`.
* `y > 0` and `u > 1/2`: then `-2πy > -log 2`, so `2πy ≤ log 2`, and `1 - u ≥ 2πy/(1 + 2πy)
  ≥ 2√2 y` because `√2 (1 + log 2) < 3 < π`; with `u ≥ 1/2` this gives
  `F² ≥ 8 y² + 8 x² = 8 ‖r‖²`, and `2√2 · (9/25) = 18√2/25 > 1` finishes.

The degenerate case `E = 1` (equivalently `s ∈ ℤ`, `d = 0`) is handled separately: then
`τ_f w = σ/0 = 0`, so `‖τ_f w - σ‖ = ‖σ‖ ≤ 2‖σ‖` and `(9/25)/d = 0` in Lean.
-/

namespace Work.Pert

set_option maxHeartbeats 1000000

/-- **Jordan's inequality, squared form.**  For `|x| ≤ 1/2` one has `4 x² ≤ sin (π x)²`
(the constant is optimal, with equality at `x = ±1/2`).  This is `Real.mul_abs_le_abs_sin`
applied to `π x`, squared. -/
private theorem sin_sq_pi_ge_four_sq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    4 * x ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
  have hpx : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hx]
  have h1 := Real.mul_abs_le_abs_sin hpx
  have h2 : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    have h3 : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    linarith [h1, h3]
  have h3 : (2 * |x|) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
    have hp : (2 * |x|) ^ 2 ≤ |Real.sin (Real.pi * x)| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rwa [sq_abs] at hp
  nlinarith [h3, sq_abs x]

/-- `s/(1+s) ≤ 1 - e^{-s}` for `s ≥ 0`, from `e^s ≥ 1 + s`. -/
private theorem div_one_add_le_one_sub_exp_neg (s : ℝ) (hs : 0 ≤ s) :
    s / (1 + s) ≤ 1 - Real.exp (-s) := by
  have h1 : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have h2 : 0 < 1 + s := by linarith
  have h4 : (Real.exp s)⁻¹ ≤ ((1 : ℝ) + s)⁻¹ := by
    rw [inv_le_inv₀ (Real.exp_pos s) h2]; exact h1
  have h3 : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
  have h5 : (1 : ℝ) - ((1 : ℝ) + s)⁻¹ = s / (1 + s) := by
    field_simp
    ring
  linarith [h3, h4, h5]

/-- **The crux.**  For `|Re r| ≤ 1/2`,

  `‖r‖ ≤ (2 ‖r‖ + 9/25) · ‖1 - exp (2πi r)‖`.

Equivalently `‖1 - exp (2πi r)‖ ≥ ‖r‖ / (2‖r‖ + 9/25)`: the exponential denominator is at
least a fixed multiple (`≥ 9/25`) of the lattice distance `‖r‖`.  See the module docstring
for the three-case proof. -/
theorem one_sub_exp_two_pi_I_mul_ge (r : ℂ) (hr : |r.re| ≤ 1 / 2) :
    ‖r‖ ≤ (2 * ‖r‖ + 9 / 25) * ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖ := by
  set x : ℝ := r.re with hx
  set y : ℝ := r.im with hy
  set u : ℝ := Real.exp (-2 * Real.pi * y) with hu
  set F : ℝ := ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖ with hF
  have hFnn : 0 ≤ F := by rw [hF]; exact norm_nonneg _
  have hAnn : 0 ≤ 2 * ‖r‖ + 9 / 25 := by positivity
  have hrsq : ‖r‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hx, hy]
    ring
  have hFsq : F ^ 2 = (1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
    rw [hF, hx, hu, hy]
    exact norm_sq_one_sub_exp_two_pi_I_mul r
  have hxabs : |x| ≤ 1 / 2 := by rw [hx]; exact hr
  have hsin : 4 * x ^ 2 ≤ (Real.sin (Real.pi * x)) ^ 2 := sin_sq_pi_ge_four_sq hxabs
  have hAk : (9 / 25 : ℝ) ^ 2 ≤ (2 * ‖r‖ + 9 / 25) ^ 2 := by
    refine pow_le_pow_left₀ (by norm_num) ?_ 2
    linarith [norm_nonneg r]
  have key : ‖r‖ ^ 2 ≤ (2 * ‖r‖ + 9 / 25) ^ 2 * F ^ 2 := by
    rw [hrsq, hFsq]
    rcases lt_or_ge y 0 with hy0 | hy0
    · -- `y < 0`: `(1-u)² ≥ 4π²y²`, `4u sin²(πx) ≥ 16x²`, so `F² ≥ 16‖r‖²`
      have huy : 0 ≤ -2 * Real.pi * y := by nlinarith [Real.pi_pos, hy0]
      have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_exp huy
      have h1u : (2 * Real.pi * y) ^ 2 ≤ (1 - u) ^ 2 := by
        have h1 : -2 * Real.pi * y ≤ u - 1 := by
          have := Real.add_one_le_exp (-2 * Real.pi * y)
          rw [hu]; linarith
        have h2 : (-2 * Real.pi * y) ^ 2 ≤ (u - 1) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h1 2
        have e1 : (-2 * Real.pi * y) ^ 2 = (2 * Real.pi * y) ^ 2 := by ring
        have e2 : (u - 1) ^ 2 = (1 - u) ^ 2 := by ring
        rw [e1, e2] at h2; exact h2
      have h2u : 16 * x ^ 2 ≤ 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
        have h1 : 4 * (Real.sin (Real.pi * x)) ^ 2 ≤ 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
          nlinarith [sq_nonneg (Real.sin (Real.pi * x)), hu1]
        nlinarith [h1, hsin]
      have hFsqge : 16 * (x ^ 2 + y ^ 2)
          ≤ (1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
        have hπ2 : (16 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have h3 : (16 : ℝ) * y ^ 2 ≤ (2 * Real.pi * y) ^ 2 := by
          nlinarith [hπ2, sq_nonneg y]
        linarith [h1u, h2u, h3]
      have h1 : (9 / 25 : ℝ) ^ 2 * (16 * (x ^ 2 + y ^ 2))
          ≤ (2 * ‖r‖ + 9 / 25) ^ 2
            * ((1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2) :=
        mul_le_mul hAk hFsqge (by positivity) (by positivity)
      have h2 : ‖r‖ ^ 2 ≤ (9 / 25 : ℝ) ^ 2 * (16 * (x ^ 2 + y ^ 2)) := by
        rw [hrsq]; nlinarith [sq_nonneg x, sq_nonneg y]
      linarith
    · -- `0 ≤ y`
      have hu_le : u ≤ 1 := by
        rw [hu, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hy0]
      rcases lt_or_ge u (1 / 2) with hu2 | hu2
      · -- `u < 1/2`: `F² ≥ (1-u)² ≥ 1/4` and `(2‖r‖+9/25)²/4 ≥ ‖r‖²`
        have h1 : (1 : ℝ) / 2 ≤ 1 - u := by linarith
        have h1' : ((1 : ℝ) / 2) ^ 2 ≤ (1 - u) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
        have hu0 : 0 ≤ u := by rw [hu]; exact (Real.exp_pos _).le
        have h2 : (1 / 4 : ℝ) ≤ (1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
          nlinarith [h1', sq_nonneg (Real.sin (Real.pi * x)), hu0]
        have h3 : x ^ 2 + y ^ 2 ≤ (2 * ‖r‖ + 9 / 25) ^ 2 * (1 / 4) := by
          nlinarith [norm_nonneg r, sq_nonneg (2 * ‖r‖ + 9 / 25), hrsq]
        have h4 : (2 * ‖r‖ + 9 / 25) ^ 2 * (1 / 4)
            ≤ (2 * ‖r‖ + 9 / 25) ^ 2
              * ((1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith [h3, h4]
      · -- `1/2 ≤ u`: `1 - u ≥ 2√2 y` and `4u sin²(πx) ≥ 8x²`, so `F² ≥ 8‖r‖²`
        have hlog : 2 * Real.pi * y ≤ Real.log 2 := by
          have h1 : Real.exp (-(Real.log 2)) ≤ Real.exp (-2 * Real.pi * y) := by
            rw [hu] at hu2
            have h2 : Real.exp (-(Real.log 2)) = (1 : ℝ) / 2 := by
              rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
              norm_num
            rw [h2]; exact hu2
          rw [Real.exp_le_exp] at h1
          linarith
        have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have hlog2 : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
        have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        have hgoal : Real.sqrt 2 * (1 + 2 * Real.pi * y) < 3 := by
          have h2 : 1 + 2 * Real.pi * y ≤ 1 + Real.log 2 := by linarith
          nlinarith [h2, hsqrt2, hlog2, hsqrt2pos]
        have hpi : Real.sqrt 2 * (1 + 2 * Real.pi * y) ≤ Real.pi := by
          linarith [Real.pi_gt_three]
        have hden : 0 < 1 + 2 * Real.pi * y := by nlinarith [Real.pi_pos, hy0]
        have h1u : (2 * Real.sqrt 2 * y) ^ 2 ≤ (1 - u) ^ 2 := by
          have hbase : 2 * Real.sqrt 2 * y ≤ 1 - u := by
            have hA : 2 * Real.pi * y / (1 + 2 * Real.pi * y) ≤ 1 - u := by
              rw [hu]
              have hkey := div_one_add_le_one_sub_exp_neg (2 * Real.pi * y)
                (by nlinarith [Real.pi_pos, hy0])
              have harg : -(2 * Real.pi * y) = -2 * Real.pi * y := by ring
              rwa [harg] at hkey
            have hB : 2 * Real.sqrt 2 * y ≤ 2 * Real.pi * y / (1 + 2 * Real.pi * y) := by
              rw [le_div_iff₀ hden]
              have hm := mul_le_mul_of_nonneg_right hpi (by linarith : (0:ℝ) ≤ 2 * y)
              nlinarith [hm]
            linarith
          exact pow_le_pow_left₀ (by nlinarith [hsqrt2pos, hy0]) hbase 2
        have h2u : 8 * x ^ 2 ≤ 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
          have h1 : 4 * u * (4 * x ^ 2) ≤ 4 * u * (Real.sin (Real.pi * x)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsin (by nlinarith [hu2] : (0:ℝ) ≤ 4 * u)
          nlinarith [h1, hu2, sq_nonneg x]
        have hFsqge : 8 * (x ^ 2 + y ^ 2)
            ≤ (1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2 := by
          have h3 : (2 * Real.sqrt 2 * y) ^ 2 = 8 * y ^ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
          linarith [h1u, h2u, h3]
        have h1 : (9 / 25 : ℝ) ^ 2 * (8 * (x ^ 2 + y ^ 2))
            ≤ (2 * ‖r‖ + 9 / 25) ^ 2
              * ((1 - u) ^ 2 + 4 * u * (Real.sin (Real.pi * x)) ^ 2) :=
          mul_le_mul hAk hFsqge (by positivity) (by positivity)
        have h2 : ‖r‖ ^ 2 ≤ (9 / 25 : ℝ) ^ 2 * (8 * (x ^ 2 + y ^ 2)) := by
          rw [hrsq]; nlinarith [sq_nonneg x, sq_nonneg y]
        linarith
  have hmain : ‖r‖ ^ 2 ≤ ((2 * ‖r‖ + 9 / 25) * F) ^ 2 := by
    rw [mul_pow]; exact key
  rw [sq_le_sq] at hmain
  rw [abs_of_nonneg (norm_nonneg r), abs_of_nonneg (mul_nonneg hAnn hFnn)] at hmain
  rw [hF] at hmain
  exact hmain

theorem tauC_sub_sigma_norm_le {σ α w : ℂ} :
    ‖Work.Pert.tauC σ α w - σ‖
      ≤ ‖σ‖ * (2 + (9 / 25) / (⨅ k : ℤ, dist (α * w) (k : ℂ))) := by
  set s : ℂ := α * w with hs
  set d : ℝ := ⨅ k : ℤ, dist s (k : ℂ) with hd
  set E : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * s)) with hE
  have harg : -(2 * Real.pi * Complex.I * α * w) = -(2 * Real.pi * Complex.I * s) := by
    rw [hs]; ring
  have htau : tauC σ α w = σ / (1 - E) := by
    rw [tauC, harg, hE]
  by_cases hE1 : E = 1
  · -- `E = 1`: the denominator of `τ_f` vanishes, so `τ_f w = 0` and `τ_f w - σ = -σ`
    have htau0 : tauC σ α w = 0 := by rw [htau, hE1, sub_self, div_zero]
    rw [htau0, zero_sub, norm_neg]
    have hdnn : 0 ≤ d := by rw [hd]; exact le_ciInf (fun k => dist_nonneg)
    have hk : 0 ≤ (9 / 25 : ℝ) / d := div_nonneg (by norm_num) hdnn
    nlinarith [mul_nonneg (norm_nonneg σ) hk, norm_nonneg σ]
  · -- `E ≠ 1`: reduce to `r = s - m`, `|Re r| ≤ 1/2`, then apply the crux
    obtain ⟨m, hm_abs, hm_eq⟩ := iInf_dist_eq_norm_sub_round s
    set r : ℂ := s - (m : ℂ) with hr
    have hr_abs : |r.re| ≤ 1 / 2 := by rw [hr]; exact hm_abs
    have hd_eq : d = ‖r‖ := by rw [hd, hm_eq, hr]
    have hcrux := one_sub_exp_two_pi_I_mul_ge r hr_abs
    -- periodicity: `exp (2πi s) = exp (2πi r)`
    have hper : Complex.exp (2 * Real.pi * Complex.I * s)
        = Complex.exp (2 * Real.pi * Complex.I * r) := by
      have hs_eq : s = r + (m : ℂ) := by rw [hr]; ring
      conv_lhs => rw [hs_eq]
      rw [mul_add, Complex.exp_add,
          show (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ)
            = (m : ℂ) * (2 * ↑Real.pi * Complex.I) by ring,
          Complex.exp_int_mul_two_pi_mul_I, mul_one]
    set F' : ℝ := ‖1 - Complex.exp (2 * Real.pi * Complex.I * s)‖ with hF'
    have hF'eq : F' = ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖ := by
      rw [hF', hper]
    have hcrux' : d ≤ (2 * d + 9 / 25) * F' := by
      rw [hd_eq, hF'eq]; exact hcrux
    have hdpos : 0 < d := by
      rw [hd_eq, norm_pos_iff]
      intro hr0
      apply hE1
      have hs_eq : s = (m : ℂ) := by
        rw [hr] at hr0
        exact sub_eq_zero.mp hr0
      rw [hE, hs_eq]
      have harg2 : -(2 * Real.pi * Complex.I * (m : ℂ))
          = (-m : ℤ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [harg2, Complex.exp_int_mul_two_pi_mul_I]
    have hF'pos : 0 < F' := by
      have hpos : 0 < (2 * d + 9 / 25) * F' := lt_of_lt_of_le hdpos hcrux'
      rcases mul_pos_iff.mp hpos with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by linarith)
    have hineq : 1 / F' ≤ 2 + (9 / 25) / d := by
      have h2d : (2 : ℝ) + (9 / 25) / d = (2 * d + 9 / 25) / d := by field_simp
      rw [h2d, le_div_iff₀ hdpos, div_mul_eq_mul_div, one_mul, div_le_iff₀ hF'pos]
      exact hcrux'
    have hne : (1 : ℂ) - E ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hE1 h.symm
    have hEne : E ≠ 0 := by rw [hE]; exact Complex.exp_ne_zero _
    -- the exact algebraic identity `τ_f w - σ = σ · E/(1-E)`
    have hts : tauC σ α w - σ = σ * (E / (1 - E)) := by
      rw [htau]
      field_simp
      ring
    -- `‖E/(1-E)‖ = 1/‖1 - exp (2πi s)‖`
    have hEmul : ‖E / (1 - E)‖ = 1 / F' := by
      have h1 : E / (1 - E) = 1 / ((1 - E) / E) := by rw [one_div, inv_div]
      have h2 : ‖(1 - E) / E‖ = F' := by
        have h3 : (1 - E) / E = 1 / E - 1 := by rw [sub_div, div_self hEne]
        have h4 : (1 : ℂ) / E = Complex.exp (2 * Real.pi * Complex.I * s) := by
          rw [one_div, hE, Complex.exp_neg, inv_inv]
        rw [h3, h4, hF']
        rw [show Complex.exp (2 * Real.pi * Complex.I * s) - 1
              = -(1 - Complex.exp (2 * Real.pi * Complex.I * s)) by ring, norm_neg]
      rw [h1, norm_div, norm_one, h2]
    calc ‖tauC σ α w - σ‖ = ‖σ‖ * ‖E / (1 - E)‖ := by rw [hts, norm_mul]
      _ = ‖σ‖ * (1 / F') := by rw [hEmul]
      _ ≤ ‖σ‖ * (2 + (9 / 25) / d) := mul_le_mul_of_nonneg_left hineq (norm_nonneg σ)

end Work.Pert
