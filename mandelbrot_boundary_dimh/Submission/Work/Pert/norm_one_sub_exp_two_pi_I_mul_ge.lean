import Mathlib
import Submission.Work.Pert.sin_sq_pi_ge_of_lattice

set_option maxHeartbeats 1000000

namespace Work.Pert

set_option autoImplicit false

/-- `‖1 - w‖² = (1 - w.re)² + w.im²` for a complex number `w`.  Elementary rewrite through
`Complex.sq_norm` and `Complex.normSq_apply`. -/
private lemma norm_sq_one_sub (w : ℂ) : ‖1 - w‖^2 = (1 - w.re)^2 + w.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- Real algebra: if `(1 - 2 t²)² + u² = 1` then `(1 - X(1-2t²))² + (Xu)² = (1-X)² + 4Xt²`. -/
private lemma norm_sq_one_sub_aux (X t u : ℝ) (h : (1 - 2*t^2)^2 + u^2 = 1) :
    (1 - X*(1-2*t^2))^2 + (X*u)^2 = (1-X)^2 + 4*X*t^2 := by
  have hu : u^2 = 1 - (1-2*t^2)^2 := by linarith [h]
  have hs : (1 - X*(1-2*t^2))^2 + (X*u)^2 = (1 - X*(1-2*t^2))^2 + X^2*u^2 := by ring
  rw [hs, hu]; ring

/-- **Exact modulus identity.**  For every `z : ℂ`,
`‖1 - exp(2πi z)‖² = (1 - e^{-2π Im z})² + 4 e^{-2π Im z} sin²(π Re z)`. -/
private lemma norm_one_sub_exp_two_pi_I_mul_sq (z : ℂ) :
    ‖1 - Complex.exp (2 * (Real.pi:ℂ) * Complex.I * z)‖ ^ 2
      = (1 - Real.exp (-2 * Real.pi * z.im)) ^ 2
        + 4 * Real.exp (-2 * Real.pi * z.im) * Real.sin (Real.pi * z.re) ^ 2 := by
  have hA : (2 * (Real.pi:ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hB : (2 * (Real.pi:ℂ) * Complex.I).im = 2 * Real.pi := by
    simp [Complex.mul_re, Complex.mul_im]
  have hzre : (2 * (Real.pi:ℂ) * Complex.I * z).re = -2*Real.pi*z.im := by
    rw [Complex.mul_re, hA, hB]; ring
  have hzim : (2 * (Real.pi:ℂ) * Complex.I * z).im = 2*Real.pi*z.re := by
    rw [Complex.mul_im, hA, hB]; ring
  have he_re : (Complex.exp (2 * (Real.pi:ℂ) * Complex.I * z)).re
      = Real.exp (-2*Real.pi*z.im) * Real.cos (2*Real.pi*z.re) := by
    rw [Complex.exp_re, hzre, hzim]
  have he_im : (Complex.exp (2 * (Real.pi:ℂ) * Complex.I * z)).im
      = Real.exp (-2*Real.pi*z.im) * Real.sin (2*Real.pi*z.re) := by
    rw [Complex.exp_im, hzre, hzim]
  have hcos2 : Real.cos (2*Real.pi*z.re) = 1 - 2*Real.sin (Real.pi*z.re)^2 := by
    rw [show 2*Real.pi*z.re = 2*(Real.pi*z.re) by ring, Real.cos_two_mul']
    have h := Real.cos_sq_add_sin_sq (Real.pi*z.re)
    nlinarith [h]
  have hcs : (1 - 2*Real.sin (Real.pi*z.re)^2)^2 + Real.sin (2*Real.pi*z.re)^2 = 1 := by
    have h := Real.cos_sq_add_sin_sq (2*Real.pi*z.re)
    rw [hcos2] at h; exact h
  rw [norm_sq_one_sub, he_re, he_im, hcos2]
  exact norm_sq_one_sub_aux _ _ _ hcs

/-- Elementary numerical bound: for `c > 0`, `(3/4) * min 1 c ≤ 1 - exp(-π c)`.
For `c ≤ 1` this is `1 - e^{-x} ≥ x/(1+x)` (from `e^x ≥ 1 + x`) together with `π ≥ 3`, and for
`c ≥ 1` it follows from `e^π ≥ 4`. -/
private theorem three_quarters_min_le_one_sub_exp (c : ℝ) (hc : 0 < c) :
    (3 / 4) * min 1 c ≤ 1 - Real.exp (-(Real.pi * c)) := by
  by_cases hc1 : c ≤ 1
  · rw [min_eq_right hc1]
    have hexp : 1 + Real.pi * c ≤ Real.exp (Real.pi * c) := by
      have := Real.add_one_le_exp (Real.pi * c); linarith
    have hpos : (0:ℝ) < 1 + Real.pi * c := by positivity
    have h1 : (Real.exp (Real.pi*c))⁻¹ ≤ (1 + Real.pi*c)⁻¹ := by
      have := one_div_le_one_div_of_le hpos hexp
      simpa [one_div] using this
    have hexpn : Real.exp (-(Real.pi*c)) = (Real.exp (Real.pi*c))⁻¹ := Real.exp_neg _
    have h2 : (3/4)*c ≤ 1 - (1 + Real.pi*c)⁻¹ := by
      have h3 : (1:ℝ) - (1 + Real.pi*c)⁻¹ = Real.pi*c/(1+Real.pi*c) := by
        field_simp; ring
      rw [h3, le_div_iff₀ hpos]
      have hc2 : c^2 ≤ c := by nlinarith [hc, hc1]
      have hπc_le : Real.pi * c ≤ Real.pi := by
        have := mul_le_mul_of_nonneg_left hc1 (le_of_lt Real.pi_pos); simpa using this
      nlinarith [hc, hc1, hc2, hπc_le, Real.pi_gt_three]
    linarith
  · have hc1' : (1:ℝ) < c := lt_of_not_ge hc1
    rw [min_eq_left (le_of_lt hc1')]
    have h4 : (4:ℝ) < Real.exp Real.pi := by
      have h3 : (4:ℝ) < Real.exp 3 := by
        have he : Real.exp 3 = Real.exp 1 ^ 3 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [he]
        have h2 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
        have h22 : (4:ℝ) < Real.exp 1 ^ 2 := by nlinarith [h2, Real.exp_pos 1]
        nlinarith [h2, h22, Real.exp_pos 1]
      have := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three] : (3:ℝ) ≤ Real.pi)
      linarith
    have hπc : Real.exp (-(Real.pi*c)) ≤ Real.exp (-(Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [hc1', Real.pi_pos])
    have hinv4 : Real.exp (-(Real.pi)) ≤ 1/4 := by
      rw [Real.exp_neg, one_div]
      exact le_of_lt ((inv_lt_inv₀ (Real.exp_pos Real.pi) (by norm_num)).mpr h4)
    linarith

/-- **Lattice lower bound for `1 - exp(2πiξ)`.** If `ξ` is at distance at least `c` from every
integer (`∀ k : ℤ, c ≤ ‖ξ + k‖`, `c > 0`) then `‖1 - exp(2πiξ)‖ ≥ (3/4) * min 1 c`.

Proof sketch: let `r = ξ - m` with `m` the nearest integer to `Re ξ`, so `|Re r| ≤ 1/2` and
`|r| ≥ c` (the hypothesis is invariant under `ξ ↦ ξ - m`). Put `ρ = exp (-2π Im r) > 0`; then
`‖1 - exp(2πiξ)‖² = (1-ρ)² + 2ρ(1 - cos(2π Re r)) ≥ (1-ρ)² + 16 ρ (Re r)²` (using
`|sin(πs)| ≥ 2 dist(s,ℤ)`). If `|Im r| ≥ c/2` this is `≥ (1-exp(-2π|Im r|))²` and
`1-exp(-πc) ≥ πc/(1+πc) ≥ (3/4)c` for `c ≤ 1` (`1-e^{-x} ≥ x/(1+x)`), while for `c ≥ 1`,
`|Im r| ≥ √3/2` (from `(Re r)² + (Im r)² ≥ c² ≥ 1` and `|Re r| ≤ 1/2`) gives
`1 - exp(-π√3) ≥ 3/4`. If `|Im r| < c/2` then `|Re r| ≥ (√3/2)c` and `c ≤ 1/√3` (as `|Re r| ≤ 1/2`),
`ρ ≥ exp(-πc) ≥ exp(-π/√3)`, so the bound is `≥ 4·exp(-π/√3)·(2·(√3/2)c)² ≥ (3/4)²c²`. -/
theorem norm_one_sub_exp_two_pi_I_mul_ge (ξ : ℂ) (c : ℝ) (hc : 0 < c)
    (h : ∀ k : ℤ, c ≤ ‖ξ + (k : ℂ)‖) :
    (3 / 4) * min 1 c ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * ξ)‖ := by
  -- nearest integer to `Re ξ`
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, (m:ℝ) ≤ ξ.re + 1/2 ∧ ξ.re + 1/2 < (m:ℝ) + 1 :=
    ⟨⌊ξ.re + 1/2⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
  set r : ℂ := ξ - (m:ℂ) with hr
  have hrre : r.re = ξ.re - (m:ℝ) := by simp [hr, Complex.sub_re]
  have hPabs : |r.re| ≤ 1/2 := by
    rw [hrre, abs_le]; constructor <;> linarith
  set T : ℝ := r.im with hT
  set P : ℝ := r.re with hPdef
  set ρ : ℝ := Real.exp (-2*Real.pi*T) with hρ
  have hA : (2 * (Real.pi:ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hB : (2 * (Real.pi:ℂ) * Complex.I).im = 2 * Real.pi := by
    simp [Complex.mul_re, Complex.mul_im]
  -- periodicity: `exp (2πi ξ) = exp (2πi r)`
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ξ)
      = Complex.exp (2 * Real.pi * Complex.I * r) := by
    have hξeq : ξ = r + (m:ℂ) := by rw [hr]; ring
    conv_lhs => rw [hξeq]
    rw [mul_add, Complex.exp_add,
        show (2 * (Real.pi:ℂ) * Complex.I) * (m:ℂ) = (m:ℂ) * (2 * ↑Real.pi * Complex.I) by ring,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  -- the exact modulus identity
  have hN : ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖^2
      = (1 - ρ)^2 + 4*ρ*(Real.sin (Real.pi*P))^2 := by
    rw [hρ, hT, hPdef]
    exact norm_one_sub_exp_two_pi_I_mul_sq r
  -- the lattice hypothesis, shifted to `r`
  have hlat : ∀ k : ℤ, c^2 ≤ (P - (k:ℝ))^2 + T^2 := by
    intro k
    have hk := h (-(m + k))
    have heq : ξ + ((-(m+k) : ℤ) : ℂ) = r - (k:ℂ) := by rw [hr]; push_cast; ring
    rw [heq] at hk
    have e1 : (r - (k:ℂ)).re = P - (k:ℝ) := by
      rw [Complex.sub_re, ← hPdef, ← Complex.ofReal_intCast k, Complex.ofReal_re]
    have e2 : (r - (k:ℂ)).im = T := by
      rw [Complex.sub_im, ← hT, ← Complex.ofReal_intCast k, Complex.ofReal_im, sub_zero]
    have hsq : ‖r - (k:ℂ)‖^2 = (P - (k:ℝ))^2 + T^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, e1, e2]; ring
    calc c^2 ≤ ‖r - (k:ℂ)‖^2 := pow_le_pow_left₀ (le_of_lt hc) hk 2
      _ = (P - (k:ℝ))^2 + T^2 := hsq
  have hmain := sin_sq_pi_ge_of_lattice (P := P) (T := T) (δ := c) hlat
  by_cases hbig : c/2 ≤ |T|
  · -- `|Im r| ≥ c/2` : use the modulus `‖1 - exp(2πi r)‖ ≥ |1 - ρ|`
    have hnorm : |1 - ρ| ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖ := by
      have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * r)‖ = ρ := by
        have hz : (2 * Real.pi * Complex.I * r).re = -2*Real.pi*T := by
          rw [Complex.mul_re, hA, hB, ← hT]; ring
        rw [Complex.norm_exp, hz, hρ]
      have := abs_norm_sub_norm_le (1:ℂ) (Complex.exp (2 * Real.pi * Complex.I * r))
      rw [norm_one, h1] at this
      simpa using this
    have hA2 : (3/4)*min 1 c ≤ |1 - ρ| := by
      by_cases hT0 : 0 ≤ T
      · have hTc : c/2 ≤ T := by
          have := hbig; rw [abs_of_nonneg hT0] at this; exact this
        have hρle : ρ ≤ Real.exp (-(Real.pi*c)) := by
          rw [hρ]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hTc]
        have hρle1 : ρ ≤ 1 := by
          rw [hρ, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hT0]
        have habs : |1 - ρ| = 1 - ρ := abs_of_nonneg (by linarith [hρle1])
        rw [habs]
        have hkey := three_quarters_min_le_one_sub_exp c hc
        linarith
      · have hT0' : T < 0 := lt_of_not_ge hT0
        have hTc : c/2 ≤ -T := by
          have := hbig; rw [abs_of_neg hT0'] at this; exact this
        have hρge : Real.exp (Real.pi*c) ≤ ρ := by
          rw [hρ]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hTc]
        have hone : (1:ℝ) ≤ Real.exp (Real.pi*c) :=
          Real.one_le_exp (by nlinarith [Real.pi_pos, hc])
        have h1ρ : 1 ≤ ρ := le_trans hone hρge
        have habs : |1 - ρ| = ρ - 1 := by
          have hle : (1:ℝ) - ρ ≤ 0 := by linarith
          rw [abs_of_nonpos hle]; ring
        rw [habs]
        have hthird : (3/4)*min 1 c ≤ Real.pi*c := by
          by_cases hc1 : c ≤ 1
          · rw [min_eq_right hc1]; nlinarith [Real.pi_gt_three, hc]
          · rw [min_eq_left (le_of_lt (lt_of_not_ge hc1))]; nlinarith [Real.pi_gt_three]
        have hπ : Real.pi*c ≤ Real.exp (Real.pi*c) - 1 := by
          have := Real.add_one_le_exp (Real.pi*c); linarith
        linarith
    linarith
  · -- `|Im r| < c/2` : use the sine term of the modulus identity
    have hbig' : |T| < c/2 := not_le.mp hbig
    have hTlt : T < c/2 := lt_of_le_of_lt (le_abs_self T) hbig'
    have hT2 : T^2 < c^2/4 := by
      have hh := hbig'; rw [abs_lt] at hh; nlinarith [hh.1, hh.2, hc]
    have hmax : max 0 (c^2 - T^2) = c^2 - T^2 := by
      apply max_eq_right; nlinarith [hT2, hc]
    rw [hmax] at hmain
    have hρge : Real.exp (-(Real.pi*c)) ≤ ρ := by
      rw [hρ]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hTlt]
    have hρpos : 0 < ρ := by rw [hρ]; exact Real.exp_pos _
    have hdiff : 0 < c^2 - T^2 := by nlinarith [hT2, hc]
    have hchain : 16 * Real.exp (-(Real.pi*c)) * (c^2 - T^2)
        ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖^2 := by
      have h4 : 4*ρ*(Real.sin (Real.pi*P))^2 ≤ (1-ρ)^2 + 4*ρ*(Real.sin (Real.pi*P))^2 := by
        nlinarith [sq_nonneg (1 - ρ)]
      have h3 : 16 * Real.exp (-(Real.pi*c)) * (c^2 - T^2) ≤ 16*ρ*(c^2 - T^2) := by
        nlinarith [hρge, hdiff]
      have h2 : 16*ρ*(c^2 - T^2) ≤ 4*ρ*(Real.sin (Real.pi*P))^2 := by
        nlinarith [hmain, hρpos]
      rw [hN]; linarith
    -- `c < 1/√3`
    have hP2 : 3*c^2/4 < P^2 := by
      have h0 := hlat 0
      simp only [Int.cast_zero, sub_zero] at h0
      nlinarith [h0, hT2]
    have hPle : P^2 ≤ 1/4 := by
      have h1 : |P|^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg P) hPabs 2
      rw [sq_abs] at h1
      norm_num at h1
      exact h1
    have hc2 : c^2 < 1/3 := by nlinarith [hP2, hPle]
    have hpc2 : (Real.pi*c)^2 < (2:ℝ)^2 := by
      have hp2 : Real.pi^2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have hc2' : c^2 ≤ 1/3 := le_of_lt hc2
      have hle : Real.pi^2 * c^2 ≤ 10 * (1/3) :=
        mul_le_mul hp2 hc2' (sq_nonneg c) (by norm_num)
      have he : (Real.pi*c)^2 = Real.pi^2 * c^2 := by ring
      rw [he]; linarith
    have hpc_lt : Real.pi*c < 2 := by
      have hh := sq_lt_sq.mp hpc2
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi*c),
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hh
      linarith
    -- `exp(-π c) > 1/9`
    have hexp2 : (1:ℝ)/9 < Real.exp (-(Real.pi*c)) := by
      have hlt : Real.exp (-2) < Real.exp (-(Real.pi*c)) := by
        apply Real.exp_lt_exp.mpr; nlinarith [hpc_lt]
      have h9 : (1:ℝ)/9 < Real.exp (-2) := by
        have he2 : Real.exp 2 < 9 := by
          have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
          have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
            rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
          rw [he]; nlinarith [h3, Real.exp_pos 1]
        rw [Real.exp_neg, show (1:ℝ)/9 = (9:ℝ)⁻¹ by norm_num]
        exact (inv_lt_inv₀ (by norm_num : (0:ℝ) < 9) (Real.exp_pos 2)).mpr he2
      linarith
    have hcle1 : c ≤ 1 := by nlinarith [hc2]
    rw [min_eq_right hcle1]
    have hfinal : ((3/4)*c)^2 < ‖1 - Complex.exp (2 * Real.pi * Complex.I * r)‖^2 := by
      have h1 : (9/16)*c^2 < 16*(1/9)*(3*c^2/4) := by nlinarith [hc]
      have h2 : 16*(1/9)*(3*c^2/4) < 16 * Real.exp (-(Real.pi*c)) * (c^2 - T^2) := by
        nlinarith [hexp2, hT2, hc]
      linarith
    have hsq := sq_lt_sq.mp hfinal
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (3/4)*c),
        abs_of_nonneg (norm_nonneg _)] at hsq
    linarith

end Work.Pert
