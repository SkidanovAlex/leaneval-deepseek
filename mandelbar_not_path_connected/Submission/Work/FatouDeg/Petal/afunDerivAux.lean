import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.polyAlgebraAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Topology
open Set Filter Metric

namespace Work.FatouDeg.Petal

/-! ## Elementary trigonometric facts used in the estimates -/

/-- `1 / 2 < cos 1`. -/
lemma half_lt_cos_one : (1 : ℝ) / 2 < Real.cos 1 := by
  have h : Real.cos 1 = 1 - 2 * Real.sin (1 / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (1 / 2)
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h1
    have h2 := Real.cos_sq_add_sin_sq (1 / 2)
    nlinarith [h1, h2]
  have hs : Real.sin (1 / 2) < 1 / 2 := Real.sin_lt (by norm_num)
  have h3 : 0 < Real.sin (1 / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  nlinarith [h, hs, h3]

/-- `cos` is decreasing on `[0, π]`, hence `cos 1 ≤ cos t` whenever `|t| ≤ 1`. -/
lemma cos_ge_cos_one_of_abs_le {t : ℝ} (ht : |t| ≤ 1) : Real.cos 1 ≤ Real.cos t := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |t|) (y := 1) (abs_nonneg t)
      (by linarith [Real.pi_gt_three]) ht
  rwa [Real.cos_abs] at h

/-- **The sector `c |Im z| < Re z` has half-angle `arctan (1/c)`.**

For `c > 0` and `c * |Im z| < Re z` one has `|arg z| < arctan (1/c)`. -/
lemma sector_arg_bound {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : c * |z.im| < z.re) :
    |z.arg| < Real.arctan (1 / c) := by
  have hre : 0 < z.re := lt_of_le_of_lt (mul_nonneg hc.le (abs_nonneg _)) hz
  have hz0 : z ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hlt : |z.arg| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl hre
  have hdiv : |z.im| / z.re < 1 / c := by
    rw [div_lt_div_iff₀ hre hc]
    simpa [mul_comm] using hz
  have htan : |Real.tan z.arg| < 1 / c := by
    rw [Complex.tan_arg, abs_div, abs_of_pos hre]
    exact hdiv
  obtain ⟨hlo, hhi⟩ := abs_lt.mp htan
  have hb := abs_lt.mp hlt
  have e1 := Real.arctan_lt_arctan_iff.mpr hhi
  have e2 := Real.arctan_lt_arctan_iff.mpr hlo
  rw [Real.arctan_tan hb.1 hb.2] at e1 e2
  rw [Real.arctan_neg] at e2
  exact abs_lt.mpr ⟨e2, e1⟩

/-! ## Powers and inverse powers -/

/-- The polar form of a power: `z ^ m = ‖z‖ ^ m * (cos (m arg z) + sin (m arg z) * I)`. -/
lemma pow_eq_polar (m : ℕ) (z : ℂ) :
    z ^ m = ↑(‖z‖ ^ m) * (↑(Real.cos (m * z.arg)) + ↑(Real.sin (m * z.arg)) * Complex.I) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  rw [show (↑m : ℂ) * (↑z.arg * Complex.I) = (↑(m * z.arg) : ℂ) * Complex.I by
        push_cast; ring]
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- The real part of `z ^ m` in polar coordinates. -/
lemma pow_re (m : ℕ) (z : ℂ) : (z ^ m).re = ‖z‖ ^ m * Real.cos (m * z.arg) := by
  rw [pow_eq_polar m z, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]

/-- The real part of an inverse power. -/
lemma inv_pow_re (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ((z ^ m)⁻¹).re = (‖z‖ ^ m)⁻¹ * Real.cos (m * z.arg) := by
  have h0 : ‖z‖ ^ m ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hns : Complex.normSq (z ^ m) = (‖z‖ ^ m) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow]
  rw [Complex.inv_re, pow_re, hns, div_eq_mul_inv]
  field_simp

/-- The norm of an inverse power. -/
lemma norm_inv_pow (m : ℕ) (z : ℂ) : ‖(z ^ m)⁻¹‖ = (‖z‖ ^ m)⁻¹ := by
  rw [norm_inv, norm_pow]

/-! ## The derivative of `Afun` -/

/-- **The algebraic identity behind the derivative.**  With `u = z ^ (m-1)`, `v = z ^ (m-2)`
(so that `v * z = u`), the derivative of `(z ^ (m-1))⁻¹ * P z + β log z` computed by the product
rule equals the value written in the chart `z ^ (-m)`. -/
lemma afunDeriv_algebra (z u v n S S' betac : ℂ) (hz : z ≠ 0) (hu : u ≠ 0) (hv : v * z = u) :
    (-(n * v) / u ^ 2) * S + u⁻¹ * S' + betac * z⁻¹
      = -((u * z)⁻¹) * (n * S - z * S' - betac * u) := by
  have hv' : v = u * z⁻¹ := by
    calc v = v * (z * z⁻¹) := by rw [mul_inv_cancel₀ hz, mul_one]
      _ = v * z * z⁻¹ := by ring
      _ = u * z⁻¹ := by rw [hv]
  rw [hv', mul_inv]
  field_simp
  ring

/-- **The derivative of the approximate coordinate `Afun`.**

For `z` with `Re z > 0`, `deriv (Afun m G) z = -z^(-m) * (Qpoly m G z - betac m G * z^(m-1))`. -/
lemma afun_hasDerivAt (m : ℕ) (hm : 2 ≤ m) (G : Polynomial ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (Afun m G)
      (-(z ^ m)⁻¹ * ((Qpoly m G).eval z - betac m G * z ^ (m - 1))) z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hsp : z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; exact Or.inl hz
  have hzn : z ^ (m - 1) ≠ 0 := pow_ne_zero _ hz0
  have h1 : HasDerivAt (fun w : ℂ => (w ^ (m - 1))⁻¹)
      (-(↑(m - 1) * z ^ ((m - 1) - 1)) / (z ^ (m - 1)) ^ 2) z :=
    (hasDerivAt_pow (m - 1) z).inv hzn
  have h2 : HasDerivAt (fun w : ℂ => (Ppoly m G).eval w)
      ((Ppoly m G).derivative.eval z) z := Polynomial.hasDerivAt (Ppoly m G) z
  have h3 : HasDerivAt (fun w : ℂ => (w ^ (m - 1))⁻¹ * (Ppoly m G).eval w)
      ((-(↑(m - 1) * z ^ ((m - 1) - 1)) / (z ^ (m - 1)) ^ 2) * (Ppoly m G).eval z
        + (z ^ (m - 1))⁻¹ * ((Ppoly m G).derivative.eval z)) z := h1.mul h2
  have h4 : HasDerivAt (fun w : ℂ => betac m G * Complex.log w) (betac m G * z⁻¹) z :=
    (Complex.hasDerivAt_log hsp).const_mul (betac m G)
  have h5 : HasDerivAt (Afun m G)
      ((-(↑(m - 1) * z ^ ((m - 1) - 1)) / (z ^ (m - 1)) ^ 2) * (Ppoly m G).eval z
        + (z ^ (m - 1))⁻¹ * ((Ppoly m G).derivative.eval z) + betac m G * z⁻¹) z := h3.add h4
  have hvu : z ^ ((m - 1) - 1) * z = z ^ (m - 1) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m - 1)]
  have hzm : z ^ m = z ^ (m - 1) * z := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hQrel : (Qpoly m G).eval z
      = (↑(m - 1) : ℂ) * (Ppoly m G).eval z - z * ((Ppoly m G).derivative.eval z) := by
    have h := congrArg (fun p : Polynomial ℂ => p.eval z) (polyAlgebraAux m (by omega) G).2
    simpa using h.symm
  have halg := afunDeriv_algebra z (z ^ (m - 1)) (z ^ ((m - 1) - 1)) (↑(m - 1) : ℂ)
      ((Ppoly m G).eval z) ((Ppoly m G).derivative.eval z) (betac m G) hz0 hzn hvu
  rw [← hzm] at halg
  refine h5.congr_deriv ?_
  rw [hQrel]
  exact halg

/-! ## The main theorem -/

/-- **The derivative of the approximate coordinate `Afun`.**

Assume `Qpoly m G` is `1 + O(z)` on the unit disc: `∃ KQ, ‖Q(w) - 1‖ ≤ KQ ‖w‖` for `‖w‖ ≤ 1`
(the second half of `polyBoundsAux`).  Then for all sufficiently small `ρ`:

* on the petal `Pet m ρ` the derivative of the approximate coordinate is strongly negative in real
  part: `(deriv (Afun m G) z).re ≤ -(1/2) * (‖z‖^m)⁻¹`;
* on the working domain `Dom m ρ` the normalized derivative is close to `-1`:
  `‖deriv (Afun m G) z * z^m + 1‖ ≤ 1/4`.

Indeed `deriv (Afun m G) z = -z^(-m) * ((Qpoly m G).eval z - betac m G * z^(m-1))` for `z ≠ 0`
(compute with `deriv` of `(z^(m-1))⁻¹ * P(z)` and `Complex.deriv_log`; at points of `Pet`/`Dom`
one has `Re z > 0` so `Complex.log` and the inverse power are honest), because
`(m-1) P - X P' = Qpoly m G`.  Hence
`deriv (Afun m G) z * z^m + 1 = 1 - (Qpoly m G).eval z + betac m G * z^(m-1)`, whose norm is
`≤ KQ ‖z‖ + ‖betac m G‖ ‖z‖^(m-1)`, and
`(deriv (Afun m G) z).re ≤ -‖z‖^(-m) cos(m θ) + (KQ ‖z‖ + ‖betac m G‖ ‖z‖^(m-1)) ‖z‖^(-m)`
with `|θ| ≤ arctan(1/m)`, so `m|θ| < 1` and `cos(mθ) ≥ cos 1 > 1/2`. -/
theorem afunDerivAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {KQ : ℝ} (hKQ : 0 ≤ KQ)
    (hQ : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖(Qpoly m G).eval w - 1‖ ≤ KQ * ‖w‖) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ((∀ z ∈ Pet m ρ, (deriv (Afun m G) z).re ≤ -(1 / 2) * (‖z‖ ^ m)⁻¹) ∧
        (∀ z ∈ Dom m ρ, ‖deriv (Afun m G) z * z ^ m + 1‖ ≤ 1 / 4)) := by
  set C : ℝ := KQ + ‖betac m G‖ with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hC1 : 0 < C + 1 := by linarith
  have hcos : 0 < Real.cos 1 - 1 / 2 := by linarith [half_lt_cos_one]
  refine ⟨min (1 / 2) (min ((Real.cos 1 - 1 / 2) / (2 * (C + 1))) (1 / (8 * (C + 1)))),
    ?_, ?_⟩
  · exact lt_min (by norm_num)
      (lt_min (div_pos hcos (by positivity)) (div_pos one_pos (by positivity)))
  · intro ρ hρ hρ0
    have hρ1 : ρ ≤ 1 / 2 := le_trans hρ0 (min_le_left _ _)
    have hρn : ρ ≤ (Real.cos 1 - 1 / 2) / (2 * (C + 1)) :=
      le_trans hρ0 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hρd : ρ ≤ 1 / (8 * (C + 1)) :=
      le_trans hρ0 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hm2 : 2 ≤ m := by omega
    have hm1 : 1 ≤ m := by omega
    constructor
    · -- the petal: the derivative is strongly negative in real part
      intro z hz
      rw [mem_Pet] at hz
      obtain ⟨hzρ, hzsec⟩ := hz
      have hzre : 0 < z.re := lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg _)) hzsec
      have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
      have hznpos : 0 < ‖z‖ := lt_of_lt_of_le hzre (Complex.re_le_norm z)
      have hz_le1 : ‖z‖ ≤ 1 := by linarith [le_of_lt hzρ]
      rw [(afun_hasDerivAt m hm2 G hzre).deriv]
      -- the angular bound
      have harg := sector_arg_bound (show (0 : ℝ) < m by positivity) hzsec
      have hθ : |(m : ℝ) * z.arg| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))]
        have hlt : |z.arg| < 1 / (m : ℝ) := lt_trans harg (Real.arctan_lt_self (by positivity))
        have hmul := mul_lt_mul_of_pos_left hlt (show (0 : ℝ) < (m : ℝ) by positivity)
        rw [mul_one_div_cancel (by positivity : (m : ℝ) ≠ 0)] at hmul
        exact le_of_lt hmul
      have hcosθ : Real.cos 1 ≤ Real.cos ((m : ℝ) * z.arg) := cos_ge_cos_one_of_abs_le hθ
      have hre_inv : (‖z‖ ^ m)⁻¹ * Real.cos 1 ≤ ((z ^ m)⁻¹).re := by
        rw [inv_pow_re m hz0]
        exact mul_le_mul_of_nonneg_left hcosθ (by positivity)
      -- the norm of the error term
      have hpow_le : ‖z‖ ^ (m - 1) ≤ ‖z‖ := by
        calc ‖z‖ ^ (m - 1) ≤ ‖z‖ ^ 1 :=
              pow_le_pow_of_le_one (norm_nonneg z) hz_le1 (by omega)
          _ = ‖z‖ := pow_one _
      have he_bound : ‖(Qpoly m G).eval z - 1 - betac m G * z ^ (m - 1)‖
          ≤ Real.cos 1 - 1 / 2 := by
        have h1 : ‖(Qpoly m G).eval z - 1‖ ≤ KQ * ‖z‖ := hQ z hz_le1
        have h2 : ‖betac m G * z ^ (m - 1)‖ = ‖betac m G‖ * ‖z‖ ^ (m - 1) := by
          rw [norm_mul, norm_pow]
        have h3 : ‖(Qpoly m G).eval z - 1 - betac m G * z ^ (m - 1)‖
            ≤ KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) := by
          calc ‖(Qpoly m G).eval z - 1 - betac m G * z ^ (m - 1)‖
              = ‖((Qpoly m G).eval z - 1) - betac m G * z ^ (m - 1)‖ := by ring_nf
            _ ≤ ‖(Qpoly m G).eval z - 1‖ + ‖betac m G * z ^ (m - 1)‖ := norm_sub_le _ _
            _ ≤ KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) := by
                rw [h2]; exact add_le_add h1 le_rfl
        have h4 : KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) ≤ C * ρ := by
          have hKQz : KQ * ‖z‖ ≤ KQ * ρ := mul_le_mul_of_nonneg_left (le_of_lt hzρ) hKQ
          have hbz : ‖betac m G‖ * ‖z‖ ^ (m - 1) ≤ ‖betac m G‖ * ‖z‖ :=
            mul_le_mul_of_nonneg_left hpow_le (norm_nonneg _)
          have hzρ : ‖z‖ ≤ ρ := le_of_lt hzρ
          calc KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1)
              ≤ KQ * ρ + ‖betac m G‖ * ‖z‖ := add_le_add hKQz hbz
            _ ≤ KQ * ρ + ‖betac m G‖ * ρ := by
                exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hzρ (norm_nonneg _))
            _ = C * ρ := by rw [hC]; ring
        have h5 : C * ρ ≤ (Real.cos 1 - 1 / 2) / 2 := by
          have hCp : C * ρ ≤ C * ((Real.cos 1 - 1 / 2) / (2 * (C + 1))) :=
            mul_le_mul_of_nonneg_left hρn hC0
          have hCe : C * ((Real.cos 1 - 1 / 2) / (2 * (C + 1)))
              = (C / (C + 1)) * ((Real.cos 1 - 1 / 2) / 2) := by
            field_simp
          have hCdiv : C / (C + 1) ≤ 1 := by
            rw [div_le_one hC1]; linarith
          have hhalf : 0 ≤ (Real.cos 1 - 1 / 2) / 2 := by linarith
          have := mul_le_mul_of_nonneg_right hCdiv hhalf
          rw [one_mul] at this
          linarith [this, hCp, hCe]
        have := le_trans h3 h4
        linarith [this, h5, hcos]
      -- the real-part estimate
      set e : ℂ := (Qpoly m G).eval z - 1 - betac m G * z ^ (m - 1) with he
      have key : -(z ^ m)⁻¹ * ((Qpoly m G).eval z - betac m G * z ^ (m - 1))
          = -(z ^ m)⁻¹ - (z ^ m)⁻¹ * e := by
        rw [he]; ring
      rw [key]
      have hstep1 : (-(z ^ m)⁻¹ - (z ^ m)⁻¹ * e).re ≤ -((z ^ m)⁻¹).re + ‖(z ^ m)⁻¹ * e‖ := by
        rw [Complex.sub_re, Complex.neg_re]
        have h := Complex.abs_re_le_norm ((z ^ m)⁻¹ * e)
        have h2 : -((z ^ m)⁻¹ * e).re ≤ |((z ^ m)⁻¹ * e).re| := neg_le_abs _
        linarith
      have hnorm_prod : ‖(z ^ m)⁻¹ * e‖ ≤ (‖z‖ ^ m)⁻¹ * ‖e‖ := by
        rw [norm_mul, norm_inv_pow]
      have hpos : 0 < (‖z‖ ^ m)⁻¹ := inv_pos.mpr (pow_pos hznpos m)
      calc (-(z ^ m)⁻¹ - (z ^ m)⁻¹ * e).re
          ≤ -((z ^ m)⁻¹).re + ‖(z ^ m)⁻¹ * e‖ := hstep1
        _ ≤ -((‖z‖ ^ m)⁻¹ * Real.cos 1) + (‖z‖ ^ m)⁻¹ * ‖e‖ := by linarith
        _ = (‖z‖ ^ m)⁻¹ * (‖e‖ - Real.cos 1) := by ring
        _ ≤ (‖z‖ ^ m)⁻¹ * (-(1 / 2)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
            linarith [he_bound]
        _ = -(1 / 2) * (‖z‖ ^ m)⁻¹ := by ring
    · -- the working domain: the normalized derivative is close to `-1`
      intro z hz
      rw [mem_Dom] at hz
      obtain ⟨hzρ, hzsec⟩ := hz
      have hzre : 0 < z.re := lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg _)) hzsec
      have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
      have hz_le1 : ‖z‖ ≤ 1 := by linarith [le_of_lt hzρ, hρ1]
      rw [(afun_hasDerivAt m hm2 G hzre).deriv]
      have hpow_le : ‖z‖ ^ (m - 1) ≤ ‖z‖ := by
        calc ‖z‖ ^ (m - 1) ≤ ‖z‖ ^ 1 :=
              pow_le_pow_of_le_one (norm_nonneg z) hz_le1 (by omega)
          _ = ‖z‖ := pow_one _
      have h1 : ‖(Qpoly m G).eval z - 1‖ ≤ KQ * ‖z‖ := hQ z hz_le1
      have h2 : ‖betac m G * z ^ (m - 1)‖ = ‖betac m G‖ * ‖z‖ ^ (m - 1) := by
        rw [norm_mul, norm_pow]
      have hkey : (-(z ^ m)⁻¹ * ((Qpoly m G).eval z - betac m G * z ^ (m - 1))) * z ^ m + 1
          = -((Qpoly m G).eval z - 1) + betac m G * z ^ (m - 1) := by
        field_simp
        ring
      rw [hkey]
      have h3 : ‖-((Qpoly m G).eval z - 1) + betac m G * z ^ (m - 1)‖
          ≤ KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) := by
        calc ‖-((Qpoly m G).eval z - 1) + betac m G * z ^ (m - 1)‖
            ≤ ‖-((Qpoly m G).eval z - 1)‖ + ‖betac m G * z ^ (m - 1)‖ := norm_add_le _ _
          _ = ‖(Qpoly m G).eval z - 1‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) := by
              rw [norm_neg, h2]
          _ ≤ KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) := add_le_add h1 le_rfl
      have h4 : KQ * ‖z‖ + ‖betac m G‖ * ‖z‖ ^ (m - 1) ≤ C * (2 * ρ) := by
        have hz2ρ : ‖z‖ ≤ 2 * ρ := le_of_lt hzρ
        have hKQz : KQ * ‖z‖ ≤ KQ * (2 * ρ) := mul_le_mul_of_nonneg_left hz2ρ hKQ
        have hbz : ‖betac m G‖ * ‖z‖ ^ (m - 1) ≤ ‖betac m G‖ * (2 * ρ) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact le_trans hpow_le hz2ρ
        have : KQ * (2 * ρ) + ‖betac m G‖ * (2 * ρ) = C * (2 * ρ) := by rw [hC]; ring
        linarith [hKQz, hbz, this.le, this.ge]
      have h5 : C * (2 * ρ) ≤ 1 / 4 := by
        have hCp : C * (2 * ρ) ≤ C * (2 * (1 / (8 * (C + 1)))) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          linarith
        have hCe : C * (2 * (1 / (8 * (C + 1)))) = (C / (C + 1)) * (1 / 4) := by
          field_simp
          ring
        have hCdiv : C / (C + 1) ≤ 1 := by
          rw [div_le_one hC1]; linarith
        have := mul_le_mul_of_nonneg_right hCdiv (by norm_num : (0 : ℝ) ≤ 1 / 4)
        linarith [hCp, hCe, this]
      linarith [le_trans h3 h4, h5]

end Work.FatouDeg.Petal
