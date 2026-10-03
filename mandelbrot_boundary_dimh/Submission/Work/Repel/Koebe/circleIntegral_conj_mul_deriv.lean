import Mathlib
import Submission.Work.Repel.Koebe.circleIntegral_series_residue
import Submission.Work.Repel.Koebe.exterior_deriv_laurent

/-!
# `(2πi)⁻¹ ∮ conj (g z) * (deriv g z) dz` for an exterior function `g`

If `g` is given on `{1 < ‖z‖}` by the absolutely convergent expansion
`g z = z + ∑ k, c k / z ^ k`, then the circle integral of `conj g * deriv g` over `‖z‖ = r`
(`r > 1`) picks out the `z⁻¹` coefficient of the Laurent expansion of the integrand, giving the
classical area formula `π (r ^ 2 - ∑ m, m * ‖c m‖ ^ 2 / r ^ (2 * m))`.
-/

namespace Work.Repel.Koebe

/-- If `0 < ρ < r` and `∑ v k / ρ ^ k` converges for a nonnegative `v`, then `∑ k * v k / r ^ k`
converges: the extra factor `k * (ρ / r) ^ k` is bounded, because it tends to `0`. -/
lemma summable_nat_mul_div_pow_of_summable {v : ℕ → ℝ} (hv : ∀ k : ℕ, 0 ≤ v k) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hvsum : Summable (fun k : ℕ => v k / ρ ^ k)) :
    Summable (fun k : ℕ => (k : ℝ) * v k / r ^ k) := by
  have hr : 0 < r := lt_trans hρ hρr
  have hq0 : 0 ≤ ρ / r := le_of_lt (div_pos hρ hr)
  have hq1 : ρ / r < 1 := (div_lt_one hr).mpr hρr
  have htend := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have hev : ∀ᶠ k : ℕ in Filter.cofinite, (k : ℝ) * (ρ / r) ^ k ≤ 1 := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [htend.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))] with k hk
    exact le_of_lt hk
  refine Summable.of_norm_bounded_eventually hvsum ?_
  filter_upwards [hev] with k hk
  have hnonneg : 0 ≤ (k : ℝ) * v k / r ^ k :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) (hv k)) (pow_nonneg hr.le k)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have h2 : (ρ / r) ^ k * (v k / ρ ^ k) = v k / r ^ k := by
    rw [div_pow, div_mul_div_comm, mul_comm (ρ ^ k) (v k),
      mul_div_mul_right _ _ (pow_ne_zero k hρ.ne')]
  have hkey : (k : ℝ) * v k / r ^ k = ((k : ℝ) * (ρ / r) ^ k) * (v k / ρ ^ k) := by
    rw [mul_assoc, h2, mul_div_assoc]
  rw [hkey]
  calc ((k : ℝ) * (ρ / r) ^ k) * (v k / ρ ^ k)
      ≤ 1 * (v k / ρ ^ k) :=
        mul_le_mul_of_nonneg_right hk (div_nonneg (hv k) (pow_nonneg hρ.le k))
    _ = v k / ρ ^ k := one_mul _

/-- If `∑ ‖c k‖ / ρ ^ k` converges for every `ρ > 1`, then `∑ ‖c k‖ ^ 2 / s ^ k` converges for
every `s > 1`. -/
lemma summable_norm_sq_div_pow {c : ℕ → ℂ} {s : ℝ} (hs : 1 < s)
    (hsum : ∀ ρ : ℝ, 1 < ρ → Summable (fun k : ℕ => ‖c k‖ / ρ ^ k)) :
    Summable (fun k : ℕ => ‖c k‖ ^ 2 / s ^ k) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hsqrt : 1 < Real.sqrt s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hs
  obtain ⟨σ, hσ1, hσs⟩ : ∃ σ : ℝ, 1 < σ ∧ σ ^ 2 = s :=
    ⟨Real.sqrt s, hsqrt, Real.sq_sqrt hs0.le⟩
  have hσpos : 0 < σ := lt_trans zero_lt_one hσ1
  have hsumσ := hsum σ hσ1
  have hsq : (fun k : ℕ => ‖c k‖ ^ 2 / s ^ k) = fun k : ℕ => (‖c k‖ / σ ^ k) ^ 2 := by
    funext k
    rw [← hσs]
    simp only [pow_two, mul_pow, div_mul_div_comm]
  rw [hsq]
  have hev : ∀ᶠ k : ℕ in Filter.cofinite, ‖c k‖ / σ ^ k ≤ 1 := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hsumσ.tendsto_atTop_zero.eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))] with k hk
    exact le_of_lt hk
  refine Summable.of_norm_bounded_eventually hsumσ ?_
  filter_upwards [hev] with k hk
  have hnn : 0 ≤ ‖c k‖ / σ ^ k := div_nonneg (norm_nonneg _) (pow_nonneg hσpos.le k)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hk, hnn]

/-- On the circle `‖z‖ = r` the conjugate of the exterior function `g` is given by the conjugate
power series `conj z = r ^ 2 / z` plus `∑ k, conj (c k) / r ^ (2 k) * z ^ k`. -/
lemma star_g_eq {g : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ} (hr : 1 < r)
    (hexp : ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun k : ℕ => c k / z ^ k) (g z - z)) :
    ∀ z : ℂ, ‖z‖ = r →
      star (g z) = (r : ℂ) ^ 2 / z + ∑' k : ℕ, star (c k) * z ^ k / (r : ℂ) ^ (2 * k) := by
  intro z hz
  have hzp : 1 < ‖z‖ := by rw [hz]; exact hr
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith
  have hz_norm : z * (starRingEnd ℂ) z = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj', hz]
  have hstz : (starRingEnd ℂ) z = (r : ℂ) ^ 2 / z := by
    rw [eq_div_iff hzne, mul_comm]
    exact hz_norm
  have hstz' : star z = (r : ℂ) ^ 2 / z := by
    rw [RCLike.star_def]
    exact hstz
  have hconj : HasSum (fun k : ℕ => star (c k / z ^ k)) (star (g z - z)) :=
    (hexp z hzp).star
  have hterm : ∀ k : ℕ, star (c k / z ^ k) = star (c k) * z ^ k / (r : ℂ) ^ (2 * k) := by
    intro k
    have hpk : (((r : ℂ) ^ 2) ^ k) = (r : ℂ) ^ (2 * k) := by rw [← pow_mul]
    simp only [RCLike.star_def, map_div₀, map_pow, hstz, div_pow, hpk]
    field_simp
  have hsum_eq : (∑' k : ℕ, star (c k) * z ^ k / (r : ℂ) ^ (2 * k)) = star (g z - z) := by
    rw [← hconj.tsum_eq]
    exact tsum_congr fun k => (hterm k).symm
  rw [hsum_eq, star_sub, hstz']
  ring

/-- **The contour integral of the exterior Koebe integrand.**  Let `g` be an exterior function with
absolutely convergent Laurent expansion `g z = z + ∑ k, c k / z ^ k` on `{1 < ‖z‖}`.  Then for
`r > 1` the circle integral of `conj g * deriv g` over `‖z‖ = r` is `2 π i (r ^ 2 - ∑ m, m ‖c m‖²
/ r ^ (2 m))`; equivalently, the signed area enclosed by the curve `g '' {‖z‖ = r}` is
`π (r ^ 2 - ∑ m, m ‖c m‖² / r ^ (2 m))`. -/
theorem circleIntegral_conj_mul_deriv {g : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ} (hr : 1 < r)
    (hexp : ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun k : ℕ => c k / z ^ k) (g z - z))
    (hsum : ∀ ρ : ℝ, 1 < ρ → Summable (fun k : ℕ => ‖c k‖ / ρ ^ k)) :
    (1 / (2 * Complex.I)) * circleIntegral (fun z : ℂ => (star (g z)) * deriv g z) 0 r
      = Real.pi * (r ^ 2 - ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  obtain ⟨ρ, hρ1, hρr⟩ : ∃ ρ : ℝ, 1 < ρ ∧ ρ < r := ⟨(1 + r) / 2, by linarith, by linarith⟩
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ1
  set α : ℕ → ℂ := fun m => star (c m) / (r : ℂ) ^ (2 * m) with hαdef
  set γ : ℕ → ℂ := fun k => -(k : ℂ) * c k with hγdef
  set S : ℝ := ∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) with hSdef
  -- summability of the `α` coefficients
  have hαsum : Summable (fun m : ℕ => ‖α m‖ * r ^ m) := by
    have hfun : (fun m : ℕ => ‖α m‖ * r ^ m) = fun m : ℕ => ‖c m‖ / r ^ m := by
      funext m
      have hnorm : ‖(r : ℂ)‖ = r := by
        rw [show ‖(r : ℂ)‖ = |r| by simp, abs_of_pos hr0]
      rw [hαdef, norm_div, norm_pow, norm_star, hnorm]
      rw [show r ^ (2 * m) = r ^ m * r ^ m by rw [two_mul, pow_add]]
      field_simp
    rw [hfun]
    exact hsum r hr
  -- summability of the `γ` coefficients
  have hγsum : Summable (fun k : ℕ => ‖γ k‖ / r ^ (k + 1)) := by
    have hfun : (fun k : ℕ => ‖γ k‖ / r ^ (k + 1))
        = fun k : ℕ => (k : ℝ) * ‖c k‖ / r ^ (k + 1) := by
      funext k
      rw [hγdef, norm_mul, norm_neg]
      simp only [Complex.norm_natCast]
    rw [hfun]
    have hbase := summable_nat_mul_div_pow_of_summable (v := fun k => ‖c k‖)
      (fun k => norm_nonneg _) hρ0 hρr (hsum ρ hρ1)
    have hfun2 : (fun k : ℕ => (k : ℝ) * ‖c k‖ / r ^ (k + 1))
        = fun k : ℕ => (1 / r) * ((k : ℝ) * ‖c k‖ / r ^ k) := by
      funext k
      rw [pow_succ]
      field_simp
    rw [hfun2]
    exact hbase.mul_left (1 / r)
  have hres := circleIntegral_series_residue (α := α) (γ := γ) (β := (r : ℂ) ^ 2)
    hr0 hαsum hγsum
  -- the pointwise identity on the sphere
  have hpoint : Set.EqOn (fun z : ℂ => star (g z) * deriv g z)
      (fun z : ℂ => ((r : ℂ) ^ 2 / z + ∑' m : ℕ, α m * z ^ m)
        * (1 + ∑' k : ℕ, γ k / z ^ (k + 1))) (Metric.sphere 0 r) := by
    intro z hz
    show star (g z) * deriv g z = ((r : ℂ) ^ 2 / z + ∑' m : ℕ, α m * z ^ m)
        * (1 + ∑' k : ℕ, γ k / z ^ (k + 1))
    have hz' : ‖z‖ = r := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      exact hz
    have hzp : 1 < ‖z‖ := by rw [hz']; exact hr
    have hstar := star_g_eq hr hexp z hz'
    have hder := exterior_deriv_laurent hexp hsum z hzp
    have hA : (∑' k : ℕ, star (c k) * z ^ k / (r : ℂ) ^ (2 * k)) = ∑' m : ℕ, α m * z ^ m := by
      apply tsum_congr
      intro m
      rw [hαdef, div_mul_eq_mul_div]
    have hB : deriv g z = 1 + ∑' k : ℕ, γ k / z ^ (k + 1) := by
      rw [hder.tsum_eq]
      ring
    rw [hstar, hA, hB]
  have hintegral : circleIntegral (fun z : ℂ => star (g z) * deriv g z) 0 r
      = 2 * (Real.pi : ℂ) * Complex.I * ((r : ℂ) ^ 2 + ∑' m : ℕ, α m * γ m) := by
    rw [circleIntegral.integral_congr hr0.le hpoint, hres]
  -- evaluation of the coefficient series
  have hcoeffterm : ∀ m : ℕ, α m * γ m = -(((m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) : ℝ) : ℂ) := by
    intro m
    rw [hαdef, hγdef]
    have hcm : star (c m) * c m = ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow]
    have hkey : star (c m) / (r : ℂ) ^ (2 * m) * (-(m : ℂ) * c m)
        = -((m : ℂ) * ((‖c m‖ ^ 2 : ℝ) : ℂ) / (r : ℂ) ^ (2 * m)) := by
      rw [← hcm]
      ring
    rw [hkey]
    congr 1
    push_cast
    rfl
  have hcoeff : (∑' m : ℕ, α m * γ m) = -((S : ℝ) : ℂ) := by
    rw [hSdef]
    calc (∑' m : ℕ, α m * γ m)
        = ∑' m : ℕ, -(((m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) : ℝ) : ℂ) :=
          tsum_congr hcoeffterm
      _ = -(∑' m : ℕ, (((m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) : ℝ) : ℂ)) := tsum_neg
      _ = -((∑' m : ℕ, (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m) : ℝ) : ℂ) := by
          rw [Complex.ofReal_tsum]
  -- final bookkeeping
  rw [hintegral, hcoeff]
  have hneg : ((r : ℂ) ^ 2 + -((S : ℝ) : ℂ)) = ((r : ℂ) ^ 2 - ((S : ℝ) : ℂ)) := by ring
  rw [hneg]
  have hscalar : ∀ Y : ℂ,
      (1 / (2 * Complex.I)) * (2 * (Real.pi : ℂ) * Complex.I * Y) = (Real.pi : ℂ) * Y := by
    intro Y
    field_simp
  exact hscalar _

end Work.Repel.Koebe
