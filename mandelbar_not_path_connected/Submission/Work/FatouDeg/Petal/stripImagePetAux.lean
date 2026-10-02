import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Topology
open Set Filter Metric

set_option maxHeartbeats 4000000

namespace Work.FatouDeg.Petal

/-! ## Generic elementary helpers -/

/-- The power-difference bound `‖a^n - b^n‖ ≤ n (max ‖a‖ ‖b‖)^{n-1} ‖a - b‖`. -/
private lemma norm_pow_sub_pow_le (a b : ℂ) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * (max ‖a‖ ‖b‖) ^ (n - 1) * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hMnn : 0 ≤ max ‖a‖ ‖b‖ := le_trans (norm_nonneg a) (le_max_left _ _)
      have ha : ‖a‖ ≤ max ‖a‖ ‖b‖ := le_max_left _ _
      have hpow : (k : ℝ) * max ‖a‖ ‖b‖ * (max ‖a‖ ‖b‖) ^ (k - 1)
          = (k : ℝ) * (max ‖a‖ ‖b‖) ^ k := by
        rcases k with _ | k'
        · simp
        · rw [show k' + 1 - 1 = k' by omega, pow_succ]; ring
      have hstep : a ^ (k + 1) - b ^ (k + 1)
          = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by
        rw [pow_succ, pow_succ]; ring
      have hidx : k + 1 - 1 = k := by omega
      rw [hstep, hidx]
      have hterm2 : ‖a - b‖ * ‖b ^ k‖ ≤ ‖a - b‖ * (max ‖a‖ ‖b‖) ^ k := by
        rw [norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg b) (le_max_right _ _) k) (norm_nonneg _)
      have hterm1 : ‖a‖ * ‖a ^ k - b ^ k‖
          ≤ max ‖a‖ ‖b‖ * ((k : ℝ) * (max ‖a‖ ‖b‖) ^ (k - 1) * ‖a - b‖) := by
        calc ‖a‖ * ‖a ^ k - b ^ k‖
            ≤ ‖a‖ * ((k : ℝ) * (max ‖a‖ ‖b‖) ^ (k - 1) * ‖a - b‖) :=
              mul_le_mul_of_nonneg_left ih (norm_nonneg a)
          _ ≤ max ‖a‖ ‖b‖ * ((k : ℝ) * (max ‖a‖ ‖b‖) ^ (k - 1) * ‖a - b‖) :=
              mul_le_mul_of_nonneg_right ha (by positivity)
      calc ‖a * (a ^ k - b ^ k) + (a - b) * b ^ k‖
          ≤ ‖a * (a ^ k - b ^ k)‖ + ‖(a - b) * b ^ k‖ := norm_add_le _ _
        _ = ‖a‖ * ‖a ^ k - b ^ k‖ + ‖a - b‖ * ‖b ^ k‖ := by rw [norm_mul, norm_mul]
        _ ≤ max ‖a‖ ‖b‖ * ((k : ℝ) * (max ‖a‖ ‖b‖) ^ (k - 1) * ‖a - b‖)
              + ‖a - b‖ * (max ‖a‖ ‖b‖) ^ k := add_le_add hterm1 hterm2
        _ = ((k + 1 : ℕ) : ℝ) * (max ‖a‖ ‖b‖) ^ k * ‖a - b‖ := by
              have h1 : max ‖a‖ ‖b‖ * ((k : ℝ) * (max ‖a‖ ‖b‖) ^ (k - 1) * ‖a - b‖)
                  = (k : ℝ) * (max ‖a‖ ‖b‖) ^ k * ‖a - b‖ := by
                rw [← hpow]; ring
              rw [h1]; push_cast; ring

/-! ## The `n`-th root `z0 = w ^ (-1/n)` and its elementary properties -/

/-- Principal-branch root: `zroot w n = exp (-(log w)/n)`, a solution of `z^n = w⁻¹`. -/
private noncomputable def zroot (w : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(Complex.log w) / (n : ℂ))

private lemma log_div_re (w : ℂ) (n : ℕ) :
    (-(Complex.log w) / (n : ℂ)).re = -(Real.log ‖w‖) / n := by
  rw [Complex.div_re]
  have hnr : ((n : ℕ) : ℂ).re = (n : ℝ) := by simp
  have hni : ((n : ℕ) : ℂ).im = 0 := by simp
  have hns : Complex.normSq ((n : ℕ) : ℂ) = (n : ℝ) * n := by
    rw [Complex.normSq_apply, hnr, hni]; ring
  rw [hnr, hni, hns, Complex.neg_re, Complex.log_re, Complex.neg_im, Complex.log_im]
  simp only [mul_zero]
  by_cases hn : (n:ℝ) = 0
  · rw [hn]; simp
  · field_simp; ring

private lemma log_div_im (w : ℂ) (n : ℕ) :
    (-(Complex.log w) / (n : ℂ)).im = -(w.arg) / n := by
  rw [Complex.div_im]
  have hnr : ((n : ℕ) : ℂ).re = (n : ℝ) := by simp
  have hni : ((n : ℕ) : ℂ).im = 0 := by simp
  have hns : Complex.normSq ((n : ℕ) : ℂ) = (n : ℝ) * n := by
    rw [Complex.normSq_apply, hnr, hni]; ring
  rw [hnr, hni, hns, Complex.neg_re, Complex.log_re, Complex.neg_im, Complex.log_im]
  simp only [mul_zero]
  by_cases hn : (n:ℝ) = 0
  · rw [hn]; simp
  · field_simp; ring

private lemma zroot_re (w : ℂ) (n : ℕ) :
    (zroot w n).re = Real.exp (-(Real.log ‖w‖) / n) * Real.cos (-(w.arg) / n) := by
  rw [zroot, Complex.exp_re, log_div_re, log_div_im]

private lemma zroot_im (w : ℂ) (n : ℕ) :
    (zroot w n).im = Real.exp (-(Real.log ‖w‖) / n) * Real.sin (-(w.arg) / n) := by
  rw [zroot, Complex.exp_im, log_div_re, log_div_im]

private lemma zroot_norm (w : ℂ) (n : ℕ) :
    ‖zroot w n‖ = Real.exp (-(Real.log ‖w‖) / n) := by
  rw [zroot, Complex.norm_exp, log_div_re]

private lemma zroot_pow (w : ℂ) (n : ℕ) (hn : 0 < n) (hw : w ≠ 0) :
    zroot w n ^ n = w⁻¹ := by
  have hnne : ((n : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (Nat.pos_iff_ne_zero.mp hn)
  calc zroot w n ^ n = Complex.exp (-(Complex.log w)) := by
        rw [zroot, ← Complex.exp_nat_mul]
        congr 1
        field_simp
    _ = w⁻¹ := by rw [Complex.exp_neg, Complex.exp_log hw]

private lemma zroot_norm_pow (w : ℂ) (n : ℕ) (hn : 0 < n) (hw : w ≠ 0) :
    ‖zroot w n‖ ^ n = ‖w‖⁻¹ := by
  rw [← norm_pow, zroot_pow w n hn hw, norm_inv]

/-- The real part of `-log w / n` in `zroot`, i.e. the argument bound. -/
private lemma abs_arg_le_im_div (τ : ℂ) (hre : 0 < τ.re) : |τ.arg| ≤ |τ.im| / τ.re := by
  have hle := Complex.abs_arg_le_pi_div_two_iff.mpr hre.le
  have hlt : τ.arg < Real.pi/2 := by
    refine lt_of_le_of_ne (le_trans (le_abs_self _) hle) ?_
    intro h
    rw [Complex.arg_eq_pi_div_two_iff] at h
    linarith [h.1]
  have hgt : -(Real.pi/2) < τ.arg := by
    refine lt_of_le_of_ne (le_trans (neg_le_neg hle) (neg_abs_le _)) ?_
    intro h
    have h2 : τ.arg = -(Real.pi/2) := h.symm
    rw [Complex.arg_eq_neg_pi_div_two_iff] at h2
    linarith [h2.1]
  rcases lt_or_ge τ.im 0 with him | him
  · have hargneg : τ.arg < 0 := Complex.arg_neg_iff.mpr him
    have hg : -(τ.arg) ≤ Real.tan (-(τ.arg)) := by
      apply Real.le_tan <;> linarith
    have htan : Real.tan (-(τ.arg)) = -τ.im/τ.re := by
      rw [Real.tan_neg, Complex.tan_arg]; ring
    rw [htan] at hg
    rw [abs_of_neg hargneg, abs_of_neg him]
    exact hg
  · have hargnn : 0 ≤ τ.arg := Complex.arg_nonneg_iff.mpr him
    have hg : τ.arg ≤ Real.tan τ.arg := Real.le_tan hargnn hlt
    rw [Complex.tan_arg] at hg
    rw [abs_of_nonneg hargnn, abs_of_nonneg him]
    exact hg

/-- `|Im zroot|` is small compared with the (positive) margin of the sector: for `|arg w| ≤ 1/4`
and `n ≥ 2` one has `Re zroot - (n+1)|Im zroot| ≥ ‖zroot‖/2`. -/
private lemma zroot_margin (n : ℕ) (hn : 2 ≤ n) (w : ℂ) (harg : |w.arg| ≤ 1/4) :
    (zroot w n).re - (n+1) * |(zroot w n).im| ≥ ‖zroot w n‖ / 2 := by
  set σ : ℝ := ‖zroot w n‖ with hσ
  set b : ℝ := -(w.arg) / n with hb
  have hσeq : σ = Real.exp (-(Real.log ‖w‖) / n) := by rw [hσ]; exact zroot_norm w n
  have hσpos : 0 < σ := by rw [hσeq]; positivity
  have hre : (zroot w n).re = σ * Real.cos b := by rw [zroot_re, hb, hσeq]
  have him : (zroot w n).im = σ * Real.sin b := by rw [zroot_im, hb, hσeq]
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hbn : |b| ≤ 1/(4*(n:ℝ)) := by
    rw [hb, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < n)]
    have h : (1/(4*(n:ℝ))) * n = 1/4 := by field_simp
    rw [h]; exact harg
  have hbsq : b^2/2 ≤ 1/128 := by
    have h1 : b^2 ≤ (1/(4*(n:ℝ)))^2 := by
      have h2 := abs_le.mp hbn
      nlinarith [h2.1, h2.2]
    have h3 : (1/(4*(n:ℝ)))^2 = 1/(16*(n:ℝ)^2) := by field_simp; ring
    rw [h3] at h1
    have h4 : 1/(16*(n:ℝ)^2) ≤ 1/64 := by
      rw [div_le_iff₀ (show (0:ℝ) < 16*(n:ℝ)^2 by positivity)]
      nlinarith
    linarith
  have hcos : Real.cos b ≥ 1 - 1/128 := by
    have := Real.one_sub_sq_div_two_le_cos (x := b)
    linarith
  have hmb : (n+1:ℝ) * |b| ≤ 3/8 := by
    have h1 : (n+1:ℝ) * |b| ≤ (n+1) * (1/(4*(n:ℝ))) :=
      mul_le_mul_of_nonneg_left hbn (by positivity)
    have h2 : (n+1:ℝ) * (1/(4*(n:ℝ))) ≤ 3/8 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 4*(n:ℝ))]
      nlinarith
    linarith
  have hmarg : Real.cos b - (n+1:ℝ) * |Real.sin b| ≥ 1/2 := by
    have hsin : (n+1:ℝ) * |Real.sin b| ≤ (n+1:ℝ) * |b| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by positivity)
    linarith
  have hbound : (zroot w n).re - (n+1) * |(zroot w n).im|
      = σ * (Real.cos b - (n+1) * |Real.sin b|) := by
    rw [hre, him, abs_mul, abs_of_pos hσpos]; ring
  rw [hbound]
  nlinarith [hσpos, hmarg]

/-- A threshold beyond which `log t / n + π ≤ t ^ (1 - 1/n)`. -/
private lemma exists_log_threshold (n : ℕ) (hn : 2 ≤ n) :
    ∃ N : ℝ, 0 < N ∧ ∀ t : ℝ, N ≤ t →
      Real.log t / n + Real.pi ≤ t ^ ((1:ℝ) - 1/(n:ℝ)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hθ : 0 < (1:ℝ) - 1/(n:ℝ) := by
    have : 1/(n:ℝ) ≤ 1/2 := by
      rw [one_div_le_one_div (by positivity) (by norm_num)]
      linarith
    linarith
  have hev1 : ∀ᶠ t : ℝ in Filter.atTop, Real.log t ≤ (1/(2*n)) * t ^ ((1:ℝ) - 1/(n:ℝ)) := by
    have hb := (isLittleO_log_rpow_atTop hθ).bound (show (0:ℝ) < 1/(2*n) by positivity)
    filter_upwards [hb, Filter.eventually_ge_atTop (1:ℝ)] with t ht ht1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1),
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at ht
    exact ht
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, Real.pi ≤ (1/2) * t ^ ((1:ℝ) - 1/(n:ℝ)) := by
    have htend := (tendsto_rpow_atTop hθ).eventually_ge_atTop (2*Real.pi)
    filter_upwards [htend] with t ht
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  have htN : N ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : (1:ℝ) ≤ t := le_trans (le_max_right _ _) ht
  obtain ⟨h1, h2⟩ := hN t htN
  have htθ : 0 ≤ t ^ ((1:ℝ) - 1/(n:ℝ)) := Real.rpow_nonneg (by linarith) _
  have h3 : Real.log t / n + Real.pi
      ≤ (1/(2*n)) * t ^ ((1:ℝ) - 1/(n:ℝ)) / n + (1/2) * t ^ ((1:ℝ) - 1/(n:ℝ)) := by
    have : Real.log t / n ≤ ((1/(2*n)) * t ^ ((1:ℝ) - 1/(n:ℝ))) / n :=
      div_le_div_of_nonneg_right h1 (by positivity)
    linarith
  refine le_trans h3 ?_
  have hfac : (1/(2*n)) * t ^ ((1:ℝ) - 1/(n:ℝ)) / n + (1/2) * t ^ ((1:ℝ) - 1/(n:ℝ))
      = t ^ ((1:ℝ) - 1/(n:ℝ)) * (1/(2*(n:ℝ)*(n:ℝ)) + 1/2) := by ring
  rw [hfac]
  have hle : 1/(2*(n:ℝ)*(n:ℝ)) + 1/2 ≤ 1 := by
    have hn2 : 1 ≤ (n:ℝ)*(n:ℝ) := by nlinarith
    have h5 : 1/(2*(n:ℝ)*(n:ℝ)) ≤ 1/2 := by
      rw [div_le_iff₀ (show (0:ℝ) < 2*(n:ℝ)*(n:ℝ) by positivity)]
      linarith
    linarith
  calc t ^ ((1:ℝ) - 1/(n:ℝ)) * (1/(2*(n:ℝ)*(n:ℝ)) + 1/2)
      ≤ t ^ ((1:ℝ) - 1/(n:ℝ)) * 1 := mul_le_mul_of_nonneg_left hle htθ
    _ = t ^ ((1:ℝ) - 1/(n:ℝ)) := by ring

/-- A key rpow identity: if `σ = T ^ (-1/n)` then `T ^ (1 - 1/n) * σ^(n-1) = 1`. -/
private lemma rpow_key (n : ℕ) (hn : 2 ≤ n) {T σ : ℝ} (hT : 0 < T)
    (hσ : σ = T ^ (-(1:ℝ)/(n:ℝ))) :
    T ^ ((1:ℝ) - 1/(n:ℝ)) * σ ^ (n-1) = 1 := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  rw [hσ]
  rw [← Real.rpow_natCast (T ^ (-(1:ℝ)/(n:ℝ))) (n-1)]
  rw [← Real.rpow_mul (le_of_lt hT) (-(1:ℝ)/(n:ℝ)) (((n-1:ℕ)):ℝ)]
  rw [← Real.rpow_add hT]
  rw [show (1:ℝ) - 1/(n:ℝ) + (-(1:ℝ)/(n:ℝ)) * (((n-1:ℕ)):ℝ) = 0 by
    rw [show (((n-1:ℕ)):ℝ) = (n:ℝ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp]
    field_simp
    ring]
  rw [Real.rpow_zero]

/-- Banach fixed point on a closed ball. -/
private theorem exists_fixedpoint_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E → E} {y : E} {ρ κ : ℝ} (hρ : 0 < ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hmaps : ‖f y - y‖ ≤ (1 - κ) * ρ)
    (hlip : ∀ z z' : E, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ → ‖f z - f z'‖ ≤ κ * ‖z - z'‖) :
    ∃ z : E, ‖z - y‖ ≤ ρ ∧ f z = z := by
  have hK1 : (⟨κ, hκ0⟩ : NNReal) < 1 := by show κ < 1; exact hκ1
  have hsmaps : Set.MapsTo f (Metric.closedBall y ρ) (Metric.closedBall y ρ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    have hz' : ‖z - y‖ ≤ ρ := by rwa [dist_eq_norm] at hz
    have hy' : ‖y - y‖ ≤ ρ := by simp only [sub_self, norm_zero]; exact le_of_lt hρ
    have h1 : ‖f z - f y‖ ≤ κ * ‖z - y‖ := hlip z y hz' hy'
    have h2 : ‖f y - y‖ ≤ (1 - κ) * ρ := hmaps
    rw [dist_eq_norm]
    calc ‖f z - y‖ = ‖(f z - f y) + (f y - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖f z - f y‖ + ‖f y - y‖ := norm_add_le _ _
      _ ≤ κ * ‖z - y‖ + (1 - κ) * ρ := add_le_add h1 h2
      _ ≤ κ * ρ + (1 - κ) * ρ :=
          add_le_add (mul_le_mul_of_nonneg_left hz' hκ0) le_rfl
      _ = ρ := by ring
  have hcontract : ContractingWith (⟨κ, hκ0⟩ : NNReal)
      (Set.MapsTo.restrict f (Metric.closedBall y ρ) (Metric.closedBall y ρ) hsmaps) := by
    refine ⟨hK1, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have hu : ‖(↑u : E) - y‖ ≤ ρ := by
      have := u.2; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    have hv : ‖(↑v : E) - y‖ ≤ ρ := by
      have := v.2; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    exact hlip ↑u ↑v hu hv
  obtain ⟨z, hz, hfix, -⟩ := hcontract.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hsmaps
    (Metric.mem_closedBall_self (le_of_lt hρ)) (edist_ne_top y (f y))
  exact ⟨z, by rwa [Metric.mem_closedBall, dist_eq_norm] at hz, hfix⟩

/-- **The Fatou coordinate maps the petal onto the tails of all horizontal strips.**

This is the version of `stripImageAux` in which the derivative normalisation is only assumed on the
petal `Pet m ρ` (not on the larger `Dom m ρ`), which is all the contraction argument uses: the
fixed point is produced in a ball `B(z₀,r) ⊆ Pet m ρ` around `z₀ = ((m-1)τ)^(-1/(m-1))`.

`phifun m G` is holomorphic on `Dom m ρ`, `‖deriv (phifun m G) z * z^m + 1‖ ≤ ε < 1/2` on
`Pet m ρ` (i.e. `φ'(z) ≈ -z^(-m)`), `phifun m G` differs from `Afun m G` by at most `D ‖z‖` on
`Dom m ρ`, `(Ppoly m G).eval w` is within `K ‖w‖` of its constant term `1/(m-1)` for `‖w‖ ≤ 1`,
and every point of `Pet m ρ` has the ball of radius `κ ‖z‖` around it inside `Dom m ρ`.  Then for
every `B ≥ 0` the tail of the strip `{τ : |Im τ| ≤ B}` is contained in the image of `Pet m ρ`.

Proof (contraction argument): given `τ` with `τ.re` large and `|τ.im| ≤ B`, put `z₀ = (n τ)^(-1/n)`
with `n = m-1` (principal branch), so that `(z₀^n)⁻¹ = n τ` and `z₀` lies in `Pet m ρ` provided
`τ.re` is large enough (its argument is `-arg(nτ)/n`, of modulus `< (1/2) arctan(1/m)`).
Then `Afun m G z₀ - τ = nτ (P(z₀) - 1/n) + β log z₀`, so by `hP` and `‖log z₀‖ ≤ (log(n|τ|))/n + π`
we get `‖phifun m G z₀ - τ‖ ≤ C₁ (|τ|^(1-1/n) + log|τ|) ≤ C₂ |τ|^(1-1/n)` for `|τ| ≥ 2`.
Now let `M = -z₀^(-m)` (a constant with `‖M‖ = ‖z₀‖^(-m)`), `r = K₀ |τ|^(-2/n)` with a large
constant `K₀` and consider `T z = z - (phifun m G z - τ)/M` on the closed ball `B(z₀, r)`.  On it
`‖T z - T z₀‖ ≤ (1/2)‖z - z₀‖` because
`‖1 - φ'(z)/M‖ ≤ ‖1 + φ'(z) z^m‖ + ‖φ'(z)(z^m - z₀^m)‖/‖z₀‖^m ≤ ε + m r/‖z₀‖ ≤ 1/2` for large
`|τ|`, while `‖T z₀ - z₀‖ = ‖φ z₀ - τ‖/‖M‖ ≤ C₂ n^(-1-1/n) |τ|^(-2/n) ≤ r/2`; so `T` has a
unique fixed point `z ∈ B(z₀, r)`, and `phifun m G z = τ`.  Since `r/‖z₀‖ = K₀ n^(1/n)|τ|^(-1/n) → 0`
and `z₀` sits at half of the petal's angular half-width, `B(z₀, r) ⊆ Pet m ρ` for large `|τ|`, so
the fixed point lies in the petal. -/
theorem stripImagePetAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ ε D K κ : ℝ} (hρ : 0 < ρ)
    (hε : ε < 1 / 2) (hD : 0 ≤ D) (hK : 0 ≤ K) (hκ : 0 < κ)
    (hdiff : DifferentiableOn ℂ (phifun m G) (Dom m ρ))
    (hderiv : ∀ z ∈ Pet m ρ, ‖deriv (phifun m G) z * z ^ m + 1‖ ≤ ε)
    (hgrowth : ∀ z ∈ Dom m ρ, ‖phifun m G z - Afun m G z‖ ≤ D * ‖z‖)
    (hP : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖(Ppoly m G).eval w - (1 / (((m - 1 : ℕ) : ℂ)))‖ ≤ K * ‖w‖)
    (hmargin : ∀ z ∈ Pet m ρ, ∀ w : ℂ, ‖w - z‖ ≤ κ * ‖z‖ → w ∈ Dom m ρ) :
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
      ∃ z ∈ Pet m ρ, phifun m G z = τ := by
  intro B hB
  -- ==================== elementary set-up ====================
  set n : ℕ := m - 1 with hndef
  have hn3 : 2 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hnne : n ≠ 0 := by omega
  have hmn : m = n + 1 := by omega
  have hmnn : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hmnne : (n:ℝ) ≠ 0 := ne_of_gt hmnn
  have hcast : (((m - 1 : ℕ)) : ℂ) = (n : ℂ) := by rw [hndef]
  have hε0 : 0 ≤ ε := by
    obtain ⟨z, hz⟩ := Pet_nonempty m (by omega : 1 ≤ m) hρ
    exact le_trans (norm_nonneg _) (hderiv z hz)
  set β : ℂ := betac m G with hβdef
  set C₂ : ℝ := D + K + ‖β‖ + 1 with hC₂def
  have hC₂pos : 0 < C₂ := by rw [hC₂def]; positivity
  set K₁ : ℝ := 2 * C₂ + 1 with hK₁def
  have hK₁pos : 0 < K₁ := by rw [hK₁def]; positivity
  have hC₂ge : D + K + ‖β‖ ≤ K₁ / 2 := by
    rw [hK₁def, hC₂def]; nlinarith [norm_nonneg β, hD, hK]
  have hε2 : 0 < 1/2 - ε := by linarith
  have h1ε : 0 < 1 + ε := by linarith
  set qd : ℝ := (1/2 - ε) / ((1+ε) * (2:ℝ)^(2*m-1) * m) with hqddef
  have hqdpos : 0 < qd := by rw [hqddef]; apply div_pos hε2; positivity
  set M : ℝ := max (max (2/ρ) 1) (max (8 * ((m:ℝ)+1) * K₁) (K₁/qd)) with hMdef
  have hMpos : 0 < M :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _))
  have hMgeρ : 2/ρ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMgeK : 8 * ((m:ℝ)+1) * K₁ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMgeqd : K₁/qd ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨Nlog, hNlogpos, hNlog⟩ := exists_log_threshold n hn2
  -- ==================== the threshold C ====================
  set C : ℝ := max (max (max (4*B) 1) (M^n / n)) (Nlog / n) with hCdef
  refine ⟨C, fun τ hτ hτim => ?_⟩
  have hC4B : 4*B ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC1 : (1:ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hCM : M^n / (n:ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCN : Nlog / (n:ℝ) ≤ C := le_max_right _ _
  have hs4B : 4*B < τ.re := lt_of_le_of_lt hC4B hτ
  have hs1 : (1:ℝ) < τ.re := lt_of_le_of_lt hC1 hτ
  have hsM : M^n / (n:ℝ) < τ.re := lt_of_le_of_lt hCM hτ
  have hsN : Nlog / (n:ℝ) < τ.re := lt_of_le_of_lt hCN hτ
  have hre : 0 < τ.re := by linarith
  have hnormτ_ge : (1:ℝ) ≤ ‖τ‖ := le_trans (le_of_lt hs1) (Complex.re_le_norm τ)
  have hτne : τ ≠ 0 := by intro h; rw [h] at hre; simp at hre
  -- ==================== the root z₀ ====================
  set ww : ℂ := (n:ℂ) * τ with hwwdef
  have hwwne : ww ≠ 0 := by
    rw [hwwdef]; exact mul_ne_zero (by exact_mod_cast hnne) hτne
  have hT : ‖ww‖ = (n:ℝ) * ‖τ‖ := by rw [hwwdef, norm_mul, Complex.norm_natCast]
  have hTpos : 0 < ‖ww‖ := norm_pos_iff.mpr hwwne
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hTge1 : (1:ℝ) ≤ ‖ww‖ := by rw [hT]; nlinarith [hn1R, hnormτ_ge]
  have hTM : M^n ≤ ‖ww‖ := by
    rw [hT]
    have h := hsM
    rw [div_lt_iff₀ hmnn] at h
    nlinarith [Complex.re_le_norm τ, h]
  have hTN : Nlog ≤ ‖ww‖ := by
    rw [hT]
    have h := hsN
    rw [div_lt_iff₀ hmnn] at h
    nlinarith [Complex.re_le_norm τ, h]
  set z0 : ℂ := zroot ww n with hz0def
  set σ : ℝ := ‖z0‖ with hσdef
  have hz0pow : z0 ^ n = ww⁻¹ := by rw [hz0def]; exact zroot_pow ww n hnpos hwwne
  have hz0ne : z0 ≠ 0 := by
    intro h
    rw [h, zero_pow hnne] at hz0pow
    exact (inv_ne_zero hwwne) hz0pow.symm
  have hσpow : σ ^ n = ‖ww‖⁻¹ := by rw [hσdef, hz0def]; exact zroot_norm_pow ww n hnpos hwwne
  have hσpos : 0 < σ := by rw [hσdef]; exact norm_pos_iff.mpr hz0ne
  have hσnn : 0 ≤ σ := le_of_lt hσpos
  have hσle1 : σ ≤ 1 := by
    have h1 : σ ^ n ≤ (1:ℝ)^n := by
      rw [hσpow, one_pow, inv_le_one₀ hTpos]
      exact hTge1
    exact (pow_le_pow_iff_left₀ hσnn zero_le_one hnne).mp h1
  have hσM : σ ≤ 1/M := by
    have h1 : σ ^ n ≤ (1/M)^n := by
      rw [hσpow, one_div, inv_pow]
      exact (inv_le_inv₀ hTpos (pow_pos hMpos n)).mpr hTM
    exact (pow_le_pow_iff_left₀ hσnn (by positivity) hnne).mp h1
  have hσhρ : σ ≤ ρ/2 := by
    have h1 : (1:ℝ)/M ≤ ρ/2 := by
      rw [div_le_iff₀ hMpos]
      rw [div_le_iff₀ hρ] at hMgeρ
      nlinarith
    linarith
  have hσK : K₁ * σ ≤ 1/(8*((m:ℝ)+1)) := by
    have h1 : (1:ℝ)/M ≤ 1/(8*((m:ℝ)+1)*K₁) :=
      one_div_le_one_div_of_le (by positivity) hMgeK
    calc K₁ * σ ≤ K₁ * (1/M) := mul_le_mul_of_nonneg_left hσM (le_of_lt hK₁pos)
      _ ≤ K₁ * (1/(8*((m:ℝ)+1)*K₁)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hK₁pos)
      _ = 1/(8*((m:ℝ)+1)) := by field_simp
  have hσqd : K₁ * σ ≤ qd := by
    have h1 : (1:ℝ)/M ≤ qd/K₁ := by
      have h2 := one_div_le_one_div_of_le (show (0:ℝ) < K₁/qd by positivity) hMgeqd
      rwa [one_div_div] at h2
    calc K₁ * σ ≤ K₁ * (1/M) := mul_le_mul_of_nonneg_left hσM (le_of_lt hK₁pos)
      _ ≤ K₁ * (qd/K₁) := mul_le_mul_of_nonneg_left h1 (le_of_lt hK₁pos)
      _ = qd := by field_simp
  -- argument of ww
  have harg1 : |ww.arg| ≤ 1/4 := by
    have hwa : ww.arg = τ.arg := by
      rw [hwwdef]
      rw [show (n:ℂ) = ((n:ℝ):ℂ) by push_cast; ring]
      exact Complex.arg_real_mul τ hmnn
    rw [hwa]
    have h1 := abs_arg_le_im_div τ hre
    have h2 : |τ.im| / τ.re ≤ 1/4 := by
      rw [div_le_iff₀ hre]
      nlinarith [hτim, hs4B]
    linarith
  -- z₀ lies in the petal
  have hmarg0 : z0.re - m * |z0.im| ≥ σ/2 := by
    have h := zroot_margin n hn2 ww harg1
    have h' : z0.re - (n+1) * |z0.im| ≥ σ/2 := by
      simpa only [← hz0def, ← hσdef] using h
    rw [hmn]
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hz0Pet : z0 ∈ Pet m ρ := by
    rw [mem_Pet]
    exact ⟨by linarith [hσhρ, hσpos], by linarith [hmarg0]⟩
  have hz0Dom : z0 ∈ Dom m ρ := Pet_subset_Dom m (by omega) ρ hz0Pet
  -- ==================== the ball is inside the petal ====================
  set r : ℝ := K₁ * σ^2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrσ : r ≤ σ/2 := by
    rw [hrdef]
    have h1 : K₁ * σ ≤ 1/2 := by
      have h2 : (1:ℝ)/(8*((m:ℝ)+1)) ≤ 1/2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*((m:ℝ)+1))]
        nlinarith
      linarith
    calc K₁ * σ^2 = σ * (K₁*σ) := by ring
      _ ≤ σ * (1/2) := mul_le_mul_of_nonneg_left h1 hσnn
      _ = σ/2 := by ring
  have hrσ4 : ((m:ℝ)+1) * r ≤ σ/4 := by
    rw [hrdef]
    have h1 : ((m:ℝ)+1) * K₁ * σ ≤ 1/8 := by
      have h2 : ((m:ℝ)+1) * (1/(8*((m:ℝ)+1))) = 1/8 := by field_simp
      calc ((m:ℝ)+1) * K₁ * σ = ((m:ℝ)+1) * (K₁*σ) := by ring
        _ ≤ ((m:ℝ)+1) * (1/(8*((m:ℝ)+1))) := mul_le_mul_of_nonneg_left hσK (by positivity)
        _ = 1/8 := h2
    calc ((m:ℝ)+1) * (K₁ * σ^2) = (((m:ℝ)+1) * K₁ * σ) * σ := by ring
      _ ≤ (1/8) * σ := mul_le_mul_of_nonneg_right h1 hσnn
      _ ≤ σ/4 := by linarith [hσnn]
  have hballPet : ∀ z : ℂ, ‖z - z0‖ ≤ r → z ∈ Pet m ρ := by
    intro z hzr
    rw [mem_Pet]
    refine ⟨?_, ?_⟩
    · have h1 : ‖z‖ ≤ σ + r := by
        have h2 : ‖z‖ ≤ ‖z - z0‖ + ‖z0‖ := by
          calc ‖z‖ = ‖(z - z0) + z0‖ := by ring_nf
            _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
        have h4 : ‖z0‖ = σ := hσdef.symm
        linarith
      linarith [h1, hrσ, hσhρ, hσpos]
    · have h3 : |z.im| ≤ |z0.im| + r := by
        have h4 : |z.im - z0.im| ≤ r := by
          have h5 : |(z - z0).im| ≤ ‖z - z0‖ := Complex.abs_im_le_norm _
          rw [Complex.sub_im] at h5
          linarith
        calc |z.im| = |z0.im + (z.im - z0.im)| := by ring_nf
          _ ≤ |z0.im| + |z.im - z0.im| := abs_add_le _ _
          _ ≤ |z0.im| + r := by linarith
      have h5 : z0.re - r ≤ z.re := by
        have h6 : (z0 - z).re ≤ ‖z0 - z‖ := Complex.re_le_norm _
        rw [Complex.sub_re, norm_sub_rev] at h6
        linarith
      have h7 : (m:ℝ) * |z0.im| + m * r + r < z0.re := by
        have h8 : (m:ℝ) * |z0.im| + σ/2 ≤ z0.re := by linarith [hmarg0]
        have h9 : (m:ℝ) * r + r ≤ σ/4 := by nlinarith [hrσ4]
        nlinarith [h8, h9, hσpos]
      calc m * |z.im| ≤ m * (|z0.im| + r) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = m * |z0.im| + m * r := by ring
        _ < z0.re - r := by linarith [h7]
        _ ≤ z.re := h5
  -- ==================== the derivative bound on the ball ====================
  have hDerivBound : ∀ z : ℂ, ‖z - z0‖ ≤ r → ‖deriv (phifun m G) z * z0 ^ m + 1‖ ≤ 1/2 := by
    intro z hzr
    have hzPet := hballPet z hzr
    have hnormz_ge : σ/2 ≤ ‖z‖ := by
      have h1 : |σ - ‖z‖| ≤ r := by
        have h2 : |‖z0‖ - ‖z‖| ≤ ‖z0 - z‖ := abs_norm_sub_norm_le z0 z
        rw [hσdef.symm, norm_sub_rev] at h2
        linarith [h2, hzr]
      have h3 := abs_le.mp h1
      linarith [h3.1, hσpos]
    have hznormpos : 0 < ‖z‖ := by linarith [hnormz_ge, hσpos]
    have hdphi : ‖deriv (phifun m G) z * z ^ m‖ ≤ 1 + ε := by
      have h1 := hderiv z hzPet
      have h2 : ‖deriv (phifun m G) z * z ^ m‖
          ≤ ‖deriv (phifun m G) z * z^m + 1‖ + 1 := by
        calc ‖deriv (phifun m G) z * z ^ m‖ = ‖(deriv (phifun m G) z * z^m + 1) - 1‖ := by
              rw [add_sub_cancel_right]
          _ ≤ ‖deriv (phifun m G) z * z^m + 1‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
          _ = ‖deriv (phifun m G) z * z^m + 1‖ + 1 := by rw [norm_one]
      linarith
    have hzpow_bound : ‖z0 ^ m - z ^ m‖ ≤ (m:ℝ) * ((2*σ)^(m-1)) * r := by
      have h1 := norm_pow_sub_pow_le z0 z m
      have hmax : max ‖z0‖ ‖z‖ ≤ 2*σ := by
        have h3 : ‖z‖ ≤ σ + r := by
          have h4 : ‖z‖ ≤ ‖z - z0‖ + ‖z0‖ := by
            calc ‖z‖ = ‖(z - z0) + z0‖ := by ring_nf
              _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
          have h5 : ‖z0‖ = σ := hσdef.symm
          linarith
        rw [max_le_iff]
        exact ⟨by rw [hσdef]; linarith [hσpos, hrσ], by linarith [h3, hrσ]⟩
      have h2 : (max ‖z0‖ ‖z‖)^(m-1) ≤ (2*σ)^(m-1) :=
        pow_le_pow_left₀ (by positivity) hmax (m-1)
      have h3 : ‖z0 - z‖ ≤ r := by rwa [norm_sub_rev] at hzr
      calc ‖z0 ^ m - z ^ m‖ ≤ (m:ℝ) * (max ‖z0‖ ‖z‖)^(m-1) * ‖z0 - z‖ := h1
        _ ≤ (m:ℝ) * (2*σ)^(m-1) * r := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left h2 (by positivity)
            · exact h3
            · exact norm_nonneg _
            · positivity
    have hσm_le : σ^m ≤ (2:ℝ)^m * ‖z‖^m := by
      have h7 : σ ≤ 2*‖z‖ := by linarith [hnormz_ge]
      calc σ^m ≤ (2*‖z‖)^m := pow_le_pow_left₀ hσnn h7 m
        _ = (2:ℝ)^m * ‖z‖^m := by rw [mul_pow]
    have hfinal : ‖deriv (phifun m G) z * (z0^m - z^m)‖ ≤ 1/2 - ε := by
      rw [norm_mul]
      have h1 : ‖deriv (phifun m G) z‖ ≤ (1+ε)/‖z‖^m := by
        rw [le_div_iff₀ (pow_pos hznormpos m)]
        have := hdphi
        rwa [norm_mul, norm_pow] at this
      have h2 : ‖deriv (phifun m G) z‖ * ‖z0^m - z^m‖
          ≤ ((1+ε)/‖z‖^m) * ((m:ℝ) * ((2*σ)^(m-1)) * r) :=
        mul_le_mul h1 hzpow_bound (norm_nonneg _) (by positivity)
      refine le_trans h2 ?_
      have h3 : ((1+ε)/‖z‖^m) * ((m:ℝ) * ((2*σ)^(m-1)) * r)
          ≤ (1+ε) * (m:ℝ) * (2:ℝ)^(2*m-1) * (K₁*σ) := by
        rw [hrdef]
        have h4 : (1+ε)/‖z‖^m ≤ (1+ε) * (2:ℝ)^m / σ^m := by
          have h5 : (1:ℝ)/‖z‖^m ≤ (2:ℝ)^m/σ^m := by
            rw [div_le_iff₀ (pow_pos hznormpos m)]
            have h6 : σ^m ≤ (2:ℝ)^m * ‖z‖^m := hσm_le
            rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hσpos m)]
            simpa using h6
          calc (1+ε)/‖z‖^m = (1+ε) * (1/‖z‖^m) := by ring
            _ ≤ (1+ε) * ((2:ℝ)^m/σ^m) := mul_le_mul_of_nonneg_left h5 h1ε.le
            _ = (1+ε) * (2:ℝ)^m / σ^m := by ring
        calc ((1+ε)/‖z‖^m) * ((m:ℝ) * ((2*σ)^(m-1)) * (K₁*σ^2))
            ≤ ((1+ε) * (2:ℝ)^m / σ^m) * ((m:ℝ) * ((2*σ)^(m-1)) * (K₁*σ^2)) := by
              apply mul_le_mul_of_nonneg_right h4; positivity
          _ = (1+ε) * (m:ℝ) * (2:ℝ)^(2*m-1) * (K₁*σ) := by
              rw [mul_pow]
              have hm1 : (0:ℝ) < σ ^ m := pow_pos hσpos m
              field_simp
              have e1 : (2:ℝ)^m * (2:ℝ)^(m-1) = (2:ℝ)^(2*m-1) := by
                rw [← pow_add]; congr 1; omega
              have e2 : σ^(m-1) * σ = σ^m := by rw [← pow_succ]; congr 1; omega
              calc 2 ^ m * 2 ^ (m - 1) * σ ^ (m - 1) * σ
                  = ((2:ℝ)^m * (2:ℝ)^(m-1)) * (σ^(m-1) * σ) := by ring
                _ = σ ^ m * 2 ^ (2 * m - 1) := by rw [e1, e2]; ring
      refine le_trans h3 ?_
      have h7 : (1+ε) * (m:ℝ) * (2:ℝ)^(2*m-1) * (K₁*σ)
          ≤ (1+ε) * (m:ℝ) * (2:ℝ)^(2*m-1) * qd := by
        apply mul_le_mul_of_nonneg_left hσqd; positivity
      refine le_trans h7 ?_
      rw [hqddef]
      have hD : ((1+ε) * (2:ℝ)^(2*m-1) * m) ≠ 0 := by positivity
      rw [show (1+ε) * (m:ℝ) * (2:ℝ)^(2*m-1) * ((1/2-ε) / ((1+ε) * (2:ℝ)^(2*m-1) * m))
          = (1/2-ε) by
        rw [show (1+ε) * (m:ℝ) * (2:ℝ)^(2*m-1) = (1+ε) * (2:ℝ)^(2*m-1) * m by ring]
        exact mul_div_cancel₀ (1/2-ε) hD]
    have hsplit : deriv (phifun m G) z * z0^m + 1
        = (deriv (phifun m G) z * z^m + 1) + deriv (phifun m G) z * (z0^m - z^m) := by ring
    rw [hsplit]
    calc ‖(deriv (phifun m G) z * z ^ m + 1) + deriv (phifun m G) z * (z0^m - z^m)‖
        ≤ ‖deriv (phifun m G) z * z ^ m + 1‖ + ‖deriv (phifun m G) z * (z0^m - z^m)‖ :=
          norm_add_le _ _
      _ ≤ ε + (1/2 - ε) := by
          apply add_le_add (hderiv z hzPet)
          exact hfinal
      _ = 1/2 := by ring
  -- ==================== the center bound ====================
  have hcenter : ‖phifun m G z0 - τ‖ * σ^(n-1) ≤ K₁/2 := by
    have hTpos' := hTpos
    have hσrpow : σ = ‖ww‖ ^ (-(1:ℝ)/(n:ℝ)) := by
      have hpow2 : (‖ww‖ ^ (-(1:ℝ)/(n:ℝ)))^n = ‖ww‖⁻¹ := by
        rw [show (-(1:ℝ)/(n:ℝ)) = -((n:ℝ)⁻¹) by rw [div_eq_mul_inv, neg_mul, one_mul]]
        rw [Real.rpow_neg (le_of_lt hTpos'), inv_pow,
          Real.rpow_inv_natCast_pow (le_of_lt hTpos') hnne]
      have h1 : σ^n = (‖ww‖ ^ (-(1:ℝ)/(n:ℝ)))^n := by rw [hσpow, hpow2]
      exact le_antisymm
        ((pow_le_pow_iff_left₀ hσnn (Real.rpow_nonneg (norm_nonneg _) _) hnne).mp (le_of_eq h1))
        ((pow_le_pow_iff_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hσnn hnne).mp (le_of_eq h1.symm))
    have hrpowkey : ‖ww‖ ^ ((1:ℝ) - 1/(n:ℝ)) * σ^(n-1) = 1 :=
      rpow_key n hn2 hTpos' hσrpow
    have hTσ : ‖ww‖ * σ^n = 1 := by
      rw [hσpow, mul_inv_cancel₀ (ne_of_gt hTpos')]
    have hσsucc : σ * σ^(n-1) = σ^n := by
      rw [← pow_succ' σ (n-1)]; congr 1; omega
    have hlogterm : (Real.log ‖ww‖ / n + Real.pi) * σ^(n-1) ≤ 1 := by
      have h1 : Real.log ‖ww‖ / n + Real.pi ≤ ‖ww‖ ^ ((1:ℝ)-1/(n:ℝ)) := hNlog ‖ww‖ hTN
      have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hσnn (n-1))
      rwa [hrpowkey] at h2
    have hPz' : ‖(Ppoly m G).eval z0 - (1/(n:ℂ))‖ ≤ K * σ := by
      have h1 := hP z0 (by rw [← hσdef]; exact hσle1)
      rw [hcast] at h1
      rw [← hσdef] at h1
      exact h1
    have hTA : ‖ww * ((Ppoly m G).eval z0 - (1/(n:ℂ)))‖ * σ^(n-1) ≤ K := by
      rw [norm_mul]
      have h1 := mul_le_mul_of_nonneg_left hPz' (norm_nonneg ww)
      have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hσnn (n-1))
      refine le_trans h2 ?_
      exact le_of_eq (by
        calc ‖ww‖ * (K*σ) * σ^(n-1) = K * (‖ww‖ * (σ * σ^(n-1))) := by ring
          _ = K * (‖ww‖ * σ^n) := by rw [hσsucc]
          _ = K := by rw [hTσ]; ring)
    have hlogz : ‖Complex.log z0‖ ≤ Real.log ‖ww‖ / n + Real.pi := by
      have h1 : (Complex.log z0).re = -(Real.log ‖ww‖) / n := by
        rw [Complex.log_re, show ‖z0‖ = Real.exp (-(Real.log ‖ww‖)/n) from zroot_norm ww n,
          Real.log_exp]
      have h2 : |(Complex.log z0).im| ≤ Real.pi := by
        rw [Complex.log_im]; exact Complex.abs_arg_le_pi z0
      calc ‖Complex.log z0‖ ≤ |(Complex.log z0).re| + |(Complex.log z0).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = Real.log ‖ww‖ / n + |(Complex.log z0).im| := by
              rw [h1, abs_div, abs_neg, abs_of_nonneg hmnn.le,
                abs_of_nonneg (Real.log_nonneg hTge1)]
        _ ≤ Real.log ‖ww‖ / n + Real.pi := by linarith
    have hTB : ‖β * Complex.log z0‖ * σ^(n-1) ≤ ‖β‖ := by
      rw [norm_mul]
      have h1 := mul_le_mul_of_nonneg_left hlogz (norm_nonneg β)
      have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hσnn (n-1))
      refine le_trans h2 ?_
      calc ‖β‖ * (Real.log ‖ww‖ / n + Real.pi) * σ^(n-1)
          = ‖β‖ * ((Real.log ‖ww‖ / n + Real.pi) * σ^(n-1)) := by ring
        _ ≤ ‖β‖ * 1 := mul_le_mul_of_nonneg_left hlogterm (norm_nonneg β)
        _ = ‖β‖ := by ring
    have hAfun : Afun m G z0 = ww * (Ppoly m G).eval z0 + β * Complex.log z0 := by
      rw [Afun]
      rw [show m - 1 = n by omega, hz0pow, inv_inv, ← hβdef]
    have hτw : τ = ww * (n:ℂ)⁻¹ := by
      rw [hwwdef]; field_simp
    have hTA' : ‖Afun m G z0 - τ‖ * σ^(n-1) ≤ K + ‖β‖ := by
      rw [hAfun, hτw]
      have hsplit : ww * (Ppoly m G).eval z0 + β * Complex.log z0 - ww * (n:ℂ)⁻¹
          = ww * ((Ppoly m G).eval z0 - (1/(n:ℂ))) + β * Complex.log z0 := by
        rw [one_div]; ring
      rw [hsplit]
      calc ‖ww * ((Ppoly m G).eval z0 - (1/(n:ℂ))) + β * Complex.log z0‖ * σ^(n-1)
          ≤ (‖ww * ((Ppoly m G).eval z0 - (1/(n:ℂ)))‖ + ‖β * Complex.log z0‖) * σ^(n-1) :=
            mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hσnn (n-1))
        _ = ‖ww * ((Ppoly m G).eval z0 - (1/(n:ℂ)))‖ * σ^(n-1)
              + ‖β * Complex.log z0‖ * σ^(n-1) := by ring
        _ ≤ K + ‖β‖ := add_le_add hTA hTB
    have hTD : ‖phifun m G z0 - Afun m G z0‖ * σ^(n-1) ≤ D := by
      have h1 := hgrowth z0 hz0Dom
      have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hσnn (n-1))
      refine le_trans h2 ?_
      calc (D*σ) * σ^(n-1) = D * (σ*σ^(n-1)) := by ring
        _ = D * σ^n := by rw [hσsucc]
        _ = D * ‖ww‖⁻¹ := by rw [hσpow]
        _ ≤ D * 1 := mul_le_mul_of_nonneg_left (by rw [inv_le_one₀ hTpos']; exact hTge1) hD
        _ = D := by ring
    have hmain : ‖phifun m G z0 - τ‖ * σ^(n-1) ≤ (D + ‖β‖) + K := by
      have hsplit : phifun m G z0 - τ = (phifun m G z0 - Afun m G z0) + (Afun m G z0 - τ) := by
        ring
      rw [hsplit]
      calc ‖(phifun m G z0 - Afun m G z0) + (Afun m G z0 - τ)‖ * σ^(n-1)
          ≤ (‖phifun m G z0 - Afun m G z0‖ + ‖Afun m G z0 - τ‖) * σ^(n-1) :=
            mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hσnn (n-1))
        _ = ‖phifun m G z0 - Afun m G z0‖ * σ^(n-1) + ‖Afun m G z0 - τ‖ * σ^(n-1) := by ring
        _ ≤ D + (K + ‖β‖) := add_le_add hTD hTA'
        _ = (D + ‖β‖) + K := by ring
    refine le_trans hmain ?_
    linarith [hC₂ge]
  -- ==================== the fixed point ====================
  set F : ℂ → ℂ := fun y => y + (phifun m G y - τ) * z0^m with hFdef
  have hmaps : ‖F z0 - z0‖ ≤ (1 - 1/2) * r := by
    have h1 : F z0 - z0 = (phifun m G z0 - τ) * z0^m := by rw [hFdef]; ring
    rw [h1, norm_mul]
    have h2 : ‖z0^m‖ = σ^m := by rw [norm_pow, hσdef]
    rw [h2]
    have h3 : σ^m = σ^(n-1) * σ^2 := by
      rw [hmn, show n + 1 = (n-1) + 2 by omega, pow_add]
    rw [h3]
    calc ‖phifun m G z0 - τ‖ * (σ^(n-1) * σ^2)
        = (‖phifun m G z0 - τ‖ * σ^(n-1)) * σ^2 := by ring
      _ ≤ (K₁/2) * σ^2 := mul_le_mul_of_nonneg_right hcenter (sq_nonneg σ)
      _ = (1 - 1/2) * r := by rw [hrdef]; ring
  have hlip : ∀ z z' : ℂ, ‖z - z0‖ ≤ r → ‖z' - z0‖ ≤ r →
      ‖F z - F z'‖ ≤ (1/2) * ‖z - z'‖ := by
    intro z z' hz hz'
    have hf : ∀ y ∈ Metric.closedBall z0 r, DifferentiableAt ℂ F y := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      have hyDom : y ∈ Dom m ρ := Pet_subset_Dom m (by omega) ρ (hballPet y hy)
      have hd : DifferentiableAt ℂ (phifun m G) y :=
        hdiff.differentiableAt ((isOpen_Dom m ρ).mem_nhds hyDom)
      rw [hFdef]
      exact differentiableAt_id.add ((hd.sub_const τ).mul_const (z0^m))
    have hb : ∀ y ∈ Metric.closedBall z0 r, ‖deriv F y‖ ≤ 1/2 := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      have hyDom : y ∈ Dom m ρ := Pet_subset_Dom m (by omega) ρ (hballPet y hy)
      have hderivy : deriv F y = 1 + deriv (phifun m G) y * z0^m := by
        rw [hFdef]
        have hd : DifferentiableAt ℂ (phifun m G) y :=
          hdiff.differentiableAt ((isOpen_Dom m ρ).mem_nhds hyDom)
        have hA : HasDerivAt (fun y : ℂ => (phifun m G y - τ) * z0^m)
            (deriv (phifun m G) y * z0^m) y := hd.hasDerivAt.sub_const τ |>.mul_const (z0^m)
        exact ((hasDerivAt_id y).add hA).deriv
      rw [hderivy, add_comm]
      exact hDerivBound y hy
    have hzc : z ∈ Metric.closedBall z0 r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
    have hz'c : z' ∈ Metric.closedBall z0 r := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz'
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_closedBall z0 r) hzc hz'c
    simpa only [norm_sub_rev] using h
  obtain ⟨z, hzball, hzfix⟩ :=
    exists_fixedpoint_closedBall hrpos (by norm_num) (by norm_num) hmaps hlip
  refine ⟨z, hballPet z hzball, ?_⟩
  have h1 : F z = z := hzfix
  have h2 : (phifun m G z - τ) * z0^m = 0 := by
    rw [hFdef] at h1
    exact add_left_cancel (by rw [add_zero]; exact h1)
  have hz0mpow : z0^m ≠ 0 := pow_ne_zero _ hz0ne
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hz0mpow)


end Work.FatouDeg.Petal
