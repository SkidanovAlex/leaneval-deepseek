import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Kser_gp_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Development: unit-window mean-square bound for `Ψ₂ = Ψ - Ψ₁`
-/

namespace Work.BMF.mrlas.hsb

open Finset Real Complex

noncomputable section

/-- `locP f p x = Σ_e f (p^e) x^e`: the local Euler factor of `f` at `p` in the variable
`x = p^{-s}`. -/
noncomputable def locP (f : ℕ → ℂ) (p : ℕ) (x : ℂ) : ℂ := ∑' e : ℕ, f (p ^ e) * x ^ e

/-- `locD f p x = Σ_e e f (p^e) x^{e-1}`: the `x`-derivative of `locP`. -/
noncomputable def locD (f : ℕ → ℂ) (p : ℕ) (x : ℂ) : ℂ :=
  ∑' e : ℕ, (e : ℂ) * f (p ^ e) * x ^ (e - 1)

/-- `locB f p x = Σ_j ((j+2) f (p^{j+2}) - f p · (j+1) f (p^{j+1})) x^j`; it records the
`x²`-correction `locD - f p · locP = x · locB`. -/
noncomputable def locB (f : ℕ → ℂ) (p : ℕ) (x : ℂ) : ℂ :=
  ∑' j : ℕ, (((j + 2 : ℕ) : ℂ) * f (p ^ (j + 2)) - f p * f (p ^ (j + 1))) * x ^ j

lemma term_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p ≠ 0) (s : ℂ) (e : ℕ) :
    LSeries.term f s (p ^ e) = f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp
    have hlog : (Complex.log (p : ℂ) * (e : ℂ)).im = 0 := by
      have h1 : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) :=
        (Complex.ofReal_log (Nat.cast_nonneg p)).symm
      have h2 : ((Real.log p : ℝ) : ℂ) * ((e : ℕ) : ℂ) = (((Real.log p) * (e : ℝ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, h2, Complex.ofReal_im]
    have key : (((p ^ e : ℕ) : ℂ)) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e := by
      calc (((p ^ e : ℕ) : ℂ)) ^ (-s) = ((p : ℂ) ^ e) ^ (-s) := by rw [Nat.cast_pow]
        _ = ((p : ℂ) ^ (e : ℂ)) ^ (-s) := by rw [Complex.cpow_natCast]
        _ = (p : ℂ) ^ ((e : ℂ) * (-s)) :=
              (Complex.cpow_mul (-s) (by rw [hlog]; linarith [Real.pi_pos])
                (by rw [hlog]; linarith [Real.pi_pos])).symm
        _ = ((p : ℂ) ^ (-s)) ^ e := Complex.cpow_nat_mul (p : ℂ) e (-s)
    rw [LSeries.term_of_ne_zero hpe, div_eq_mul_inv, ← Complex.cpow_neg, key]

lemma gp_eq_locP (f : ℕ → ℂ) {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    gp f p s = locP f p ((p : ℂ) ^ (-s)) := by
  rw [gp, locP]
  exact tsum_congr (fun e => term_prime_pow f hp s e)

lemma locP_summable (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun e : ℕ => f (p ^ e) * x ^ e) := by
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hg : Summable (fun e : ℕ => (‖x‖ : ℝ) ^ e) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hr])
  refine Summable.of_norm_bounded hg (fun e => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg hr e) (hb _)

lemma locD_summable (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun e : ℕ => (e : ℂ) * f (p ^ e) * x ^ (e - 1)) := by
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hnorm : ∀ e : ℕ, ‖(e : ℂ) * f (p ^ e) * x ^ (e - 1)‖ ≤ (e : ℝ) * ‖x‖ ^ (e - 1) := by
    intro e
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (pow_nonneg hr _) (hb _)) (Nat.cast_nonneg e)
  have hpow : Summable (fun e : ℕ => (e : ℝ) * ‖x‖ ^ e) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := (‖x‖ : ℝ)) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr])
    simpa using this
  have hgeo : Summable (fun e : ℕ => (‖x‖ : ℝ) ^ e) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hr])
  have h2 : Summable (fun e : ℕ => (e : ℝ) * ‖x‖ ^ e + ‖x‖ ^ e) := hpow.add hgeo
  have h3 : Summable (fun e : ℕ => ((e + 1 : ℕ) : ℝ) * ‖x‖ ^ e) := by
    refine h2.congr (fun e => ?_); push_cast; ring
  have h4 : Summable (fun e : ℕ => (e : ℝ) * ‖x‖ ^ (e - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine h3.congr (fun e => ?_)
    simp only [Nat.add_sub_cancel]
  exact Summable.of_norm_bounded h4 (fun e => hnorm e)

lemma locP_zero (f : ℕ → ℂ) (p : ℕ) : locP f p 0 = f 1 := by
  have hsum : Summable (fun e : ℕ => f (p ^ e) * (0 : ℂ) ^ e) := by
    refine summable_of_ne_finset_zero (s := {0}) (fun e he => ?_)
    have he' : e ≠ 0 := by simpa using he
    rw [zero_pow he', mul_zero]
  rw [locP, Summable.tsum_eq_zero_add hsum]
  have hz : (∑' e : ℕ, f (p ^ (e + 1)) * (0 : ℂ) ^ (e + 1)) = 0 := by simp
  rw [hz]; simp

/-- Tail estimate for the local power series. -/
lemma norm_locP_tail_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} {x : ℂ} {ρ : ℝ}
    (hx : ‖x‖ ≤ ρ) (hρ : ρ < 1) :
    ‖∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1)‖ ≤ ρ / (1 - ρ) := by
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hnorm_term : ∀ e : ℕ, ‖f (p ^ (e + 1)) * x ^ (e + 1)‖ ≤ ‖x‖ ^ (e + 1) := by
    intro e; rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg hr _) (hb _)
  have hgeo : Summable (fun e : ℕ => (‖x‖ : ℝ) ^ e) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hr]; exact lt_of_le_of_lt hx hρ)
  have hgeo1 : Summable (fun e : ℕ => ‖x‖ ^ (e + 1)) :=
    hgeo.comp_injective (fun a b h => Nat.succ_injective h)
  have hnormsum : Summable (fun e : ℕ => ‖f (p ^ (e + 1)) * x ^ (e + 1)‖) :=
    Summable.of_norm_bounded hgeo1 (fun e => by simpa using hnorm_term e)
  calc ‖∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1)‖
      ≤ ∑' e : ℕ, ‖f (p ^ (e + 1)) * x ^ (e + 1)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' e : ℕ, ‖x‖ ^ (e + 1) := Summable.tsum_le_tsum hnorm_term hnormsum hgeo1
    _ = ‖x‖ * (1 - ‖x‖)⁻¹ := by
        have hg : (∑' e : ℕ, ‖x‖ ^ (e + 1)) = ‖x‖ * (∑' e : ℕ, ‖x‖ ^ e) := by
          rw [show (fun e : ℕ => ‖x‖ ^ (e + 1)) = (fun e => ‖x‖ * ‖x‖ ^ e) from
            funext (fun e => by rw [pow_succ'])]
          exact hgeo.tsum_mul_left ‖x‖
        rw [hg, tsum_geometric_of_norm_lt_one (by
          rw [Real.norm_eq_abs, abs_of_nonneg hr]; exact lt_of_le_of_lt hx hρ)]
    _ ≤ ρ * (1 - ρ)⁻¹ := by
        refine mul_le_mul hx ?_ (inv_nonneg.mpr (by linarith)) (le_trans hr hx)
        rw [inv_le_inv₀ (by linarith) (by linarith)]; linarith
    _ = ρ / (1 - ρ) := by rw [div_eq_mul_inv]

lemma norm_locP_sub_one_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ}
    {x : ℂ} {ρ : ℝ} (hx : ‖x‖ ≤ ρ) (hρ : ρ < 1) : ‖locP f p x - 1‖ ≤ ρ / (1 - ρ) := by
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx hρ
  have hsum := locP_summable f hb (p := p) hx1
  have hsplit : locP f p x = f 1 + ∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1) := by
    rw [locP, Summable.tsum_eq_zero_add hsum]; simp
  rw [hsplit, hf1, show (1 : ℂ) + (∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1)) - 1
    = ∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1) from by ring]
  exact norm_locP_tail_le f hb hx hρ

lemma norm_locP_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} {x : ℂ} {ρ : ℝ}
    (hx : ‖x‖ ≤ ρ) (hρ : ρ < 1) : ‖locP f p x‖ ≤ 1 / (1 - ρ) := by
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx hρ
  have hsum := locP_summable f hb (p := p) hx1
  have hsplit : locP f p x = f 1 + ∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1) := by
    rw [locP, Summable.tsum_eq_zero_add hsum]; simp
  rw [hsplit]
  have h1 := norm_locP_tail_le (p := p) (x := x) f hb hx hρ
  have h2 : ‖f 1‖ ≤ 1 := hb 1
  calc ‖f 1 + ∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1)‖
      ≤ ‖f 1‖ + ‖∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1)‖ := norm_add_le _ _
    _ ≤ 1 + ρ / (1 - ρ) := add_le_add h2 h1
    _ = 1 / (1 - ρ) := by
        have hρ' : (1 - ρ) ≠ 0 := by linarith
        rw [div_eq_mul_inv]
        field_simp [hρ']
        ring

lemma re_locP_ge (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} {x : ℂ} {ρ : ℝ}
    (hx : ‖x‖ ≤ ρ) (hρ : ρ < 1 / 2) : (1 - 2 * ρ) / (1 - ρ) ≤ (locP f p x).re := by
  have hρ1 : ρ < 1 := by linarith
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx hρ1
  have hsum := locP_summable f hb (p := p) hx1
  have hsplit : locP f p x = f 1 + ∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1) := by
    rw [locP, Summable.tsum_eq_zero_add hsum]; simp
  set T := ∑' e : ℕ, f (p ^ (e + 1)) * x ^ (e + 1) with hT
  have h1 : ‖T‖ ≤ ρ / (1 - ρ) := norm_locP_tail_le f hb hx hρ1
  have h2 : -(ρ / (1 - ρ)) ≤ T.re := by
    have := neg_le_of_abs_le (le_trans (abs_re_le_norm T) h1); linarith
  rw [hsplit, hf1]
  have h3 : (1 + T).re = 1 + T.re := by simp
  rw [h3]
  have hkey : (1 - 2 * ρ) / (1 - ρ) = 1 - ρ / (1 - ρ) := by
    have hρ' : (1 - ρ) ≠ 0 := by linarith
    field_simp
    ring
  rw [hkey]
  linarith

lemma hasDerivAt_locP (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (_hp : p.Prime)
    {x : ℂ} (hx : ‖x‖ < 1 / 2) : HasDerivAt (locP f p) (locD f p x) x := by
  have hr : (3 / 4 : ℝ) < 1 := by norm_num
  have hxr : ‖x‖ < 3 / 4 := by linarith
  have hu : Summable (fun e : ℕ => (e : ℝ) * (3 / 4 : ℝ) ^ (e - 1)) := by
    have h1 : Summable (fun e : ℕ => (e : ℝ) * (3 / 4 : ℝ) ^ e) := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := (3 / 4 : ℝ)) (by norm_num)
      simpa using this
    have h2 : Summable (fun e : ℕ => (e : ℝ) * (3 / 4 : ℝ) ^ e + (3 / 4 : ℝ) ^ e) :=
      h1.add (summable_geometric_of_norm_lt_one (by norm_num : ‖(3 / 4 : ℝ)‖ < 1))
    have h3 : Summable (fun e : ℕ => ((e + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ e) := by
      refine h2.congr (fun e => ?_); push_cast; ring
    rw [← summable_nat_add_iff 1]
    refine h3.congr (fun e => ?_); simp only [Nat.add_sub_cancel]
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (F := ℂ)
    (u := fun e : ℕ => (e : ℝ) * (3 / 4 : ℝ) ^ (e - 1)) hu
    (Metric.isOpen_ball) (convex_ball (0 : ℂ) (3 / 4)).isPreconnected
    (g := fun e z => f (p ^ e) * z ^ e)
    (g' := fun e z => f (p ^ e) * ((e : ℂ) * z ^ (e - 1)))
    (fun n y _ => (hasDerivAt_pow n y).const_mul (f (p ^ n)))
    (fun n y hy => by
      have hyr : ‖y‖ < 3 / 4 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
      have hX : 0 ≤ (n : ℝ) * ‖y‖ ^ (n - 1) :=
        mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (norm_nonneg y) _)
      have h1 : ‖f (p ^ n)‖ * ((n : ℝ) * ‖y‖ ^ (n - 1)) ≤ 1 * ((n : ℝ) * ‖y‖ ^ (n - 1)) :=
        mul_le_mul_of_nonneg_right (hb _) hX
      have h3 : ‖y‖ ^ (n - 1) ≤ (3 / 4 : ℝ) ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg y) (le_of_lt hyr) _
      have h4 : (n : ℝ) * ‖y‖ ^ (n - 1) ≤ (n : ℝ) * (3 / 4 : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
      linarith)
    (y₀ := (0 : ℂ))
    (by simp [Metric.mem_ball, dist_eq_norm])
    (by
      refine summable_of_ne_finset_zero (s := {0}) (fun e he => ?_)
      have he' : e ≠ 0 := by simpa using he
      rw [zero_pow he', mul_zero])
    (by simpa [Metric.mem_ball, dist_eq_norm] using hxr)
  refine hmain.congr_deriv ?_
  rw [locD]
  exact tsum_congr (fun e => by ring)

lemma deriv_gp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (gp f p) s = -(Real.log p : ℂ) * ((p : ℂ) ^ (-s)) * locD f p ((p : ℂ) ^ (-s)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  have hxnorm : ‖((p : ℂ) ^ (-s))‖ < 1 / 2 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (1 : ℝ) < p := by linarith
    have hne : (-s).re ≠ 0 := by simp [Complex.neg_re]; linarith
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p hne, Complex.neg_re]
    have hstep1 : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
    have hstep2 : (p : ℝ) ^ (-1 : ℝ) = (p : ℝ)⁻¹ := Real.rpow_neg_one p
    have hstep3 : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr hp2
    have hstep4 : ((2 : ℝ)⁻¹) = 1 / 2 := by norm_num
    have hA : (p : ℝ) ^ (-s.re) < (2 : ℝ)⁻¹ := hstep1.trans_le (hstep2.le.trans hstep3)
    rwa [hstep4] at hA
  have hgp : gp f p = fun z : ℂ => locP f p ((p : ℂ) ^ (-z)) := by
    funext z; exact gp_eq_locP f hp0 z
  rw [hgp]
  have hinner : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
      (-(Real.log p : ℂ) * (p : ℂ) ^ (-s)) s := by
    have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) :=
      (Complex.ofReal_log (Nat.cast_nonneg p)).symm
    have hfun : (fun z : ℂ => (p : ℂ) ^ (-z))
        = fun z : ℂ => Complex.exp (((Real.log p : ℝ) : ℂ) * (-z)) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hpc, hlog]
    rw [hfun]
    have h1 : HasDerivAt (fun z : ℂ => ((Real.log p : ℝ) : ℂ) * (-z))
        (-((Real.log p : ℝ) : ℂ)) s := by
      have h2 := hasDerivAt_neg (s : ℂ)
      simpa using h2.const_mul (((Real.log p : ℝ)) : ℂ)
    have h4 : HasDerivAt (fun z : ℂ => Complex.exp (((Real.log p : ℝ) : ℂ) * (-z)))
        (Complex.exp (((Real.log p : ℝ) : ℂ) * (-s)) * (-((Real.log p : ℝ) : ℂ))) s := h1.cexp
    have h5 : Complex.exp (((Real.log p : ℝ) : ℂ) * (-s)) = (p : ℂ) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero hpc, hlog]
    rw [h5] at h4
    convert h4 using 1
    ring
  have houter : HasDerivAt (locP f p) (locD f p ((p : ℂ) ^ (-s))) ((p : ℂ) ^ (-s)) :=
    hasDerivAt_locP f hb hp hxnorm
  have hcomp := houter.comp s hinner
  have hderiv : deriv (fun z : ℂ => locP f p ((p : ℂ) ^ (-z))) s
      = locD f p ((p : ℂ) ^ (-s)) * (-(Real.log p : ℂ) * (p : ℂ) ^ (-s)) := by
    rw [show (fun z : ℂ => locP f p ((p : ℂ) ^ (-z)))
      = (locP f p) ∘ (fun z : ℂ => (p : ℂ) ^ (-z)) from rfl]
    exact hcomp.deriv
  rw [hderiv]; ring

/-- `Σ_n log n · n^{-a}` converges for `a > 1`. -/
lemma summable_log_mul_rpow_neg {a : ℝ} (ha : 1 < a) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-a)) := by
  have hε : 0 < (a - 1) / 2 := by linarith
  have hne : (a - 1) / 2 - a ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ ((a - 1) / 2 - a)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hmaj : Summable (fun n : ℕ => ((a - 1) / 2)⁻¹ * (n : ℝ) ^ ((a - 1) / 2 - a)) :=
    hsum.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast h)) (Real.rpow_nonneg (by positivity) _)
  · rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp [Real.zero_rpow hne]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast h
      have hlog : Real.log (n : ℝ) ≤ ((a - 1) / 2)⁻¹ * (n : ℝ) ^ ((a - 1) / 2) := by
        have h := Real.log_le_rpow_div (le_of_lt hnpos) hε
        rwa [div_eq_mul_inv, mul_comm] at h
      have hkey : (n : ℝ) ^ ((a - 1) / 2) * (n : ℝ) ^ (-a)
          = (n : ℝ) ^ ((a - 1) / 2 - a) := by
        rw [← Real.rpow_add hnpos]
        rfl
      calc Real.log (n : ℝ) * (n : ℝ) ^ (-a)
          ≤ (((a - 1) / 2)⁻¹ * (n : ℝ) ^ ((a - 1) / 2)) * (n : ℝ) ^ (-a) :=
            mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (le_of_lt hnpos) _)
        _ = ((a - 1) / 2)⁻¹ * (n : ℝ) ^ ((a - 1) / 2 - a) := by
              rw [mul_assoc, hkey]

/-- Continuity of `τ ↦ Kser f (a+iτ)` for `a > 1`. -/
lemma continuous_Kser_line (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {a : ℝ} (ha : 1 < a) :
    Continuous (fun τ : ℝ => Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
  have hu := summable_log_mul_rpow_neg ha
  show Continuous (fun τ : ℝ => ∑' n : ℕ,
    (f n * (Real.log n : ℂ)) * (n : ℂ) ^ (-(((a : ℂ) + (τ : ℂ) * Complex.I))))
  refine continuous_tsum (u := fun n : ℕ => Real.log n * (n : ℝ) ^ (-a)) ?_ hu ?_
  · intro n
    by_cases hn : n = 0
    · subst hn
      simpa [Real.log_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · have hnpos : (n : ℂ) ≠ 0 := by simpa using hn
      have hfun : (fun τ : ℝ => (f n * (Real.log n : ℂ))
            * (n : ℂ) ^ (-(((a : ℂ) + (τ : ℂ) * Complex.I))))
          = fun τ : ℝ => (f n * (Real.log n : ℂ))
              * Complex.exp (-(((a : ℂ) + (τ : ℂ) * Complex.I)) * Complex.log (n : ℂ)) := by
        funext τ
        have harg : Complex.log (n : ℂ) * (-(((a : ℂ) + (τ : ℂ) * Complex.I)))
            = (-(((a : ℂ) + (τ : ℂ) * Complex.I))) * Complex.log (n : ℂ) := mul_comm _ _
        rw [Complex.cpow_def_of_ne_zero hnpos, harg]
      rw [hfun]
      exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  · intro n τ
    have hre : (((a : ℂ) + (τ : ℂ) * Complex.I)).re = a := by simp
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : (1 : ℕ) ≤ n := h
      rw [norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_natCast_cpow_of_re_ne_zero n (by rw [Complex.neg_re, hre]; linarith),
        Complex.neg_re, hre]
      rcases eq_or_lt_of_le hn1 with h1 | h2
      · subst h1; simp
      · have hn2 : (1 : ℝ) < n := by exact_mod_cast h2
        have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn2
        rw [Real.norm_of_nonneg (le_of_lt hlogpos)]
        have h1' : ‖f n‖ * Real.log (n : ℝ) ≤ 1 * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right (hb n) (le_of_lt hlogpos)
        have h2' : ‖f n‖ * Real.log (n : ℝ) * (n : ℝ) ^ (-a)
            ≤ 1 * Real.log (n : ℝ) * (n : ℝ) ^ (-a) :=
          mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg (by positivity) _)
        simpa using h2'

end

end Work.BMF.mrlas.hsb
