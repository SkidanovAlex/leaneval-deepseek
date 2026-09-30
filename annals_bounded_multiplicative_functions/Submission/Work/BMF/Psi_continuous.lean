import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.hasDerivAt_LSeries_term

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of `τ ↦ ‖Ψ_f(a + iτ)‖²` for `a > 1`

`Work.BMF.Psi f s = Σ_p g_p'(s)/g_p(s)` is the log-derivative of the (formal) Euler product
of `f`, `g_p(s) = Σ_{e≥0} f(p^e) p^{-es}`.  For `Re s = a > 1` both `g_p` and its derivative
are bounded by geometric majorants that are summable over the primes, so `Ψ_f` is a locally
uniform limit of continuous functions on the line `Re s = a`.
-/

namespace Work.BMF

open Complex

/-! ## Geometric majorants -/

private lemma geom_aux {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun e : ℕ => r ^ e) ∧ (∑' e : ℕ, r ^ e) = 1 / (1 - r) ∧
    Summable (fun e : ℕ => (e : ℝ) * r ^ e) ∧
    (∑' e : ℕ, (e : ℝ) * r ^ e) = r / (1 - r) ^ 2 := by
  have hn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  exact ⟨summable_geometric_of_norm_lt_one hn,
    by rw [tsum_geometric_of_norm_lt_one hn, one_div],
    (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable,
    tsum_coe_mul_geometric_of_norm_lt_one hn⟩

private lemma rpow_neg_lt_one {k : ℕ} (hk : 1 < k) {σ : ℝ} (hσ : 0 < σ) :
    (k : ℝ) ^ (-σ) < 1 := by
  rw [Real.rpow_lt_one_iff_of_pos (by positivity : (0 : ℝ) < k)]
  exact Or.inl ⟨by exact_mod_cast hk, by linarith⟩

private lemma rpow_neg_pow_eq {k : ℕ} (hk : 1 ≤ k) (σ : ℝ) (e : ℕ) :
    ((k : ℝ) ^ e) ^ (-σ) = ((k : ℝ) ^ (-σ)) ^ e := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  rw [← Real.rpow_natCast (k : ℝ) e, ← Real.rpow_natCast ((k : ℝ) ^ (-σ)) e,
      ← Real.rpow_mul hk0 (e : ℝ) (-σ), ← Real.rpow_mul hk0 (-σ) (e : ℝ)]
  congr 1
  ring

private lemma rpow_neg_pow_le {k : ℕ} (hk : 2 ≤ k) {σ r : ℝ} (h : σ ≤ r) (e : ℕ) :
    ((k : ℝ) ^ e) ^ (-r) ≤ ((k : ℝ) ^ (-σ)) ^ e := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hstep : (k : ℝ) ^ (-r) ≤ (k : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  calc ((k : ℝ) ^ e) ^ (-r) = ((k : ℝ) ^ (-r)) ^ e :=
        rpow_neg_pow_eq (by omega : 1 ≤ k) r e
    _ ≤ ((k : ℝ) ^ (-σ)) ^ e :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) _) hstep e

/-! ## Norm bounds for the terms and their derivatives -/

private lemma norm_term_bound (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} (_hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) (e : ℕ) :
    ‖LSeries.term f s (k ^ e)‖ ≤ ((k : ℝ) ^ (-σ)) ^ e := by
  have hk0 : k ≠ 0 := by omega
  have hke : k ^ e ≠ 0 := pow_ne_zero e hk0
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hbase : (1 : ℝ) ≤ (↑(k ^ e) : ℝ) := by
    rw [Nat.cast_pow]; exact one_le_pow₀ hk1
  have hposb : (0 : ℝ) < (↑(k ^ e) : ℝ) := lt_of_lt_of_le one_pos hbase
  rw [LSeries.norm_term_eq, ite_eq_right hke]
  have h1 : ‖f (k ^ e)‖ / (↑(k ^ e) : ℝ) ^ s.re ≤ 1 / (↑(k ^ e) : ℝ) ^ s.re := by
    gcongr
    exact hb _
  refine h1.trans ?_
  have h2 : 1 / (↑(k ^ e) : ℝ) ^ s.re ≤ 1 / (↑(k ^ e) : ℝ) ^ σ := by
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hposb σ)
    exact Real.rpow_le_rpow_of_exponent_le hbase hs
  refine h2.trans (le_of_eq ?_)
  rw [one_div, ← Real.rpow_neg hposb.le, Nat.cast_pow,
    rpow_neg_pow_eq (by omega : 1 ≤ k) σ e]

private lemma norm_deriv_term_bound (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} (_hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) (e : ℕ) :
    ‖f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) * (((k ^ e : ℕ)) : ℂ) ^ (-s)‖
      ≤ Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hlog0 : 0 ≤ Real.log ((k : ℝ) ^ e) :=
    Real.log_nonneg (one_le_pow₀ hk1)
  have hnorm : ‖(((k ^ e : ℕ)) : ℂ) ^ (-s)‖ = ((k : ℝ) ^ e) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (pow_pos (by omega : 0 < k) e), Complex.neg_re,
      Nat.cast_pow]
  have hnlog : ‖((Real.log ((k : ℝ) ^ e)) : ℂ)‖ = Real.log ((k : ℝ) ^ e) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg hlog0
  have hgoal : ‖f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) * (((k ^ e : ℕ)) : ℂ) ^ (-s)‖
      = ‖f (k ^ e)‖ * Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ e) ^ (-s.re) := by
    rw [norm_mul, norm_mul, norm_neg, hnlog, hnorm]
  rw [hgoal]
  have hle : ((k : ℝ) ^ e) ^ (-s.re) ≤ ((k : ℝ) ^ (-σ)) ^ e := rpow_neg_pow_le hk hs e
  calc ‖f (k ^ e)‖ * Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ e) ^ (-s.re)
      ≤ 1 * Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e := by
        gcongr
        exact hb _
    _ = Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e := by rw [one_mul]

/-! ## Closed forms for the log-weighted majorant -/

private lemma summable_log_pow_mul {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun e : ℕ => Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e) := by
  have hq1 : (k : ℝ) ^ (-σ) < 1 := rpow_neg_lt_one (by omega : 1 < k) hσ
  have hsum1 : Summable (fun e : ℕ => (e : ℝ) * ((k : ℝ) ^ (-σ)) ^ e) :=
    (geom_aux (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) _) hq1).2.2.1
  refine (hsum1.mul_left (Real.log k)).congr (fun e => ?_)
  rw [Real.log_pow]; ring

private lemma tsum_log_pow_mul {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} (hσ : 0 < σ) :
    (∑' e : ℕ, Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e)
      = Real.log k * (((k : ℝ) ^ (-σ)) / (1 - (k : ℝ) ^ (-σ)) ^ 2) := by
  have hq1 : (k : ℝ) ^ (-σ) < 1 := rpow_neg_lt_one (by omega : 1 < k) hσ
  have hg := geom_aux (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) _) hq1
  have hsum1 : Summable (fun e : ℕ => (e : ℝ) * ((k : ℝ) ^ (-σ)) ^ e) := hg.2.2.1
  rw [show (fun e : ℕ => Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e)
        = fun e : ℕ => Real.log k * ((e : ℝ) * ((k : ℝ) ^ (-σ)) ^ e) by
      funext e; rw [Real.log_pow]; ring]
  rw [tsum_mul_left, hg.2.2.2]

/-! ## Summability of the prime majorant -/

private lemma summable_log_rpow_primes {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-σ))) := by
  have hε : 0 < (σ - 1) / 2 := by linarith
  have hlt : (σ - 1) / 2 - σ < -1 := by linarith
  have hmain : Summable (fun n : ℕ => ((n : ℝ) ^ ((σ - 1) / 2 - σ))) :=
    (Real.summable_nat_rpow).mpr hlt
  have hbnd : ∀ n : ℕ,
      Real.log n * (n : ℝ) ^ (-σ) ≤ ((n : ℝ) ^ ((σ - 1) / 2 - σ)) / ((σ - 1) / 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, Real.log_zero, zero_mul]
      exact div_nonneg (Real.rpow_nonneg le_rfl _) (by linarith)
    · have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2) :=
        Real.log_le_rpow_div (by positivity) hε
      have hpos : (0 : ℝ) < n := by positivity
      have h2 : ((n : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2)) * (n : ℝ) ^ (-σ)
          = (n : ℝ) ^ ((σ - 1) / 2 - σ) / ((σ - 1) / 2) := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hpos,
          show (σ - 1) / 2 + -σ = (σ - 1) / 2 - σ by ring]
      calc Real.log (n : ℝ) * (n : ℝ) ^ (-σ)
          ≤ ((n : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2)) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hpos.le _)
        _ = (n : ℝ) ^ ((σ - 1) / 2 - σ) / ((σ - 1) / 2) := h2
  have hsm : Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hbnd (hmain.div_const _)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (Real.log_nonneg this) (Real.rpow_nonneg (by positivity) _)
  exact hsm.subtype Nat.Prime

/-! ## Continuity of the individual terms along a vertical line -/

private lemma continuous_cpow_neg_line (n : ℕ) (hn : n ≠ 0) (a : ℝ) :
    Continuous (fun τ : ℝ => (n : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I))) := by
  have heq : ∀ τ : ℝ,
      (n : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I))
        = Complex.exp (-(Real.log n : ℂ) * ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
    intro τ
    have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def, ite_eq_right hne, ← Complex.natCast_log]
    congr 1
    ring
  rw [funext heq]
  refine Complex.continuous_exp.comp ?_
  exact Continuous.mul continuous_const
    (Continuous.add continuous_const
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const))

private lemma continuous_LSeries_term_line (f : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) (a : ℝ) :
    Continuous (fun τ : ℝ => LSeries.term f ((a : ℂ) + (τ : ℂ) * Complex.I) n) := by
  have heq : (fun τ : ℝ => LSeries.term f ((a : ℂ) + (τ : ℂ) * Complex.I) n)
      = fun τ : ℝ => f n * (n : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I)) := by
    funext τ
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, Complex.cpow_neg]
  rw [heq]
  exact continuous_const.mul (continuous_cpow_neg_line n hn a)

/-! ## The local factor: nonvanishing and derivative -/

private lemma norm_gp_lower (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    1 - ((k : ℝ) ^ (-σ)) / (1 - (k : ℝ) ^ (-σ)) ≤ ‖gp f k s‖ := by
  have hk0 : k ≠ 0 := by omega
  have hq0 : 0 ≤ (k : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have hq1 : (k : ℝ) ^ (-σ) < 1 := rpow_neg_lt_one (by omega : 1 < k) hσ
  have hgeo : Summable (fun e : ℕ => ((k : ℝ) ^ (-σ)) ^ e) := (geom_aux hq0 hq1).1
  have hsum : Summable (fun e : ℕ => LSeries.term f s (k ^ e)) :=
    Summable.of_norm_bounded hgeo (fun e => norm_term_bound f hb hk hσ hs e)
  have hsplit : gp f k s = 1 + ∑' e : ℕ, LSeries.term f s (k ^ (e + 1)) := by
    have h := hsum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    have hg0 : LSeries.term f s (k ^ 0) = 1 := by
      have h1 : LSeries.term f s (k ^ 0) = f 1 / (1 : ℂ) ^ s := by
        rw [pow_zero, LSeries.term_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0) f s, Nat.cast_one]
      rw [h1, Complex.one_cpow, div_one, hf1]
    rw [hg0] at h
    simp only [gp]
    rw [h]
  have hgeo1 : Summable (fun e : ℕ => ((k : ℝ) ^ (-σ)) ^ (e + 1)) := by
    rw [summable_nat_add_iff 1]; exact hgeo
  have hb2 : ‖∑' e : ℕ, LSeries.term f s (k ^ (e + 1))‖
      ≤ ((k : ℝ) ^ (-σ)) / (1 - (k : ℝ) ^ (-σ)) := by
    have hsub : Summable (fun e : ℕ => ‖LSeries.term f s (k ^ (e + 1))‖) := by
      refine Summable.of_nonneg_of_le (fun e => norm_nonneg _)
        (fun e => norm_term_bound f hb hk hσ hs (e + 1)) hgeo1
    calc ‖∑' e : ℕ, LSeries.term f s (k ^ (e + 1))‖
        ≤ ∑' e : ℕ, ‖LSeries.term f s (k ^ (e + 1))‖ := norm_tsum_le_tsum_norm hsub
      _ ≤ ∑' e : ℕ, ((k : ℝ) ^ (-σ)) ^ (e + 1) :=
          Summable.tsum_le_tsum (fun e => norm_term_bound f hb hk hσ hs (e + 1)) hsub hgeo1
      _ = ((k : ℝ) ^ (-σ)) / (1 - (k : ℝ) ^ (-σ)) := by
          rw [show (fun e : ℕ => ((k : ℝ) ^ (-σ)) ^ (e + 1))
                = fun e : ℕ => ((k : ℝ) ^ (-σ)) * ((k : ℝ) ^ (-σ)) ^ e by
              funext e; rw [pow_succ]; ring]
          rw [tsum_mul_left, (geom_aux hq0 hq1).2.1]
          ring
  have hkey : 1 - ‖∑' e : ℕ, LSeries.term f s (k ^ (e + 1))‖ ≤ ‖gp f k s‖ := by
    have h1 : (1 : ℂ) - (1 + ∑' e : ℕ, LSeries.term f s (k ^ (e + 1)))
        = -(∑' e : ℕ, LSeries.term f s (k ^ (e + 1))) := by ring
    have h := norm_sub_norm_le (1 : ℂ) (1 + ∑' e : ℕ, LSeries.term f s (k ^ (e + 1)))
    rw [norm_one, h1, norm_neg, ← hsplit] at h
    linarith
  linarith

private lemma gp_hasDerivAt (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {k : ℕ} (hk : 2 ≤ k)
    {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    HasDerivAt (gp f k)
      (∑' e : ℕ, f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) * (((k ^ e : ℕ)) : ℂ) ^ (-s)) s := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  set σ' : ℝ := σ / 2 with hσ'def
  have hσ'0 : 0 < σ' := by rw [hσ'def]; linarith
  have hσ'lt : σ' < σ := by rw [hσ'def]; linarith
  have hσ'le : σ' ≤ s.re := le_trans hσ'lt.le hs
  have hmaj : Summable (fun e : ℕ => Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ')) ^ e) :=
    summable_log_pow_mul hk hσ'0
  have hconv : Convex ℝ {z : ℂ | σ' < z.re} := by
    intro x hx y hy p q hp hq hpq
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · have hq1 : q = 1 := by linarith
      rw [show p * x.re + q * y.re = y.re by rw [← hp0, hq1]; ring]
      exact hy
    · rcases eq_or_lt_of_le hq with hq0 | hq0
      · have hp1 : p = 1 := by linarith
        rw [show p * x.re + q * y.re = x.re by rw [← hq0, hp1]; ring]
        exact hx
      · have h1 : p * σ' + q * σ' < p * x.re + q * y.re := by
          nlinarith [mul_lt_mul_of_pos_left hx hp0, mul_lt_mul_of_pos_left hy hq0]
        have h2 : p * σ' + q * σ' = σ' := by nlinarith
        linarith
  have hmain := hasDerivAt_tsum_of_isPreconnected (α := ℕ) (𝕜 := ℂ) (F := ℂ)
    (u := fun e : ℕ => Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ')) ^ e)
    (g := fun e z => LSeries.term f z (k ^ e))
    (g' := fun e z => f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) * (((k ^ e : ℕ)) : ℂ) ^ (-z))
    (t := {z : ℂ | σ' < z.re}) (y₀ := (σ : ℂ)) hmaj
    (isOpen_lt continuous_const Complex.continuous_re) hconv.isPreconnected
    (fun e z _ => by
      simpa only [Nat.cast_pow] using hasDerivAt_LSeries_term f (pow_ne_zero e hk0) z)
    (fun e z hz => norm_deriv_term_bound f hb hk hσ'0 hz.le e)
    (show σ' < (σ : ℂ).re from by simpa using hσ'lt)
    (by
      refine Summable.of_norm_bounded (geom_aux
        (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ k) _)
        (rpow_neg_lt_one (by omega : 1 < k) hσ'0)).1 (fun e => ?_)
      simpa using norm_term_bound f hb hk hσ'0 (s := (σ:ℂ)) (by simpa using hσ'lt.le) e)
    (show σ' < s.re from lt_of_lt_of_le hσ'lt hs)
  exact hmain

/-! ## The main theorem -/

theorem Psi_continuous (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    (a : ℝ) (ha : 1 < a) :
    Continuous fun τ : ℝ => ‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
  set σ : ℝ := (1 + a) / 2 with hσdef
  have hσ0 : 0 < σ := by rw [hσdef]; linarith
  have hσa : σ < a := by rw [hσdef]; linarith
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hline : ∀ τ : ℝ, ((a : ℂ) + (τ : ℂ) * Complex.I).re = a := by
    intro τ
    simp [Complex.add_re, Complex.mul_re]
  have hlineσ : ∀ τ : ℝ, σ ≤ ((a : ℂ) + (τ : ℂ) * Complex.I).re := by
    intro τ; rw [hline]; exact hσa.le
  have hQhalf : (2 : ℝ) ^ (-σ) < 1 / 2 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num)
      (show -σ < -1 by linarith)
    rw [Real.rpow_neg_one] at h
    have h21 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith [h, h21]
  have hQpos : 0 < (2 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by norm_num) _
  have hQle : ∀ k : ℕ, 2 ≤ k → (k : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    intro k hk
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hk) (by linarith)
  set K : ℝ := 1 / ((1 - (2 : ℝ) ^ (-σ)) * (1 - 2 * (2 : ℝ) ^ (-σ))) with hKdef
  have hsum_maj : Summable (fun P : Nat.Primes =>
      K * (Real.log ((P : ℕ) : ℝ) * (((P : ℕ) : ℝ) ^ (-σ)))) :=
    (summable_log_rpow_primes hσ1).mul_left K
  have hcont : Continuous (fun τ : ℝ => ∑' P : Nat.Primes,
      deriv (gp f (P : ℕ)) ((a : ℂ) + (τ : ℂ) * Complex.I) /
        gp f (P : ℕ) ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
    refine continuous_tsum (u := fun P : Nat.Primes =>
        K * (Real.log ((P : ℕ) : ℝ) * (((P : ℕ) : ℝ) ^ (-σ)))) ?_ hsum_maj ?_
    · intro P
      set k : ℕ := (P : ℕ) with hkdef
      have hk2 : 2 ≤ k := by rw [hkdef]; exact P.prop.two_le
      have hk0 : k ≠ 0 := by omega
      have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
      have hq1 : (k : ℝ) ^ (-σ) < 1 := rpow_neg_lt_one (by omega : 1 < k) hσ0
      have hq0 : 0 ≤ (k : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have hGc : Continuous (fun τ : ℝ => gp f k ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
        change Continuous (fun τ : ℝ => ∑' e : ℕ,
          LSeries.term f ((a : ℂ) + (τ : ℂ) * Complex.I) (k ^ e))
        exact continuous_tsum
          (fun e => continuous_LSeries_term_line f (k ^ e) (pow_ne_zero e hk0) a)
          (geom_aux hq0 hq1).1
          (fun e τ => norm_term_bound f hb hk2 hσ0 (hlineσ τ) e)
      have hDc : Continuous (fun τ : ℝ => deriv (gp f k) ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
        have hform : ∀ τ : ℝ, deriv (gp f k) ((a : ℂ) + (τ : ℂ) * Complex.I)
            = ∑' e : ℕ, f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) *
                (((k ^ e : ℕ)) : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I)) := by
          intro τ
          exact (gp_hasDerivAt f hb hk2 hσ0 (hlineσ τ)).deriv
        rw [funext hform]
        exact continuous_tsum
          (fun e => (continuous_const : Continuous fun _ : ℝ =>
              f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ))).mul
            (continuous_cpow_neg_line (k ^ e) (pow_ne_zero e hk0) a))
          (summable_log_pow_mul hk2 hσ0)
          (fun e τ => norm_deriv_term_bound f hb hk2 hσ0 (hlineσ τ) e)
      have hne : ∀ τ : ℝ, gp f k ((a : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
        intro τ hzero
        have hlow := norm_gp_lower f hf1 hb hk2 hσ0 (hlineσ τ)
        rw [hzero, norm_zero] at hlow
        have hQl : (k : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by rw [hkdef]; exact hQle k hk2
        have hlt : (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) < 1 := by
          rw [div_lt_one (by linarith)]
          nlinarith [hQl, hQhalf]
        linarith
      exact hDc.div hGc hne
    · intro P τ
      set k : ℕ := (P : ℕ) with hkdef
      have hk2 : 2 ≤ k := by rw [hkdef]; exact P.prop.two_le
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hq1 : (k : ℝ) ^ (-σ) < 1 := rpow_neg_lt_one (by omega : 1 < k) hσ0
      have hq0 : 0 ≤ (k : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have hQl : (k : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by rw [hkdef]; exact hQle k hk2
      -- numerator bound
      have hnum : ‖deriv (gp f k) ((a : ℂ) + (τ : ℂ) * Complex.I)‖
          ≤ Real.log k * ((k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) ^ 2) := by
        rw [(gp_hasDerivAt f hb hk2 hσ0 (hlineσ τ)).deriv]
        have hnn : Summable (fun e : ℕ => ‖f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) *
              (((k ^ e : ℕ)) : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I))‖) :=
          Summable.of_norm_bounded (summable_log_pow_mul hk2 hσ0)
            (fun e => by
              simpa using norm_deriv_term_bound f hb hk2 hσ0 (hlineσ τ) e)
        calc ‖∑' e : ℕ, f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) *
                (((k ^ e : ℕ)) : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I))‖
            ≤ ∑' e : ℕ, ‖f (k ^ e) * (-(Real.log ((k : ℝ) ^ e) : ℂ)) *
                (((k ^ e : ℕ)) : ℂ) ^ (-((a : ℂ) + (τ : ℂ) * Complex.I))‖ :=
              norm_tsum_le_tsum_norm hnn
          _ ≤ ∑' e : ℕ, Real.log ((k : ℝ) ^ e) * ((k : ℝ) ^ (-σ)) ^ e :=
              Summable.tsum_le_tsum (fun e => norm_deriv_term_bound f hb hk2 hσ0 (hlineσ τ) e)
                hnn (summable_log_pow_mul hk2 hσ0)
          _ = Real.log k * ((k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) ^ 2) :=
              tsum_log_pow_mul hk2 hσ0
      have hden : 1 - (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ))
          ≤ ‖gp f k ((a : ℂ) + (τ : ℂ) * Complex.I)‖ :=
        norm_gp_lower f hf1 hb hk2 hσ0 (hlineσ τ)
      have hden_pos : 0 < 1 - (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) := by
        have h1 : (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) < 1 := by
          rw [div_lt_one (by linarith)]; linarith
        linarith
      have hnum_nn : 0 ≤ Real.log k * ((k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) ^ 2) :=
        mul_nonneg (Real.log_nonneg hk1)
          (div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
      have hstep1 : ‖deriv (gp f k) ((a : ℂ) + (τ : ℂ) * Complex.I) /
            gp f k ((a : ℂ) + (τ : ℂ) * Complex.I)‖
          ≤ (Real.log k * ((k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) ^ 2)) /
              (1 - (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ))) := by
        rw [norm_div]
        exact div_le_div₀ hnum_nn hnum hden_pos hden
      have hstep2 : (Real.log k * ((k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) ^ 2)) /
              (1 - (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)))
          ≤ Real.log k * ((k : ℝ) ^ (-σ) /
              ((1 - (2 : ℝ) ^ (-σ)) * (1 - 2 * (2 : ℝ) ^ (-σ)))) := by
        have h2Q : 2 * (2 : ℝ) ^ (-σ) < 1 := by linarith
        have h1q : 0 < 1 - (k : ℝ) ^ (-σ) := by linarith
        have h12q : 0 < 1 - 2 * (k : ℝ) ^ (-σ) := by linarith
        have h1Q : 0 < 1 - (2 : ℝ) ^ (-σ) := by linarith
        have h12Q : 0 < 1 - 2 * (2 : ℝ) ^ (-σ) := by linarith
        have hmono : (1 - (2 : ℝ) ^ (-σ)) * (1 - 2 * (2 : ℝ) ^ (-σ))
            ≤ (1 - (k : ℝ) ^ (-σ)) * (1 - 2 * (k : ℝ) ^ (-σ)) :=
          mul_le_mul (by linarith) (by linarith) h12Q.le h1q.le
        have hrew : (Real.log k * ((k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)) ^ 2)) /
              (1 - (k : ℝ) ^ (-σ) / (1 - (k : ℝ) ^ (-σ)))
            = Real.log k * ((k : ℝ) ^ (-σ) /
                ((1 - (k : ℝ) ^ (-σ)) * (1 - 2 * (k : ℝ) ^ (-σ)))) := by
          field_simp
          ring
        rw [hrew]
        apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg hk1)
        exact div_le_div₀ hq0 le_rfl (mul_pos h1Q h12Q) hmono
      have hstep3 : Real.log k * ((k : ℝ) ^ (-σ) /
              ((1 - (2 : ℝ) ^ (-σ)) * (1 - 2 * (2 : ℝ) ^ (-σ))))
          = K * (Real.log ((P : ℕ) : ℝ) * (((P : ℕ) : ℝ) ^ (-σ))) := by
        rw [hKdef, hkdef]; ring
      linarith [hstep1, hstep2, hstep3]
  refine (hcont.norm.pow 2).congr (fun τ => ?_)
  simp only [Pi.pow_apply, Psi]

end Work.BMF
