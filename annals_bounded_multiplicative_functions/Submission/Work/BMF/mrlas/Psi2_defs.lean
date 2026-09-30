import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Kser_gp_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local Euler factors as power series in `u = p^{-s}`

Foundational lemmas for `Work.BMF.mrlas.Psi2_L2_bound`.  We rewrite the local Euler factor
`gp f p s = Σ_e f(p^e) p^{-es}` as the power series `Σ_e f(p^e) (u p s)^e` in `u p s = p^{-s}`,
and record the resulting upper/lower bounds.
-/

namespace Work.BMF.mrlas

open Finset Real Complex MeasureTheory
open scoped BigOperators

noncomputable section

/-- `u p s = exp (-(log p) s)`: the local variable `p^{-s}` of the Euler factor at the prime `p`. -/
noncomputable def u (p : ℕ) (s : ℂ) : ℂ := Complex.exp (-(Real.log p : ℂ) * s)

lemma u_eq_cpow {p : ℕ} (hp : p ≠ 0) (s : ℂ) : u p s = (p : ℂ) ^ (-s) := by
  rw [u, Complex.cpow_def_of_ne_zero (by exact_mod_cast hp), Complex.natCast_log]
  ring_nf

lemma norm_u {p : ℕ} (hp : 0 < p) (s : ℂ) : ‖u p s‖ = (p : ℝ) ^ (-s.re) := by
  rw [u, Complex.norm_exp, Real.rpow_def_of_pos (by exact_mod_cast hp)]
  congr 1
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  simp

/-- `LSeries.term f s (p^e) = f (p^e) * (u p s)^e`. -/
lemma term_primePow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) (e : ℕ) :
    LSeries.term f s (p ^ e) = f (p ^ e) * (u p s) ^ e := by
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hpe]
  have hA : (↑(p^e) : ℂ)^s = Complex.exp ((e:ℂ) * (Real.log p : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpe), ← Complex.natCast_log (n := p^e)]
    rw [show ((p^e : ℕ) : ℝ) = (p:ℝ)^e by push_cast; ring, Real.log_pow]
    congr 1
    push_cast
    ring
  have hB : (u p s)^e = Complex.exp (-((e:ℂ) * (Real.log p : ℂ) * s)) := by
    rw [u, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hA, hB, div_eq_mul_inv, ← Complex.exp_neg]

/-- The Euler factor as a power series in `u p s`. -/
lemma gp_eq (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    gp f p s = ∑' e : ℕ, f (p ^ e) * (u p s) ^ e :=
  tsum_congr (fun e => term_primePow f hp s e)

lemma norm_u_lt_one {p : ℕ} (hp : p.Prime) {s : ℂ} (hσ : 0 < s.re) : ‖u p s‖ < 1 := by
  rw [norm_u hp.pos]
  have := Real.rpow_lt_rpow_of_exponent_lt (x := (p:ℝ)) (by exact_mod_cast hp.one_lt)
    (show -s.re < (0:ℝ) by linarith)
  rwa [Real.rpow_zero] at this

lemma summable_geom_u {p : ℕ} (hp : p.Prime) {s : ℂ} (hσ : 0 < s.re) :
    Summable (fun e : ℕ => (‖u p s‖ : ℝ) ^ e) :=
  summable_geometric_of_norm_lt_one (R := ℝ)
    (by rw [Real.norm_of_nonneg (norm_nonneg (u p s))]; exact norm_u_lt_one hp hσ)

/-- Summability of the terms of the Euler-factor power series at `p`. -/
lemma summable_gp_terms (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hσ : 0 < s.re) :
    Summable (fun e : ℕ => f (p ^ e) * (u p s) ^ e) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => ?_)
    (summable_geom_u hp hσ)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hb _)

/-- Upper bound: `‖gp f p s‖ ≤ (1 - ‖u p s‖)⁻¹`. -/
lemma norm_gp_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hσ : 0 < s.re) :
    ‖gp f p s‖ ≤ (1 - ‖u p s‖)⁻¹ := by
  have hsum := summable_gp_terms f hb hp hσ
  rw [gp_eq f hp]
  calc ‖∑' e : ℕ, f (p ^ e) * (u p s) ^ e‖
      ≤ ∑' e : ℕ, ‖f (p ^ e) * (u p s) ^ e‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' e : ℕ, (‖u p s‖ : ℝ) ^ e :=
        Summable.tsum_le_tsum (fun e => by
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hb _))
          hsum.norm (summable_geom_u hp hσ)
    _ = (1 - ‖u p s‖)⁻¹ := tsum_geometric_of_norm_lt_one
          (by rw [Real.norm_of_nonneg (norm_nonneg (u p s))]; exact norm_u_lt_one hp hσ)

/-- Lower bound: `‖u p s‖ / (1 - ‖u p s‖)` controls `‖gp f p s - 1‖`. -/
lemma norm_gp_sub_one_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hσ : 0 < s.re) :
    ‖gp f p s - 1‖ ≤ ‖u p s‖ / (1 - ‖u p s‖) := by
  have hsum := summable_gp_terms f hb hp hσ
  rw [gp_eq f hp, Summable.tsum_eq_zero_add hsum]
  simp only [pow_zero, mul_one, hf1, add_sub_cancel_left]
  have htailC : Summable (fun e : ℕ => f (p ^ (e+1)) * (u p s) ^ (e+1)) :=
    hsum.comp_injective Nat.succ_injective
  have hgeomS : Summable (fun e : ℕ => (‖u p s‖ : ℝ) ^ (e+1)) :=
    (summable_geom_u hp hσ).comp_injective Nat.succ_injective
  calc ‖∑' e : ℕ, f (p ^ (e + 1)) * (u p s) ^ (e + 1)‖
      ≤ ∑' e : ℕ, ‖f (p ^ (e + 1)) * (u p s) ^ (e + 1)‖ := norm_tsum_le_tsum_norm htailC.norm
    _ ≤ ∑' e : ℕ, (‖u p s‖ : ℝ) ^ (e+1) :=
        Summable.tsum_le_tsum (fun e => by
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hb _)) htailC.norm hgeomS
    _ = ‖u p s‖ * (1 - ‖u p s‖)⁻¹ := by
        rw [tsum_congr (fun e => by rw [pow_succ']), tsum_mul_left,
          tsum_geometric_of_norm_lt_one (by
            rw [Real.norm_of_nonneg (norm_nonneg (u p s))]; exact norm_u_lt_one hp hσ)]
    _ = ‖u p s‖ / (1 - ‖u p s‖) := by rw [div_eq_mul_inv]

/-- Lower bound on `‖gp‖` in the useful form. -/
lemma gp_lower_bound (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hσ : 0 < s.re) :
    (1 - 2 * ‖u p s‖) / (1 - ‖u p s‖) ≤ ‖gp f p s‖ := by
  have h1 := norm_gp_sub_one_le f hf1 hb hp hσ
  have h2 : (1:ℝ) - ‖gp f p s - 1‖ ≤ ‖gp f p s‖ := by
    have := abs_norm_sub_norm_le (gp f p s) (1:ℂ)
    rw [norm_one, abs_le] at this
    linarith [this.1]
  have h4 : 1 - ‖u p s‖ / (1 - ‖u p s‖) = (1 - 2 * ‖u p s‖) / (1 - ‖u p s‖) := by
    have hne : (1 - ‖u p s‖) ≠ 0 := by
      have := norm_u_lt_one hp hσ; linarith
    field_simp
    ring
  linarith [h1, h2, le_of_eq h4]

/-- `log (p^e) = e log p`. -/
lemma log_prime_pow (p : ℕ) (e : ℕ) :
    Complex.log (↑(p^e) : ℂ) = (e : ℂ) * (Real.log p : ℂ) := by
  rw [← Complex.natCast_log (n := p^e)]
  rw [show ((p^e : ℕ) : ℝ) = (p:ℝ)^e by push_cast; ring, Real.log_pow]
  push_cast
  ring

/-- The derivative of the local Euler factor, as a power series in `u p z`. -/
lemma deriv_gp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime) {z : ℂ}
    (hz : 1 < z.re) :
    deriv (gp f p) z = -(Real.log p : ℂ) * ∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p z) ^ e := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  have hpinv : ((p:ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp1
  have hsum : Summable (fun e : ℕ => ((p:ℝ)⁻¹) ^ e) :=
    summable_geometric_of_norm_lt_one (R := ℝ)
      (by rw [Real.norm_of_nonneg (inv_nonneg.mpr hp0.le)]; exact hpinv)
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
  have hF : ∀ e : ℕ, DifferentiableOn ℂ (fun w : ℂ => LSeries.term f w (p ^ e)) {w : ℂ | 1 < w.re} :=
    fun e w _ => (LSeries.hasDerivAt_term f (p^e) w).differentiableAt.differentiableWithinAt
  have hbound : ∀ e : ℕ, ∀ w ∈ {w : ℂ | 1 < w.re},
      ‖LSeries.term f w (p ^ e)‖ ≤ ((p:ℝ)⁻¹) ^ e := by
    intro e w hw
    have hw1 : 1 < w.re := hw
    rw [term_primePow f hp w e, norm_mul, norm_pow]
    have hnorm : ‖u p w‖ ≤ (p:ℝ)⁻¹ := by
      rw [norm_u hp.pos, ← Real.rpow_neg_one p]
      exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith [hw1])
    calc ‖f (p^e)‖ * ‖u p w‖^e ≤ 1 * ‖u p w‖^e :=
          mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (norm_nonneg _) e)
      _ ≤ 1 * ((p:ℝ)⁻¹)^e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm e) (by norm_num)
      _ = ((p:ℝ)⁻¹)^e := one_mul _
  have hH := Complex.hasSum_deriv_of_summable_norm (F := fun (e:ℕ) (w:ℂ) => LSeries.term f w (p ^ e))
    hsum hF hU hbound hz
  have hd : ∀ e : ℕ, deriv (fun w : ℂ => LSeries.term f w (p ^ e)) z
      = -(LSeries.term (LSeries.logMul f) z (p ^ e)) :=
    fun e => (LSeries.hasDerivAt_term f (p^e) z).deriv
  have hterm : ∀ e : ℕ, LSeries.term (LSeries.logMul f) z (p ^ e)
      = (Real.log p : ℂ) * ((e : ℂ) * f (p ^ e) * (u p z) ^ e) := by
    intro e
    rw [term_primePow (LSeries.logMul f) hp z e, LSeries.logMul, log_prime_pow p e]
    ring
  have key : deriv (fun w : ℂ => ∑' e : ℕ, LSeries.term f w (p^e)) z = deriv (gp f p) z := rfl
  rw [← key, ← hH.tsum_eq, tsum_congr (fun e => hd e), tsum_neg,
      tsum_congr (fun e => hterm e), tsum_mul_left]
  ring

end

end Work.BMF.mrlas
