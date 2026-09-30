import Mathlib
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.mrlas.summable_prime_log_mul_rpow_neg
import Submission.Work.BMF.mrlas.gp_lower_bound_line
import Submission.Work.BMF.mrlas.norm_tsum_e_mul_u_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex
open scoped BigOperators

noncomputable section

/-- `K = Σ_{e ≥ 1} e (1/2)^{e-1}`: the constant dominating the local derivative series
`Σ_e e · f(p^e) · (p^{-s})^e` uniformly in the prime `p`, for `Re s > 1`. -/
private noncomputable def psiK : ℝ := ∑' e : ℕ, (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1)

private lemma summable_psiK : Summable (fun e : ℕ => (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1)) := by
  have heq : (fun e : ℕ => (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1))
      = fun e : ℕ => 2 * ((e : ℝ) * (1 / 2 : ℝ) ^ e) := by
    funext e
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
      rw [Nat.succ_sub_one, pow_succ]
      push_cast
      ring
  have h : Summable (fun e : ℕ => (e : ℝ) * (1 / 2 : ℝ) ^ e) := by
    have hh := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / 2 : ℝ))
      (by norm_num)
    simpa [pow_one] using hh
  rw [heq]
  exact h.mul_left 2

private lemma psiK_nonneg : 0 ≤ psiK := by
  rw [psiK]
  exact tsum_nonneg (fun e => mul_nonneg (Nat.cast_nonneg e) (pow_nonneg (by norm_num) _))

/-- The log-derivative of the local Euler factor at a prime is dominated by
`K · (log p) · p^{-Re s}`, uniformly in `p`. -/
private lemma norm_deriv_div_gp_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s‖
      ≤ (psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re))) / (1 - 2 * (2 : ℝ) ^ (-s.re)) := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hD := norm_tsum_e_mul_u_pow_le f hb hp hs
  have hnum : ‖deriv (Work.BMF.gp f p) s‖
      ≤ psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re)) := by
    rw [deriv_gp f hb hp hs, norm_mul, norm_neg]
    have h1 : ‖((Real.log (p : ℝ)) : ℂ)‖ = Real.log (p : ℝ) :=
      Complex.norm_of_nonneg hlog
    rw [h1]
    calc Real.log (p : ℝ) * ‖∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e‖
        ≤ Real.log (p : ℝ) * (psiK * (p : ℝ) ^ (-s.re)) :=
          mul_le_mul_of_nonneg_left (by simpa [psiK] using hD) hlog
      _ = psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re)) := by ring
  have hgp := gp_lower_bound_line f hf1 hb (c := s.re) hs p hp (le_refl s.re)
  have hc0 : 0 < 1 - 2 * (2 : ℝ) ^ (-s.re) := by
    have h := Work.BMF.two_mul_rpow_neg_two_lt_one hs
    linarith
  have hb_nn : 0 ≤ psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re)) :=
    mul_nonneg psiK_nonneg (mul_nonneg hlog (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hgppos : 0 < ‖Work.BMF.gp f p s‖ := lt_of_lt_of_le hc0 hgp
  rw [norm_div, div_le_div_iff₀ hgppos hc0]
  calc ‖deriv (Work.BMF.gp f p) s‖ * (1 - 2 * (2 : ℝ) ^ (-s.re))
      ≤ (psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re))) * (1 - 2 * (2 : ℝ) ^ (-s.re)) :=
        mul_le_mul_of_nonneg_right hnum hc0.le
    _ ≤ (psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re))) * ‖Work.BMF.gp f p s‖ :=
        mul_le_mul_of_nonneg_left hgp hb_nn

theorem summable_Psi_series (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => deriv (Work.BMF.gp f (p : ℕ)) s / Work.BMF.gp f (p : ℕ) s) ∧
    Summable (fun p : Nat.Primes =>
      -(f (p : ℕ) * (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s))) := by
  constructor
  · have hbase : Summable (fun p : Nat.Primes => Real.log (p : ℝ) * (p : ℝ) ^ (-s.re)) :=
      summable_prime_log_mul_rpow_neg s.re hs
    have hcmp : Summable (fun p : Nat.Primes =>
        (psiK * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re))) / (1 - 2 * (2 : ℝ) ^ (-s.re))) :=
      (hbase.mul_left psiK).div_const _
    exact Summable.of_norm_bounded hcmp (fun p => norm_deriv_div_gp_le f hf1 hb p.2 hs)
  · refine Summable.of_norm_bounded (summable_prime_log_mul_rpow_neg s.re hs) (fun p => ?_)
    have hp : (p : ℕ).Prime := p.2
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hp2 : (0 : ℝ) < (p : ℝ) := by
      have h : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      linarith
    have hpnn : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg hp2.le _
    have hrn : ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_re_ne_zero (p : ℕ)
        (by rw [Complex.neg_re]; linarith), Complex.neg_re]
    have hlogC : ‖(Real.log (p : ℕ) : ℂ)‖ = Real.log (p : ℝ) := Complex.norm_of_nonneg hlog
    rw [norm_neg, norm_mul, norm_mul, hlogC, hrn]
    calc ‖f (p : ℕ)‖ * Real.log (p : ℝ) * (p : ℝ) ^ (-s.re)
        ≤ 1 * Real.log (p : ℝ) * (p : ℝ) ^ (-s.re) := by
          have h1 : ‖f (p : ℕ)‖ ≤ 1 := hb _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hlog) hpnn
      _ = Real.log (p : ℝ) * (p : ℝ) ^ (-s.re) := by ring

end

end Work.BMF.mrlas
