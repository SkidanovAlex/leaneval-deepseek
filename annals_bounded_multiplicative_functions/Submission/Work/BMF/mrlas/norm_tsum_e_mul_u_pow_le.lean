import Mathlib
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex MeasureTheory
open scoped BigOperators

/-- Bound for the "derivative-type" power series `Σ_e e · f(p^e) · u^e` with `u = p^{-s}`:
its norm is at most `(Σ_e e (1/2)^{e-1}) · p^{-Re s}`. -/
theorem norm_tsum_e_mul_u_pow_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    ‖∑' e : ℕ, (e : ℂ) * f (p ^ e) * (Work.BMF.mrlas.u p s) ^ e‖
      ≤ (∑' e : ℕ, (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1)) * (p : ℝ) ^ (-s.re) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  have hx0 : 0 ≤ (p:ℝ)^(-s.re) := Real.rpow_nonneg hp0.le _
  have hxhalf : (p:ℝ)^(-s.re) ≤ 1/2 := by
    have h1 : (p:ℝ)^(-s.re) ≤ (p:ℝ)^(-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (p:ℝ)^(-1:ℝ) ≤ 1/2 := by
      rw [Real.rpow_neg_one]
      have h3 := one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num)
        (show (2:ℝ) ≤ (p:ℝ) by exact_mod_cast hp.two_le)
      simpa [one_div] using h3
    linarith
  have hsum2 : Summable (fun e : ℕ => (e:ℝ) * (1/2:ℝ)^e) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2:ℝ)) (by norm_num)
    simpa [pow_one] using h
  have hG : Summable (fun e : ℕ => (e:ℝ) * (1/2:ℝ)^(e-1)) := by
    have heq : (fun e : ℕ => (e:ℝ) * (1/2:ℝ)^(e-1))
        = fun e : ℕ => 2 * ((e:ℝ) * (1/2:ℝ)^e) := by
      funext e
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
        rw [Nat.succ_sub_one, pow_succ]
        push_cast
        ring
    rw [heq]
    exact hsum2.mul_left 2
  have hmain : ∀ e : ℕ,
      (e:ℝ) * ((p:ℝ)^(-s.re))^e ≤ (e:ℝ) * (1/2:ℝ)^(e-1) * (p:ℝ)^(-s.re) := by
    intro e
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
      have hxm : ((p:ℝ)^(-s.re))^m ≤ (1/2:ℝ)^m := pow_le_pow_left₀ hx0 hxhalf m
      rw [Nat.succ_sub_one, pow_succ]
      push_cast
      have h2 : ((m:ℝ)+1) * (((p:ℝ)^(-s.re))^m * (p:ℝ)^(-s.re))
          ≤ ((m:ℝ)+1) * ((1/2:ℝ)^m * (p:ℝ)^(-s.re)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hxm hx0
      linarith [h2]
  have hle : ∀ e : ℕ, ‖(e:ℂ) * f (p^e) * (u p s)^e‖
      ≤ (e:ℝ) * (1/2:ℝ)^(e-1) * (p:ℝ)^(-s.re) := by
    intro e
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_u hp.pos]
    calc (e:ℝ) * ‖f (p^e)‖ * ((p:ℝ)^(-s.re))^e
        ≤ (e:ℝ) * 1 * ((p:ℝ)^(-s.re))^e := by gcongr; exact hb _
      _ = (e:ℝ) * ((p:ℝ)^(-s.re))^e := by ring
      _ ≤ (e:ℝ) * (1/2:ℝ)^(e-1) * (p:ℝ)^(-s.re) := hmain e
  have hnormsum : Summable (fun e : ℕ => ‖(e:ℂ) * f (p^e) * (u p s)^e‖) :=
    Summable.of_nonneg_of_le (fun e => norm_nonneg _) hle (hG.mul_right _)
  calc ‖∑' e : ℕ, (e:ℂ) * f (p^e) * (u p s)^e‖
      ≤ ∑' e : ℕ, ‖(e:ℂ) * f (p^e) * (u p s)^e‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' e : ℕ, (e:ℝ) * (1/2:ℝ)^(e-1) * (p:ℝ)^(-s.re) :=
        Summable.tsum_le_tsum hle hnormsum (hG.mul_right _)
    _ = (∑' e : ℕ, (e:ℝ) * (1/2:ℝ)^(e-1)) * (p:ℝ)^(-s.re) := tsum_mul_right

end Work.BMF.mrlas
