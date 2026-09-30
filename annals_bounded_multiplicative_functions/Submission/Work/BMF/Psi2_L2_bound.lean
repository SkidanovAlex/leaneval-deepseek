import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.mrlas.Psi2_assembly
import Submission.Work.BMF.mrlas.powerSeries_circle_inv_L2
import Submission.Work.BMF.mrlas.continuous_circle_integr
import Submission.Work.BMF.mrlas.periodic_window_integral_le
import Submission.Work.BMF.mrlas.T_p_bound
import Submission.Work.BMF.mrlas.primes_log_summable
import Submission.Work.BMF.mrlas.summable_Psi_series

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mean-square (`L²`) bound for `Ψ₂` on the line `Re s = 1 + α`

For every `1`-bounded `f : ℕ → ℂ` with `f 1 = 1`, every `0 < α ≤ 1` and every `c : ℝ` there is
an absolute constant `C > 0` with

`∫_{c}^{c+1} ‖Ψ₂ f (1 + α + i τ)‖² dτ ≤ C / α`.

Here `Ψ₂ f s = Ψ f s - Ψ₁ f s` where `Ψ = Σ_p g_p'(s)/g_p(s)` is the log-derivative of the Euler
product and `Ψ₁ f s = -Σ_p f(p) log p · p^{-s}` is its prime part.

Split `Ψ₂ f s = Σ_p c_p(s)` with `c_p(s) = g_p'(s)/g_p(s) + f(p) log p · p^{-s}`.  For `p ≠ 2`
the pointwise bound `‖c_p‖ ≤ 16 log p · p^{-2σ}‖g_p^{-1}‖ ≤ 32 log p · p^{-2σ}` is summable over
the primes, giving the absolute constant `32 K` with `K = Σ_p log p · p^{-2}`.  Only the prime
`p = 2` needs the mean-square input: on the line `Re s = 1 + α` the local factor `g_2` is the
power series `Σ_e f(2^e) z^e` evaluated at `z = 2^{-1-α} e^{-iτ log 2}`, so

`∫_{c}^{c+1} ‖g_2(1+α+iτ)^{-1}‖² dτ ≤ (2 C₀ / (log 2)²) / α`

by the circle bound `Work.BMF.mrlas.powerSeries_circle_inv_L2` together with the periodic-window
reduction `Work.BMF.mrlas.periodic_window_integral_le`.  Combining the two bounds and squaring
yields the claim.

The per-prime bound `T_p_bound`, the two summability statements and the general assembly
lemmas `Psi2_pointwise_of` / `Psi2_integral_bound_of` are the shared `Work.BMF.mrlas` development;
the mean-square bound for `g_2` and the final assembly are proved here.
-/

namespace Work.BMF

open Real Complex
open scoped BigOperators

/-- For `0 ≤ x ≤ 1`, `1 - e^{-x} ≥ x/2`. -/
private lemma one_sub_exp_neg_ge (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h1 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg]
    have h := Real.add_one_le_exp x
    have h2 : (0:ℝ) < 1 + x := by linarith
    have h3 : (1 + x) ≤ Real.exp x := by linarith
    calc (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := inv_anti₀ h2 h3
      _ = 1 / (1 + x) := by rw [one_div]
  have h2 : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + x)]
    nlinarith [hx0, hx1]
  linarith

/-- The local variable at the prime `2`: `u 2 (σ+iτ) = 2^{-σ} · e^{-iτ log 2}`. -/
private lemma u_two_eq (σ τ : ℝ) :
    Work.BMF.mrlas.u 2 ((σ:ℂ) + (τ:ℂ)*Complex.I)
      = (((2:ℝ)^(-σ) : ℝ) : ℂ) * Complex.exp (((-(τ * Real.log 2)) : ℝ) * Complex.I) := by
  rw [Work.BMF.mrlas.u]
  rw [show Real.log ((2:ℕ):ℝ) = Real.log 2 by norm_num]
  have harg : -(Real.log 2 : ℂ) * ((σ:ℂ)+(τ:ℂ)*Complex.I)
      = ((-(Real.log 2 * σ) : ℝ) : ℂ) + ((-(τ * Real.log 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-- Mean-square bound for the reciprocal local Euler factor at `2` over a unit window on the
line `Re s = 1 + α`: `∫_{c}^{c+1} ‖g_2(1+α+iτ)^{-1}‖² dτ ≤ C/α`. -/
theorem gp2_window_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖(gp f 2 ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ ^ 2)
          ≤ C / α := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.BMF.mrlas.powerSeries_circle_inv_L2
  refine ⟨2 * C₀ / (Real.log 2) ^ 2, by positivity, ?_⟩
  intro f hf1 hb α hα hα1 c
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLle : Real.log 2 ≤ 2 * Real.pi := by
    have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have h2 : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    linarith
  set σ : ℝ := 1 + α with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  set ρ : ℝ := (2:ℝ)^(-σ) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hρ2 : ρ < 1/2 := by
    rw [hρdef, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have h2σ : (2:ℝ) < (2:ℝ)^σ := by
      calc (2:ℝ) = (2:ℝ)^(1:ℝ) := (Real.rpow_one 2).symm
        _ < (2:ℝ)^σ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hσ1
    have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 2) h2σ
    simpa [one_div] using h
  set a : ℕ → ℂ := fun e => f (2^e) with hadef
  have ha0 : a 0 = 1 := by simp [hadef, hf1]
  have hab : ∀ n, ‖a n‖ ≤ 1 := fun n => hb _
  set φ : ℝ → ℝ := fun θ => ‖(∑' e : ℕ, a e * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e)⁻¹‖^2 with hφdef
  have hφcont : Continuous φ := by
    rw [hφdef]; exact Work.BMF.mrlas.continuous_circle_integr a ha0 hab ρ hρpos hρ2
  have hφnn : ∀ θ, 0 ≤ φ θ := by intro θ; rw [hφdef]; positivity
  have hcircle : (∫ θ in (0)..(2*Real.pi), φ θ) ≤ C₀/(1-2*ρ) := by
    rw [hφdef]; exact hC₀ a ha0 hab ρ hρpos hρ2
  have hφper : Function.Periodic φ (2*Real.pi) := by
    intro θ
    have hexp : Complex.exp (((θ + 2*Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ:ℂ)*Complex.I) := by
      rw [show ((θ + 2*Real.pi : ℝ) : ℂ) * Complex.I = (θ:ℂ)*Complex.I + ((2*Real.pi:ℝ):ℂ)*Complex.I by
        push_cast; ring]
      rw [Complex.exp_add]
      rw [show ((2*Real.pi:ℝ):ℂ)*Complex.I = 2 * (Real.pi:ℂ) * Complex.I by push_cast; ring,
        Complex.exp_two_pi_mul_I, mul_one]
    have hsum : (∑' e : ℕ, a e * ((ρ:ℂ) * Complex.exp (((θ+2*Real.pi:ℝ):ℂ) * Complex.I))^e)
        = (∑' e : ℕ, a e * ((ρ:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))^e) := by
      apply tsum_congr; intro e; rw [hexp]
    rw [hφdef]
    simp only
    rw [hsum]
  have hpt : ∀ τ : ℝ,
      ‖(gp f 2 ((σ:ℂ)+(τ:ℂ)*Complex.I))⁻¹‖^2 = φ (-(τ * Real.log 2)) := by
    intro τ
    have hgp : gp f 2 ((σ:ℂ)+(τ:ℂ)*Complex.I)
        = ∑' e : ℕ, a e * ((ρ:ℂ) * Complex.exp (((-(τ * Real.log 2)):ℝ) * Complex.I))^e := by
      rw [Work.BMF.mrlas.gp_eq f Nat.prime_two]
      apply tsum_congr; intro e
      change f (2^e) * (Work.BMF.mrlas.u 2 ((σ:ℂ)+(τ:ℂ)*Complex.I))^e
        = f (2^e) * ((ρ:ℂ) * Complex.exp (((-(τ * Real.log 2)):ℝ) * Complex.I))^e
      rw [u_two_eq σ τ]
    rw [hgp, hφdef]
  have hsub : (∫ τ in c..(c+1), φ (-(τ * Real.log 2)))
      = (Real.log 2)⁻¹ * ∫ u in (-((c+1) * Real.log 2))..(-(c * Real.log 2)), φ u := by
    have h := intervalIntegral.integral_comp_mul_left (a := c) (b := c + 1)
      (c := -Real.log 2) φ (by rw [neg_ne_zero]; exact hLpos.ne')
    have hL' := h
    rw [show (∫ x in c..(c + 1), φ ((-Real.log 2) * x))
          = (∫ x in c..(c + 1), φ (-(x * Real.log 2))) by
        apply intervalIntegral.integral_congr; intro x _
        show φ ((-Real.log 2) * x) = φ (-(x * Real.log 2))
        congr 1; ring] at hL'
    rw [hL']
    have h1 : (-Real.log 2) * c = -(c * Real.log 2) := by ring
    have h2 : (-Real.log 2) * (c + 1) = -((c + 1) * Real.log 2) := by ring
    rw [h1, h2]
    have hsym : (∫ x in -(c * Real.log 2)..-((c+1) * Real.log 2), φ x)
        = -∫ x in -((c+1) * Real.log 2)..-(c * Real.log 2), φ x :=
      intervalIntegral.integral_symm (-((c+1) * Real.log 2)) (-(c * Real.log 2))
    rw [hsym]
    simp only [neg_inv, smul_eq_mul]
    ring
  have hwin : (∫ u in (-((c+1) * Real.log 2))..(-(c * Real.log 2)), φ u)
      ≤ ∫ θ in (0)..(2*Real.pi), φ θ := by
    have hp := Work.BMF.mrlas.periodic_window_integral_le (φ := φ)
      (p := 2*Real.pi) (L := Real.log 2) (a := -((c+1) * Real.log 2))
      (by positivity) hφper hφnn hLpos.le hLle hφcont
    convert hp using 3 <;> ring
  have hfinal : (Real.log 2)⁻¹ * (C₀/(1-2*ρ)) ≤ (2 * C₀ / (Real.log 2) ^ 2) / α := by
    have hx0 : 0 ≤ α * Real.log 2 := by positivity
    have hxle : α * Real.log 2 ≤ 1 := by
      have h1 : α * Real.log 2 ≤ 1 * Real.log 2 := mul_le_mul_of_nonneg_right hα1 hLpos.le
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have hge := one_sub_exp_neg_ge (α * Real.log 2) hx0 hxle
    have he : Real.exp (-(α * Real.log 2)) = 2 * ρ := by
      rw [hρdef]
      have h1 : 2 * (2:ℝ)^(-σ) = (2:ℝ)^(1 + -σ) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      rw [h1, show (1:ℝ) + -σ = -α by rw [hσdef]; ring,
        Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      ring_nf
    have hρge : α * Real.log 2 / 2 ≤ 1 - 2*ρ := by rw [he] at hge; linarith
    have hp0 : 0 < 1 - 2*ρ := by linarith
    have hkey : Real.log 2 * α ≤ 2 * (1 - 2*ρ) := by linarith
    rw [div_eq_mul_inv, div_eq_mul_inv]
    field_simp
    nlinarith [hkey, hC₀pos, hLpos, hα, hp0]
  calc (∫ τ in c..(c+1), ‖(gp f 2 ((σ:ℂ)+(τ:ℂ)*Complex.I))⁻¹‖^2)
      = ∫ τ in c..(c+1), φ (-(τ * Real.log 2)) := intervalIntegral.integral_congr (fun τ _ => hpt τ)
    _ = (Real.log 2)⁻¹ * ∫ u in (-((c+1) * Real.log 2))..(-(c * Real.log 2)), φ u := hsub
    _ ≤ (Real.log 2)⁻¹ * ∫ θ in (0)..(2*Real.pi), φ θ := mul_le_mul_of_nonneg_left hwin (by positivity)
    _ ≤ (Real.log 2)⁻¹ * (C₀/(1-2*ρ)) := mul_le_mul_of_nonneg_left hcircle (by positivity)
    _ ≤ (2 * C₀ / (Real.log 2) ^ 2) / α := hfinal

theorem Psi2_L2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖Work.BMF.Psi2 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
          ≤ C / α := by
  obtain ⟨Cr, hCrpos, hres⟩ := gp2_window_L2
  obtain ⟨K, hK0, hK⟩ := Work.BMF.mrlas.primes_log_summable
  refine ⟨2 * (16 * Real.log 2) ^ 2 * Cr + 2 * (32 * K) ^ 2, ?_, ?_⟩
  · have h1 : 0 < (16 * Real.log 2) ^ 2 := by positivity
    nlinarith [hCrpos, sq_nonneg (32 * K)]
  · intro f hf1 hb α hα hα1 c
    refine Work.BMF.mrlas.Psi2_integral_bound_of (16 * Real.log 2) (32 * K)
      (by positivity) (by positivity) (fun f' hf1' hb' s hs => ?_) Cr hres f hf1 hb α hα hα1 c
    exact Work.BMF.mrlas.Psi2_pointwise_of Work.BMF.mrlas.T_p_bound
      Work.BMF.mrlas.summable_Psi_series K hK f' hf1' hb' hs

end Work.BMF
