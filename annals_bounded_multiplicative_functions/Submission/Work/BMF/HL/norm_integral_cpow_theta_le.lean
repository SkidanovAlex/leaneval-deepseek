import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

/-- The purely-imaginary power `p^{-iz}` is the exponential of `-(i log p) z`. -/
theorem cpow_neg_I_eq_exp (p : ℕ) (hp : 2 ≤ p) (x : ℝ) :
    (p : ℂ) ^ (-(Complex.I * (x : ℂ)))
      = Complex.exp ((-(Complex.I * (Real.log p : ℂ))) * (x : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    exact_mod_cast (ne_of_gt h)
  rw [Complex.cpow_def_of_ne_zero hp0]
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ p)]
  rw [hlog]
  ring_nf

/-- Norm bound for the `θ`-integral of the purely-imaginary power `p^{-i(u+θ)}`: for `2 ≤ p` and
`0 < δ` this integral is at most `min δ (2/log p)`, written as `δ * min 1 (2/(δ log p))`.
Indeed `∫_0^δ p^{-i(u+θ)} dθ = p^{-iu} (1 - p^{-iδ})/(i log p)`, whose norm is
`|1 - p^{-iδ}|/log p ≤ min (2/log p) δ` because `|1 - e^{-it}| ≤ min 2 |t|`. -/
theorem norm_integral_cpow_theta_le (p : ℕ) (hp : 2 ≤ p) (u : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ θ in (0 : ℝ)..δ, (p : ℂ) ^ (-(Complex.I * ((u + θ : ℝ) : ℂ)))‖
      ≤ δ * min 1 (2 / (δ * Real.log p)) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hLpos : 0 < Real.log p := Real.log_pos hp1
  set L : ℝ := Real.log p with hL
  have hLpos' : 0 < L := by rw [hL]; exact hLpos
  set c : ℂ := -(Complex.I * (L : ℂ)) with hc
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos'.ne'
  have hcne : c ≠ 0 := by rw [hc]; exact neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero hLc)
  have hcnorm : ‖c‖ = L := by
    rw [hc, norm_neg, norm_mul, Complex.norm_I, one_mul]
    simp [abs_of_pos hLpos']
  have hcpow : ∀ x : ℝ, (p:ℂ)^(-(Complex.I*(x:ℂ))) = Complex.exp (c * (x:ℂ)) := by
    intro x
    have heq : -(Complex.I * (Real.log p : ℂ)) = c := by rw [← hL, ← hc]
    rw [cpow_neg_I_eq_exp p hp x, heq]
  have hInt : ∫ θ in (0:ℝ)..δ, (p:ℂ)^(-(Complex.I * ((u+θ:ℝ):ℂ)))
      = Complex.exp (c * (u:ℂ)) * ((Complex.exp (c*(δ:ℂ)) - 1)/c) := by
    have h1 : ∫ θ in (0:ℝ)..δ, (p:ℂ)^(-(Complex.I * ((u+θ:ℝ):ℂ)))
        = ∫ θ in (0:ℝ)..δ, Complex.exp (c * ((u+θ:ℝ):ℂ)) :=
      intervalIntegral.integral_congr fun θ _ => hcpow (u+θ)
    rw [h1]
    have h2 : ∫ θ in (0:ℝ)..δ, Complex.exp (c * ((u+θ:ℝ):ℂ))
        = ∫ θ in (0:ℝ)..δ, Complex.exp (c*(u:ℂ)) * Complex.exp (c*(θ:ℂ)) :=
      intervalIntegral.integral_congr fun θ _ => by
        rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [h2, intervalIntegral.integral_const_mul, integral_exp_mul_complex hcne]
    simp
  have h1u : c * (u:ℂ) = (((-(L*u)):ℝ):ℂ) * Complex.I := by rw [hc]; push_cast; ring
  have hexpu : ‖Complex.exp (c * (u:ℂ))‖ = 1 := by
    rw [h1u, Complex.norm_exp_ofReal_mul_I]
  have h1d : c * (δ:ℂ) = Complex.I * (((-(L*δ)):ℝ):ℂ) := by rw [hc]; push_cast; ring
  have hbound1 : ‖Complex.exp (c*(δ:ℂ)) - 1‖ ≤ L * δ := by
    rw [h1d]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(L*δ))).trans ?_
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (mul_pos hLpos' hδ)]
  have hbound2 : ‖Complex.exp (c*(δ:ℂ)) - 1‖ ≤ 2 := by
    have he : ‖Complex.exp (c*(δ:ℂ))‖ = 1 := by
      rw [h1d, mul_comm, Complex.norm_exp_ofReal_mul_I]
    calc ‖Complex.exp (c*(δ:ℂ)) - 1‖ ≤ ‖Complex.exp (c*(δ:ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [he, norm_one]; norm_num
  have hA : ‖Complex.exp (c * (u:ℂ)) * ((Complex.exp (c*(δ:ℂ)) - 1)/c)‖ ≤ δ := by
    rw [norm_mul, norm_div, hexpu, hcnorm, one_mul, div_le_iff₀ hLpos', mul_comm δ L]
    exact hbound1
  have hB : ‖Complex.exp (c * (u:ℂ)) * ((Complex.exp (c*(δ:ℂ)) - 1)/c)‖ ≤ 2/L := by
    rw [norm_mul, norm_div, hexpu, hcnorm, one_mul, div_le_iff₀ hLpos',
      div_mul_cancel₀ 2 hLpos'.ne']
    exact hbound2
  have key : δ * min 1 (2 / (δ * L)) = min δ (2/L) := by
    rw [mul_min_of_nonneg 1 (2/(δ*L)) hδ.le, mul_one]
    have h2 : δ * (2 / (δ * L)) = 2 / L := by field_simp
    rw [h2]
  rw [hInt, key]
  exact le_min hA hB

end Work.BMF.HL
