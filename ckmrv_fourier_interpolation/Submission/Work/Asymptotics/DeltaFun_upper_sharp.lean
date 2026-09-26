import Mathlib
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.KPlusXiDefs

namespace Work.Asymptotics

open UpperHalfPlane ModularForm
open scoped Topology

noncomputable section

/-! ## Sharp upper bound for `Δ` on `{1 ≤ Im τ}`

`Δ(τ) = q ∏'ₙ (1 - η_q n(τ))^24` with `q = qParamFun τ = e^{2πiτ}`
(`ModularForm.discriminant_eq_q_prod`), so `‖Δ τ‖ = ‖q‖ · (∏'ₙ ‖1 - η_q n(τ)‖)^24`.
On `{1 ≤ Im τ}` we have `r := ‖q‖ = e^{-2π Im τ} ≤ e^{-2π} ≤ 1/100`, and every factor obeys
`‖1 - η_q n(τ)‖ ≤ 1 + r^{n+1}`.  The elementary infinite-product estimate
`∏'ₙ (1 + r^{n+1}) ≤ (1 - r/(1-r))⁻¹ ≤ 51/50` (from `eˣ ≤ (1-x)⁻¹` and `e^{r^{n+1}} ≥ 1 + r^{n+1}`)
then gives `∏'ₙ ‖1 - η_q n(τ)‖ ≤ 51/50`, and `(51/50)^24 ≤ 2`.  Hence the sharp bound
`‖Δ(τ)‖ ≤ 2 e^{-2π Im τ}` — exactly the form needed to make the funnel tail estimates
uniform in `τ` (see `Submission/Work/Asymptotics/funnelTailQuant.lean`). -/

/-- `e ^ x ≤ (1 - x)⁻¹` for `x < 1`, from `e ^ (-x) ≥ 1 - x` (`Real.add_one_le_exp`). -/
lemma exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have h2 : 0 < 1 - x := by linarith
  have h3 : Real.exp x * (1 - x) ≤ 1 := by
    calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le
      _ = Real.exp (x + -x) := (Real.exp_add x (-x)).symm
      _ = 1 := by simp
  rw [inv_eq_one_div, le_div_iff₀ h2]
  linarith

/-- Finite products: `∏ (1 + aᵢ) ≤ e^{Σ aᵢ}` for `aᵢ ≥ 0`. -/
lemma prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi]) (fun i _ => ?_)
  have h := Real.add_one_le_exp (a i)
  linarith

/-- `∑' n, r^{n+1} = r / (1 - r)` for `0 ≤ r < 1`. -/
lemma tsum_pow_succ_eq (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
  have h0 : (fun n : ℕ => r ^ (n + 1)) = fun n : ℕ => r * r ^ n := by
    funext n; rw [pow_succ]; ring
  rw [h0, tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · ring
  · rwa [Real.norm_eq_abs, abs_of_nonneg hr0]

/-- On the region `{1 ≤ Im τ}` the `q`-parameter is at most `1/100`. -/
lemma exp_neg_two_pi_im_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 100 := by
  have h6 : (6 : ℝ) ≤ 2 * Real.pi * τ.im := by nlinarith [Real.pi_gt_three, hτ]
  have h100 : (100 : ℝ) ≤ Real.exp 6 := by
    have h1 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
    have h2 : (100 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
    linarith
  have hexp : (100 : ℝ) ≤ Real.exp (2 * Real.pi * τ.im) :=
    le_trans h100 (Real.exp_le_exp.mpr h6)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hexp

/-- `(51/50)^24 ≤ 2`. -/
lemma fiftyOne_fiftieth_pow24_le_two : ((51 : ℝ) / 50) ^ 24 ≤ 2 := by
  have h1 : (51 / 50 : ℝ) ≤ Real.exp (1 / 50) := by
    have h := Real.add_one_le_exp (1 / 50 : ℝ)
    norm_num at h ⊢
    linarith
  have h2 : (Real.exp (1 / 50)) ^ 24 = Real.exp (12 / 25) := by
    rw [(Real.exp_nat_mul (1 / 50) 24).symm]
    norm_num
  calc (51 / 50 : ℝ) ^ 24 ≤ (Real.exp (1 / 50)) ^ 24 :=
        pow_le_pow_left₀ (by norm_num) h1 24
    _ = Real.exp (12 / 25) := h2
    _ ≤ (1 - 12 / 25)⁻¹ := exp_le_inv_one_sub (by norm_num)
    _ ≤ 2 := by norm_num

/-- **The eta product is bounded by `51/50` on `{1 ≤ Im τ}`.** -/
lemma tprod_norm_one_sub_eta_q_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖ ≤ 51 / 50 := by
  set r : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact (Real.exp_pos _).le
  have hr100 : r ≤ 1 / 100 := by rw [hr]; exact exp_neg_two_pi_im_le τ hτ
  have hr1 : r < 1 := by linarith
  have hsumm : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have h0 : Summable (fun n : ℕ => r * r ^ n) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left r
    refine h0.congr (fun n => ?_)
    rw [pow_succ]; ring
  have htsum : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := tsum_pow_succ_eq r hr0 hr1
  have hx : r / (1 - r) ≤ 1 / 52 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]
    nlinarith
  have hpow_eq : ∀ n : ℕ, r ^ (n + 1)
      = Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * τ.im)) := by
    intro n
    rw [hr, show -(2 * Real.pi * ((n : ℝ) + 1) * τ.im)
        = ((n + 1 : ℕ) : ℝ) * (-(2 * Real.pi * τ.im)) by push_cast; ring,
      Real.exp_nat_mul]
  have hmult : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable τ.2
  have hmul2 : Multipliable (fun n : ℕ => ‖1 - ModularForm.eta_q n (τ : ℂ)‖) := hmult.norm
  refine hasProd_le_of_prod_le hmul2.hasProd (fun s => ?_)
  calc ∏ i ∈ s, ‖1 - ModularForm.eta_q i (τ : ℂ)‖
      ≤ ∏ i ∈ s, (1 + r ^ (i + 1)) := by
        refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
        have h := norm_sub_le (1 : ℂ) (ModularForm.eta_q i (τ : ℂ))
        rw [norm_one, norm_eta_q] at h
        rw [hpow_eq i]
        exact h
    _ ≤ Real.exp (∑ i ∈ s, r ^ (i + 1)) :=
        prod_one_add_le_exp_sum s _ (fun i _ => pow_nonneg hr0 _)
    _ ≤ Real.exp (r / (1 - r)) := by
        refine Real.exp_le_exp.mpr ?_
        have h := hsumm.sum_le_tsum s (fun i _ => pow_nonneg hr0 _)
        rw [htsum] at h
        exact h
    _ ≤ (1 - 1 / 52)⁻¹ := by
        refine le_trans (exp_le_inv_one_sub (by linarith : r / (1 - r) < 1)) ?_
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ ≤ 51 / 50 := by norm_num

theorem DeltaFun_upper_sharp (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) := by
  have hmult : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable τ.2
  have hprod : ∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖ ≤ 51 / 50 :=
    tprod_norm_one_sub_eta_q_le τ hτ
  have hΔ : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
  have hnorm : ‖Work.Kernels.DeltaFun τ‖
      = Real.exp (-(2 * Real.pi * τ.im))
        * (∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖) ^ 24 := by
    rw [hΔ, ModularForm.discriminant_eq_q_prod,
      show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ from
        (qParamFun_eq_qParam τ).symm,
      norm_mul, norm_qParamFun, hmult.tprod_pow, norm_pow, hmult.norm_tprod]
  rw [hnorm]
  have hnn : (0 : ℝ) ≤ ∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖ := by
    rw [← hmult.norm_tprod]; exact norm_nonneg _
  have h24 : (∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖) ^ 24 ≤ 2 :=
    le_trans (pow_le_pow_left₀ hnn hprod 24) fiftyOne_fiftieth_pow24_le_two
  calc Real.exp (-(2 * Real.pi * τ.im)) * (∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖) ^ 24
      ≤ Real.exp (-(2 * Real.pi * τ.im)) * 2 :=
        mul_le_mul_of_nonneg_left h24 (Real.exp_pos _).le
    _ = 2 * Real.exp (-(2 * Real.pi * τ.im)) := by ring

end

end Work.Asymptotics
