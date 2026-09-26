import Mathlib
import Submission.Work.Asymptotics.funnelTailQuant

namespace Work.Asymptotics

/-- **Sharp lower bound for `Δ` on the funnel.**

`‖Δ(τ)‖ ≥ (1/2) e^{-2π Im τ}` for `Im τ ≥ 2`, the sharp form of `Work.Kernels.DeltaFun_lower`
(which gives `(1/2)^24`).  It is the quantitative input that makes the funnel tail estimates
uniform: it gives `‖j τ‖ ≤ 6.75 e^{2π Im τ}` (with the explicit bound `‖E₄ τ‖ ≤ 3/2`), hence
`‖Δ(it) j τ‖ ≤ 6.75 e^{-2π} ≤ 1/16` for `t ≥ Im τ + 1`, i.e. an absolute lower bound for the
CKMRV divisor `Δ(it)(j τ - j(it))` with *no* `τ`-dependent threshold.

*Proof.*  `Δ(τ) = q ∏'ₙ (1 - η_q n(τ))^24` (`ModularForm.discriminant_eq_q_prod`), with
`q = qParamFun τ = e^{2πiτ}`, `‖q‖ = e^{-2π Im τ}`, `‖η_q n(τ)‖ = e^{-2π(n+1) Im τ}` and
`‖1 - η_q n‖ ≥ 1 - ‖η_q n‖`.  The elementary infinite-product estimate
`∏'ₙ (1-aₙ) ≥ 1 - Σ'ₙ aₙ` (proved in `Submission/Work/Asymptotics/funnelTailQuant.lean` as
`tprod_one_sub_ge_one_sub_tsum`) applied to `aₙ = ‖η_q n(τ)‖` gives, since
`Σ'ₙ ‖η_q n(τ)‖ = r/(1-r) ≤ 2r` with `r = ‖q‖ ≤ e^{-4π}`,
`∏'ₙ ‖1 - η_q n(τ)‖ ≥ 1 - 2r ≥ 1 - 2e^{-4π}`.  The 24th power of the last number is `≥ 1/2`
(e.g. by Bernoulli, `(1-x)^24 ≥ 1 - 24x` with `x = 2e^{-4π} ≤ 1/10`), and
`‖Δ τ‖ = ‖q‖ ∏'ₙ ‖1 - η_q n(τ)‖^24 ≥ ‖q‖/2`. -/
theorem DeltaFun_funnel_lower_sharp {τ : UpperHalfPlane} (hτ : 2 ≤ τ.im) :
    (1 / 2) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  have hq_lt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliable_one_sub_pow hq_lt
  set r : ℝ := ‖Function.Periodic.qParam 1 (τ : ℂ)‖ with hrdef
  have hnormq : r = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hrdef, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]; congr 1; ring
  have hr0 : 0 ≤ r := by rw [hrdef]; exact norm_nonneg _
  have hr_le : r ≤ 1 / 96 := by
    rw [hnormq]
    have h96 : (96 : ℝ) ≤ Real.exp (4 * Real.pi) := by
      have h12 : (12 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hmono : Real.exp 12 ≤ Real.exp (4 * Real.pi) := Real.exp_le_exp.mpr h12
      have hexp12 : (96 : ℝ) ≤ Real.exp 12 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
        have hp : (2 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h2 12
        have he : Real.exp 12 = Real.exp 1 ^ 12 := by
          rw [show (12:ℝ) = ((12:ℕ):ℝ) * (1:ℝ) by norm_num, Real.exp_nat_mul]
        rw [he]
        norm_num at hp
        linarith
      linarith
    have hle : -(2 * Real.pi * τ.im) ≤ -(4 * Real.pi) := by
      nlinarith [Real.pi_pos, hτ]
    calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(4 * Real.pi)) := Real.exp_le_exp.mpr hle
      _ = 1 / Real.exp (4 * Real.pi) := by rw [Real.exp_neg, inv_eq_one_div]
      _ ≤ 1 / 96 := one_div_le_one_div_of_le (by norm_num) h96
  have hr1 : r < 1 := by linarith
  have hr_half : r ≤ 1 / 2 := by linarith
  have hprod : 1 - 2 * r ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))‖ := by
    have hlim := hmul.tendsto_prod_tprod_nat
    refine ge_of_tendsto hlim.norm ?_
    filter_upwards with N
    have hfac : ∀ n : ℕ, 1 - r ^ (n + 1) ≤ ‖(1 - ModularForm.eta_q n (τ : ℂ))‖ := by
      intro n
      have hnorm : ‖ModularForm.eta_q n (τ : ℂ)‖ = r ^ (n + 1) := by
        simp [ModularForm.eta_q, hrdef, norm_pow]
      have h := norm_add_le (1 - ModularForm.eta_q n (τ : ℂ)) (ModularForm.eta_q n (τ : ℂ))
      rw [sub_add_cancel, norm_one] at h
      rw [hnorm] at h
      linarith
    have hsumm : Summable (fun n : ℕ => r ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
    have hgeom : ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ 2 * r := by
      have h1 : ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∑' n : ℕ, r ^ (n + 1) :=
        hsumm.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg hr0 _)
      have htsum : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
        have heq : (fun n : ℕ => r ^ (n + 1)) = fun n : ℕ => r * r ^ n := by
          funext n; rw [pow_succ]; ring
        rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        ring
      have h2 : r / (1 - r) ≤ 2 * r := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - r)]
        nlinarith [hr0, hr_half]
      calc ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∑' n : ℕ, r ^ (n + 1) := h1
        _ = r / (1 - r) := htsum
        _ ≤ 2 * r := h2
    have h2 : 1 - ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∏ n ∈ Finset.range N, (1 - r ^ (n + 1)) :=
      one_sub_sum_le_prod_one_sub (Finset.range N) (fun n => r ^ (n + 1))
        (fun n _ => pow_nonneg hr0 _) (fun n _ => pow_le_one₀ hr0 (le_of_lt hr1))
    have h1 : ∏ n ∈ Finset.range N, (1 - r ^ (n + 1))
        ≤ ∏ n ∈ Finset.range N, ‖(1 - ModularForm.eta_q n (τ : ℂ))‖ :=
      Finset.prod_le_prod₀ (fun n _ => by
        have : r ^ (n+1) ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr1)
        linarith) (fun n _ => hfac n)
    rw [norm_prod]
    linarith
  have hDelta : ‖Work.Kernels.DeltaFun τ‖
      = Real.exp (-(2*Real.pi*τ.im)) * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ ^ 24 := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant,
        ModularForm.discriminant_eq_q_prod, norm_mul, hmul.tprod_pow, norm_pow, ← hrdef, hnormq]
  have hbase : (1:ℝ)/2 ≤ (1 - 2*r)^24 := by
    have hb : (1:ℝ) - 48 * r ≤ (1 - 2*r)^24 := by
      have h1 : (1:ℝ) + (24:ℝ) * (-(2*r)) = 1 - 48*r := by ring
      have h2 : (1:ℝ) + -(2*r) = 1 - 2*r := by ring
      rw [← h1, ← h2]
      exact one_add_mul_le_pow (a := -(2*r)) (by linarith [hr0] : (-2:ℝ) ≤ -(2*r)) (24:ℕ)
    have h48 : 48 * r ≤ 1/2 := by linarith [hr_le]
    linarith
  have hnonneg : 0 ≤ 1 - 2*r := by linarith [hr_half]
  have h24 : (1:ℝ)/2 ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ ^ 24 :=
    le_trans hbase (pow_le_pow_left₀ hnonneg hprod 24)
  calc (1:ℝ)/2 * Real.exp (-(2*Real.pi*τ.im))
      = Real.exp (-(2*Real.pi*τ.im)) * (1/2) := by ring
    _ ≤ Real.exp (-(2*Real.pi*τ.im)) * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ ^ 24 :=
        mul_le_mul_of_nonneg_left h24 (Real.exp_nonneg _)
    _ = ‖Work.Kernels.DeltaFun τ‖ := hDelta.symm

end Work.Asymptotics
