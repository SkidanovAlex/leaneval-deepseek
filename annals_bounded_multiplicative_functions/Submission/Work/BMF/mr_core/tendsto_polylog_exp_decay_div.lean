import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- Auxiliary asymptotics: `C * u^c * (log u)^k * exp (d * u^(1/8) * log u - θ * u)` tends to `0`
at `+∞` for `θ > 0`.  The `exp` factor is absorbed into `exp (θ/2 * u)` and the polylogarithmic
factor into `exp (θ/2 * u)` as well. -/
private lemma tendsto_polylog_exp_decay_div_key (C c k d θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto (fun u : ℝ => C * (u ^ c * (Real.log u) ^ k *
      Real.exp (d * u ^ ((1:ℝ)/8) * Real.log u)) * Real.exp (-(θ * u)))
      Filter.atTop (nhds 0) := by
  have hθ2 : 0 < θ / 2 := by linarith
  have hlogk : (fun u : ℝ => (Real.log u) ^ k) =o[Filter.atTop] (fun u : ℝ => u) := by
    simpa using isLittleO_log_rpow_rpow_atTop k (s := 1) one_pos
  have hmul : (fun u : ℝ => u ^ c * (Real.log u) ^ k) =o[Filter.atTop]
      (fun u : ℝ => u ^ (c + 1)) := by
    have h := hlogk.mul_isBigO (Asymptotics.isBigO_refl (fun u : ℝ => u ^ c) Filter.atTop)
    refine h.congr' ?_ ?_
    · filter_upwards with u
      exact mul_comm _ _
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
      rw [mul_comm u (u ^ c), Real.rpow_add hu c 1, Real.rpow_one u]
  have hA : (fun u : ℝ => u ^ c * (Real.log u) ^ k) =o[Filter.atTop]
      (fun u : ℝ => Real.exp ((θ/2) * u)) :=
    hmul.trans (isLittleO_rpow_exp_pos_mul_atTop (c + 1) hθ2)
  have h_arg_le : ∀ᶠ u : ℝ in Filter.atTop,
      d * u ^ ((1:ℝ)/8) * Real.log u ≤ (θ/2) * u := by
    have hlog78 : Real.log =o[Filter.atTop] (fun u : ℝ => u ^ ((7:ℝ)/8)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have hstep : (fun u : ℝ => Real.log u * u ^ ((1:ℝ)/8)) =o[Filter.atTop]
        (fun u : ℝ => u) := by
      have h := hlog78.mul_isBigO
        (Asymptotics.isBigO_refl (fun u : ℝ => u ^ ((1:ℝ)/8)) Filter.atTop)
      refine h.congr' Filter.EventuallyEq.rfl ?_
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with u hu
      rw [← Real.rpow_add hu (7/8) (1/8)]
      norm_num
    have hdstep : (fun u : ℝ => d * (Real.log u * u ^ ((1:ℝ)/8))) =o[Filter.atTop]
        (fun u : ℝ => u) :=
      hstep.const_mul_left d
    filter_upwards [Asymptotics.IsLittleO.bound hdstep (c := θ/2) hθ2,
      Filter.eventually_ge_atTop (0:ℝ)] with u hb hu
    have hb' : |d * (Real.log u * u ^ ((1:ℝ)/8))| ≤ (θ/2) * u := by
      have hbb := hb
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu] at hbb
    have h1 : d * u ^ ((1:ℝ)/8) * Real.log u = d * (Real.log u * u ^ ((1:ℝ)/8)) := by
      rw [mul_assoc d (u^((1:ℝ)/8)) (Real.log u),
        mul_comm (u ^ ((1:ℝ)/8)) (Real.log u)]
    rw [h1]
    exact le_trans (le_abs_self _) hb'
  have h_exp_le : ∀ᶠ u : ℝ in Filter.atTop,
      Real.exp (d * u ^ ((1:ℝ)/8) * Real.log u) ≤ Real.exp ((θ/2) * u) := by
    filter_upwards [h_arg_le] with u hu
    exact Real.exp_le_exp.mpr hu
  have hB : (fun u : ℝ => Real.exp (d * u ^ ((1:ℝ)/8) * Real.log u)) =O[Filter.atTop]
      (fun u : ℝ => Real.exp ((θ/2) * u)) :=
    Asymptotics.IsBigO.of_norm_eventuallyLE (h_exp_le.mono fun u hu => by
      change ‖Real.exp (d * u ^ ((1:ℝ)/8) * Real.log u)‖ ≤ Real.exp ((θ/2) * u)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hu)
  have hC := hA.mul_isBigO hB
  have hD := hC.congr_right (fun u => by
    rw [← Real.exp_add, show (θ/2)*u + (θ/2)*u = θ*u by ring])
  have hE := hD.mul_isBigO
    (Asymptotics.isBigO_refl (fun u : ℝ => Real.exp (-(θ*u))) Filter.atTop)
  have hF := hE.congr_right (fun u => by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
  have hG := hF.const_mul_left C
  have hKey : (fun u : ℝ => C * (u ^ c * (Real.log u) ^ k *
      Real.exp (d * u ^ ((1:ℝ)/8) * Real.log u)) * Real.exp (-(θ * u))) =o[Filter.atTop]
      (fun _ : ℝ => (1:ℝ)) :=
    hG.congr' (Filter.Eventually.of_forall (fun u => by simp only [mul_assoc]))
      Filter.EventuallyEq.rfl
  exact (Asymptotics.isLittleO_one_iff ℝ).mp hKey

theorem tendsto_polylog_exp_decay_div (C c k d θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto (fun Y : ℝ => C * (Real.log Y) ^ c * (Real.log (Real.log Y)) ^ k *
      Real.exp (d * (Real.log Y) ^ ((1 : ℝ) / 8) * Real.log (Real.log Y)) / Y ^ θ)
      Filter.atTop (nhds 0) := by
  have hkey := tendsto_polylog_exp_decay_div_key C c k d θ hθ
  have hcomp : Filter.Tendsto ((fun u : ℝ => C * (u ^ c * (Real.log u) ^ k *
      Real.exp (d * u ^ ((1:ℝ)/8) * Real.log u)) * Real.exp (-(θ * u))) ∘ Real.log)
      Filter.atTop (nhds 0) := hkey.comp Real.tendsto_log_atTop
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with Y hY
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos hY θ, mul_comm (Real.log Y) θ]
  rw [div_eq_mul_inv]
  rw [Real.exp_neg]
  ring_nf

end Work.BMF.mr_core
