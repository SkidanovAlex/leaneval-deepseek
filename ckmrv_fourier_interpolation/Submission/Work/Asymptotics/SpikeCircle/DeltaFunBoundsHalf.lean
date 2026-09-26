import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic

namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane ModularForm
open scoped Topology

noncomputable section

private lemma eta_prod_multipliable (τ : ℍ) :
    Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) := by
  have hq_lt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
  exact ModularForm.multipliable_one_sub_pow hq_lt

private lemma norm_qParam_one (τ : ℍ) :
    ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
  congr 1; ring

private lemma exp_le_inv_one_sub' {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
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

private lemma prod_one_add_le_exp_sum' {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi]) (fun i _ => ?_)
  have h := Real.add_one_le_exp (a i)
  linarith

private lemma exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h := exp_le_inv_one_sub' (x := (1 / 2 : ℝ)) (by norm_num)
  norm_num at h
  exact h

private lemma tsum_norm_eta_q_le_half (τ : ℍ) (hτ : (1 / 2 : ℝ) ≤ τ.im) :
    ∑' n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ 1 / 2 := by
  have hexp : Real.exp (-Real.pi) ≤ 1 / 3 := by
    have h3 : (3 : ℝ) ≤ Real.exp Real.pi := by
      have h4 : (3 : ℝ) ≤ Real.exp 3 := by
        have h5 := Real.add_one_le_exp (2 : ℝ)
        have h6 : Real.exp 2 ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
        linarith
      exact le_trans h4 (Real.exp_le_exp.mpr (le_of_lt Real.pi_gt_three))
    rw [Real.exp_neg, show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 3)).mpr h3
  have hbound : ∀ n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ (1 / 3 : ℝ) ^ (n + 1) := by
    intro n
    rw [Work.Asymptotics.norm_eta_q n τ]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hle : -(2 * Real.pi * ((n : ℝ) + 1) * τ.im) ≤ -(Real.pi * ((n : ℝ) + 1)) := by
      have hπ : (0 : ℝ) ≤ Real.pi * ((n : ℝ) + 1) := by positivity
      have h2t : (1 : ℝ) ≤ 2 * τ.im := by linarith
      have hkey : Real.pi * ((n : ℝ) + 1) ≤ 2 * Real.pi * ((n : ℝ) + 1) * τ.im := by
        calc Real.pi * ((n : ℝ) + 1) = Real.pi * ((n : ℝ) + 1) * 1 := by ring
          _ ≤ Real.pi * ((n : ℝ) + 1) * (2 * τ.im) := mul_le_mul_of_nonneg_left h2t hπ
          _ = 2 * Real.pi * ((n : ℝ) + 1) * τ.im := by ring
      exact neg_le_neg hkey
    refine le_trans (Real.exp_le_exp.mpr hle) ?_
    rw [show -(Real.pi * ((n : ℝ) + 1)) = ((n + 1 : ℕ) : ℝ) * (-Real.pi) by rw [hcast]; ring]
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hexp (n + 1)
  have hsumm3 : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ (n + 1)) := by
    have h0 : (0 : ℝ) ≤ 1 / 3 := by norm_num
    have h1 : (1 / 3 : ℝ) < 1 := by norm_num
    have h := (summable_geometric_of_lt_one h0 h1).mul_left (1 / 3 : ℝ)
    simpa [pow_succ, mul_comm] using h
  have hS : ∑' n : ℕ, (1 / 3 : ℝ) ^ (n + 1) = 1 / 2 := by
    have h0 : (0 : ℝ) ≤ 1 / 3 := by norm_num
    have h1 : (1 / 3 : ℝ) < 1 := by norm_num
    have hsplit : (fun n : ℕ => (1 / 3 : ℝ) ^ (n + 1)) = fun n : ℕ => (1 / 3) * (1 / 3) ^ n := by
      funext n; rw [pow_succ, mul_comm]
    rw [hsplit, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    norm_num
  have hsum : Summable (fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖) := by
    simpa using ModularForm.summable_eta_q τ
  calc ∑' n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖
      ≤ ∑' n : ℕ, (1 / 3 : ℝ) ^ (n + 1) := Summable.tsum_le_tsum hbound hsum hsumm3
    _ = 1 / 2 := hS

private lemma tprod_norm_eta_q_ge_half (τ : ℍ) (hτ : (1 / 2 : ℝ) ≤ τ.im) :
    (1 / 2 : ℝ) ≤ ∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖ := by
  have hsum := tsum_norm_eta_q_le_half τ hτ
  have hsumm : Summable (fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖) := by
    simpa using ModularForm.summable_eta_q τ
  have hr0 : ∀ n : ℕ, (0 : ℝ) ≤ ‖ModularForm.eta_q n (τ : ℂ)‖ := fun n => norm_nonneg _
  have hr1 : ∀ n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ 1 := by
    intro n
    rw [Work.Asymptotics.norm_eta_q, Real.exp_le_one_iff]
    have h0 : (0 : ℝ) < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
    nlinarith [mul_pos h0 τ.im_pos]
  have hmult := eta_prod_multipliable τ
  have hmul2 : Multipliable (fun n : ℕ => ‖1 - ModularForm.eta_q n (τ : ℂ)‖) := hmult.norm
  refine le_hasProd_of_le_prod hmul2.hasProd (fun s => ?_)
  have hs : ∑ i ∈ s, ‖ModularForm.eta_q i (τ : ℂ)‖ ≤ 1 / 2 :=
    le_trans (hsumm.sum_le_tsum s (fun i _ => hr0 i)) hsum
  have h1 : 1 - ∑ i ∈ s, ‖ModularForm.eta_q i (τ : ℂ)‖
      ≤ ∏ i ∈ s, (1 - ‖ModularForm.eta_q i (τ : ℂ)‖) :=
    Work.Asymptotics.one_sub_sum_le_prod s _ (fun i _ => hr0 i) (fun i _ => hr1 i)
  have h2 : ∏ i ∈ s, (1 - ‖ModularForm.eta_q i (τ : ℂ)‖)
      ≤ ∏ i ∈ s, ‖1 - ModularForm.eta_q i (τ : ℂ)‖ :=
    Work.Asymptotics.prod_le_prod_of_nonneg s _ _ (fun i _ => by linarith [hr1 i])
      (fun i _ => by
        have hh := norm_sub_norm_le (1 : ℂ) (ModularForm.eta_q i (τ : ℂ))
        rw [norm_one] at hh
        linarith)
      (fun i _ => norm_nonneg _)
  linarith

private lemma tprod_norm_eta_q_le_two (τ : ℍ) (hτ : (1 / 2 : ℝ) ≤ τ.im) :
    ∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖ ≤ 2 := by
  have hsum := tsum_norm_eta_q_le_half τ hτ
  have hsumm : Summable (fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖) := by
    simpa using ModularForm.summable_eta_q τ
  have hmult := eta_prod_multipliable τ
  have hmul2 : Multipliable (fun n : ℕ => ‖1 - ModularForm.eta_q n (τ : ℂ)‖) := hmult.norm
  refine hasProd_le_of_prod_le hmul2.hasProd (fun s => ?_)
  have h1 : ∏ i ∈ s, ‖1 - ModularForm.eta_q i (τ : ℂ)‖
      ≤ ∏ i ∈ s, (1 + ‖ModularForm.eta_q i (τ : ℂ)‖) :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => by
      have hh := norm_sub_le (1 : ℂ) (ModularForm.eta_q i (τ : ℂ))
      rw [norm_one] at hh
      linarith)
  have h2 : ∏ i ∈ s, (1 + ‖ModularForm.eta_q i (τ : ℂ)‖)
      ≤ Real.exp (∑ i ∈ s, ‖ModularForm.eta_q i (τ : ℂ)‖) :=
    prod_one_add_le_exp_sum' s _ (fun i _ => norm_nonneg _)
  have h3 : Real.exp (∑ i ∈ s, ‖ModularForm.eta_q i (τ : ℂ)‖) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.mpr (le_trans (hsumm.sum_le_tsum s (fun i _ => norm_nonneg _)) hsum)
  linarith [h1, h2, h3, exp_half_le_two]

theorem DeltaFunBoundsHalf : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w : UpperHalfPlane, 1 / 2 ≤ w.im → c * Real.exp (-(2 * Real.pi * w.im)) ≤ ‖Work.Kernels.DeltaFun w‖ ∧ ‖Work.Kernels.DeltaFun w‖ ≤ C * Real.exp (-(2 * Real.pi * w.im)) := by
  refine ⟨(1 / 2 : ℝ) ^ 24, (2 : ℝ) ^ 24, by positivity, by positivity, fun w hw => ?_⟩
  have hD : Work.Kernels.DeltaFun w = ModularForm.discriminant w := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
  have hmult := eta_prod_multipliable w
  have hnorm : ‖Work.Kernels.DeltaFun w‖ =
      Real.exp (-(2 * Real.pi * w.im)) * (∏' n : ℕ, ‖1 - ModularForm.eta_q n (w : ℂ)‖) ^ 24 := by
    rw [hD, ModularForm.discriminant_eq_q_prod, norm_mul, hmult.tprod_pow, norm_pow,
      hmult.norm_tprod, norm_qParam_one]
  have hPlo := tprod_norm_eta_q_ge_half w hw
  have hPhi := tprod_norm_eta_q_le_two w hw
  have hP0 : (0 : ℝ) ≤ ∏' n : ℕ, ‖1 - ModularForm.eta_q n (w : ℂ)‖ := by linarith
  constructor
  · rw [hnorm]
    have h24 : (1 / 2 : ℝ) ^ 24 ≤ (∏' n : ℕ, ‖1 - ModularForm.eta_q n (w : ℂ)‖) ^ 24 :=
      pow_le_pow_left₀ (by norm_num) hPlo 24
    calc (1 / 2 : ℝ) ^ 24 * Real.exp (-(2 * Real.pi * w.im))
        = Real.exp (-(2 * Real.pi * w.im)) * (1 / 2 : ℝ) ^ 24 := by ring
      _ ≤ Real.exp (-(2 * Real.pi * w.im))
            * (∏' n : ℕ, ‖1 - ModularForm.eta_q n (w : ℂ)‖) ^ 24 :=
          mul_le_mul_of_nonneg_left h24 (Real.exp_nonneg _)
  · rw [hnorm]
    have h24 : (∏' n : ℕ, ‖1 - ModularForm.eta_q n (w : ℂ)‖) ^ 24 ≤ (2 : ℝ) ^ 24 :=
      pow_le_pow_left₀ hP0 hPhi 24
    calc Real.exp (-(2 * Real.pi * w.im))
          * (∏' n : ℕ, ‖1 - ModularForm.eta_q n (w : ℂ)‖) ^ 24
        ≤ Real.exp (-(2 * Real.pi * w.im)) * (2 : ℝ) ^ 24 :=
          mul_le_mul_of_nonneg_left h24 (Real.exp_nonneg _)
      _ = (2 : ℝ) ^ 24 * Real.exp (-(2 * Real.pi * w.im)) := by ring

end

end Work.Asymptotics.SpikeCircle
