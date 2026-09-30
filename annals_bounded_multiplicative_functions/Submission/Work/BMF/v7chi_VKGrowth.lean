import Mathlib
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.HurwitzShift
import Submission.Work.BMF.vk_exp_sum
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.N7.V2_zeta_strip
import Submission.Work.BMF.N7.dyadic_vk_sum_bound
import Submission.Work.BMF.VKChain.block_sum_uniform
import Submission.Work.BMF.VKChain.shift_head_bound
import Submission.Work.BMF.VKChain.shift_vk_range_bound
import Submission.Work.BMF.VKChain.kl_tail_block_bound
import Submission.Work.BMF.VKChain.shiftTerm_kl_range_le
import Submission.Work.BMF.v7chi_kl_range_arith
import Submission.Work.BMF.v7chi_tail_arith
import Submission.Work.BMF.v7chi_head_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF

open Finset Complex
open scoped Topology BigOperators

noncomputable section

/-- **`VKExpInput` is antitone in the range constant.**  Shrinking the range exponent `c` leaves
the Vinogradov–Korobov exponential-sum bound valid: the hypothesis `log t ≤ c (log N)^{7/6}`
becomes harder to satisfy, and the right-hand side `C N^{1 - c g}` becomes larger (`g ≥ 0`). -/
lemma VKExpInput_mono {C c c' : ℝ} (h : VKExpInput C c) (hc'0 : 0 < c') (hc'c : c' ≤ c) :
    VKExpInput C c' := by
  obtain ⟨hC, _hc, hbody⟩ := h
  refine ⟨hC, hc'0, ?_⟩
  intro N t hN hNt hlog u hu hu1 R hNR hR2N
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogNt : Real.log N ≤ Real.log t := Real.log_le_log (by linarith) hNt
  have hlogr : 0 ≤ Real.log N ^ (7 / 6 : ℝ) := Real.rpow_nonneg hlogNpos.le _
  have hlog' : Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) :=
    le_trans hlog (mul_le_mul_of_nonneg_right hc'c hlogr)
  have hb := hbody N t hN hNt hlog' u hu hu1 R hNR hR2N
  have hg : 0 ≤ (Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2) := by
    refine div_nonneg (sq_nonneg _) ?_
    refine Real.log_nonneg ?_
    have h1 : 1 ≤ Real.log t / Real.log N := (le_div_iff₀ hlogNpos).mpr (by linarith)
    linarith
  refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hC.le)
  refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
  have hmul : c' * ((Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2))
      ≤ c * ((Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2)) :=
    mul_le_mul_of_nonneg_right hc'c hg
  have e1 : c * (Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2)
      = c * ((Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2)) := by ring
  have e2 : c' * (Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2)
      = c' * ((Real.log N / Real.log t) ^ 2 / Real.log (Real.log t / Real.log N + 2)) := by ring
  rw [e1, e2]
  linarith

/-- **The Riemann-zeta growth bound in the VK strip** (node V2 for `ζ`), deduced from
`Work.BMF.N7.zeta_strip_bound_of_vk_aux` and the V1 input, with the range constant normalised
to `≤ 1/4`. -/
lemma zeta_growth_v7 {Cvk cvk : ℝ} (hVK : VKExpInput Cvk cvk) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1 / 4 ∧ ∀ σ t : ℝ, 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  have hV1 : Work.BMF.N7.VKExpSumRaw :=
    ⟨Cvk, cvk, hVK.1, hVK.2.1, fun N t hN hNt hlog u hu hu1 R hNR hR2N =>
      hVK.2.2 N t hN hNt hlog u hu hu1 R hNR hR2N⟩
  obtain ⟨A, c, hA, hc, hreg⟩ :=
    Work.BMF.N7.zeta_strip_bound_of_vk_aux hV1
      (fun c₀ cζ h₀ hζ => Work.BMF.N7.dyadic_vk_sum_bound c₀ cζ h₀ hζ)
  refine ⟨A, min (1 / 4) c, hA, lt_min (by norm_num) hc, min_le_left _ _, ?_⟩
  intro σ t ht hσ hσ2
  refine hreg σ t ht ?_ hσ2
  have hLpos : 0 < Real.log (|t| + 3) := by
    have h6 : (6 : ℝ) ≤ |t| + 3 := by have := abs_nonneg t; linarith
    have h1 : (1 : ℝ) < Real.log 6 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact lt_trans Real.exp_one_lt_three (by norm_num)
    exact lt_of_lt_of_le (lt_trans zero_lt_one h1) (Real.log_le_log (by norm_num) h6)
  have hLnn : 0 ≤ Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := Real.rpow_nonneg hLpos.le _
  have hle : min (1 / 4) c ≤ c := min_le_right _ _
  nlinarith [hσ, hLnn, hle]

/-! ## The shift-difference series -/

/-- **The shift-difference series at bounded heights**, via the trivial tail bound. -/
lemma shift_series_small {cvk a σ t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hσ : 1 / 2 ≤ σ)
    (hσ2 : σ ≤ 2) (ht : |t| < Real.exp (1000 / cvk ^ 6)) :
    ‖∑' m : ℕ, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * (2 + Real.exp (1000 / cvk ^ 6))) *
        (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  have hσpos : 0 < σ := by linarith
  have hsre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  have htail := norm_tsum_shiftTerm_tail_le (a := a) ha ha1
    (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hsre]; exact hσpos) 0
  have htail' : ‖∑' m : ℕ, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ) * a ^ (-σ) := by
    simpa [hsre] using htail
  have hsnorm : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 2 + |t| := by
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = σ + |t| := by simp [abs_of_nonneg (le_of_lt hσpos)]
      _ ≤ 2 + |t| := by linarith
  have hcoef : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ ≤ 4 * (2 + Real.exp (1000 / cvk ^ 6)) := by
    have h1 : 1 / σ ≤ 2 := by rw [div_le_iff₀ hσpos]; linarith
    have h2 : 2 + |t| ≤ 2 + Real.exp (1000 / cvk ^ 6) := by linarith [le_of_lt ht]
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ
        = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ * (1 / σ) := by ring
      _ ≤ (2 + |t|) * 2 := mul_le_mul hsnorm h1 (by positivity) (by positivity)
      _ ≤ (2 + Real.exp (1000 / cvk ^ 6)) * 2 := mul_le_mul_of_nonneg_right h2 (by norm_num)
      _ ≤ 4 * (2 + Real.exp (1000 / cvk ^ 6)) := by linarith [Real.exp_pos (1000 / cvk ^ 6)]
  have hann : 0 ≤ a ^ (-σ) := Real.rpow_nonneg ha.le _
  have hL6 : 0 ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) _
  refine le_trans htail' ?_
  calc (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ) * a ^ (-σ)
      ≤ (4 * (2 + Real.exp (1000 / cvk ^ 6))) * a ^ (-σ) :=
        mul_le_mul_of_nonneg_right hcoef hann
    _ ≤ (4 * (2 + Real.exp (1000 / cvk ^ 6))) *
          (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The gated shift-difference series bound.** -/
lemma shift_series_gated {Cvk cvk : ℝ} (hVK : VKExpInput Cvk cvk) (hcvk0 : 0 < cvk)
    (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) :
    ∃ As : ℝ, 0 < As ∧ ∀ (a σ t : ℝ), 0 < a → a ≤ 1 → 3 ≤ |t| →
      Real.exp (1000 / cvk ^ 6) ≤ |t| →
      1 - (cvk / 4) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖∑' m : ℕ, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        As * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨Ab, hAb0, hAbound⟩ := Work.BMF.VKChain.block_sum_uniform cvk hcvk0 hcvk1
  obtain ⟨Akl, hAkl0, hAkl⟩ := v7chi_kl_range_arith
  obtain ⟨At, hAt0, hAt⟩ := v7chi_tail_arith
  obtain ⟨Bhd, hBhd0, hBhd⟩ := v7chi_head_arith hcvk0 hcvk1
  set Bvk : ℝ := 2 * Cvk * Real.exp (1 / 2) * Ab with hBvkdef
  have hBvk0 : 0 < Bvk := by rw [hBvkdef]; positivity
  refine ⟨Bhd + 2 + Bvk + Akl + At, by linarith, ?_⟩
  intro a σ t ha ha1 ht hgate hσlo hσ2
  set L : ℝ := Real.log (|t| + 3) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    linarith [Real.exp_one_lt_three, abs_nonneg t]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLgate : 1000 / cvk ^ 6 ≤ L := by
    have h : Real.log (Real.exp (1000 / cvk ^ 6)) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (Real.exp_pos _) (by linarith)
    rw [Real.log_exp] at h
    rw [hLdef]; exact h
  have hcvk6pos : (0 : ℝ) < cvk ^ 6 := by positivity
  have hLcvk : cvk ≤ L := by
    have h2 : cvk ^ 7 ≤ 1000 := le_trans (pow_le_pow_left₀ hcvk0.le hcvk1 7) (by norm_num)
    have h3 : cvk * cvk ^ 6 = cvk ^ 7 := by ring
    have h4 : cvk ≤ 1000 / cvk ^ 6 := by
      rw [le_div_iff₀ hcvk6pos, h3]; exact h2
    linarith [hLgate, h4]
  have hcl : (cvk / 4) * L ^ (-(6 / 7 : ℝ)) ≤ 1 / 4 := by
    have h2 : L ^ (-(6 / 7 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    have h3 : cvk / 4 ≤ 1 / 4 := by linarith
    nlinarith [h2, Real.rpow_nonneg hLpos.le (-(6 / 7 : ℝ)), hcvk0, h3]
  have hσpos : 0 < σ := by linarith
  have hσ34 : 3 / 4 ≤ σ := by linarith
  have hσ12 : 1 / 2 ≤ σ := by linarith
  have hL67pos : 0 < L ^ (6 / 7 : ℝ) := Real.rpow_pos_of_pos hLpos (6 / 7 : ℝ)
  have hcvk17 : cvk ^ (1 / 7 : ℝ) ≤ 2 :=
    le_trans (Real.rpow_le_one hcvk0.le hcvk1 (by norm_num)) (by norm_num)
  have hcvk17b : cvk ^ (1 / 7 : ℝ) ≤ 1 := Real.rpow_le_one hcvk0.le hcvk1 (by norm_num)
  set κ : ℝ := (L / cvk) ^ (6 / 7 : ℝ) with hκdef
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg (by positivity) (6 / 7 : ℝ)
  have hκex : κ = L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ)) := by
    rw [hκdef, Real.div_rpow hLpos.le hcvk0.le, div_eq_mul_inv, ← Real.rpow_neg hcvk0.le]
  have hκ1 : 1 ≤ κ := by
    rw [hκdef]
    exact Real.one_le_rpow ((le_div_iff₀ hcvk0).mpr (by linarith [hLcvk])) (by norm_num)
  have hκcvk : κ ≤ cvk ^ (-(6 / 7 : ℝ)) * L ^ (6 / 7 : ℝ) := by
    rw [hκex, mul_comm]
  have hLmulκ : L ^ (-(6 / 7 : ℝ)) * κ = cvk ^ (-(6 / 7 : ℝ)) := by
    rw [hκex, ← mul_assoc, ← Real.rpow_add hLpos]
    have h : L ^ (-(6 / 7 : ℝ) + 6 / 7 : ℝ) = 1 := by
      rw [show -(6 / 7 : ℝ) + 6 / 7 = 0 by norm_num, Real.rpow_zero]
    rw [h, one_mul]
  have hκle : κ ≤ L / 2 := by
    have h1 : 2 * cvk ^ (-(6 / 7 : ℝ)) ≤ L ^ (1 / 7 : ℝ) := by
      have h2 : (1000 / cvk ^ 6) ^ (1 / 7 : ℝ) ≤ L ^ (1 / 7 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hLgate (by norm_num)
      have h3 : (1000 / cvk ^ 6) ^ (1 / 7 : ℝ)
          = 1000 ^ (1 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ)) := by
        rw [Real.div_rpow (by norm_num) hcvk6pos.le]
        have hb : (cvk ^ 6 : ℝ) ^ (1 / 7 : ℝ) = cvk ^ (6 / 7 : ℝ) := by
          rw [← Real.rpow_natCast cvk 6, ← Real.rpow_mul hcvk0.le]; norm_num
        rw [hb, div_eq_mul_inv, ← Real.rpow_neg hcvk0.le]
      have h4 : (2 : ℝ) ≤ 1000 ^ (1 / 7 : ℝ) := by
        have h5 : ((2 : ℝ) ^ 7) ^ (1 / 7 : ℝ) ≤ 1000 ^ (1 / 7 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
        have h6 : ((2 : ℝ) ^ 7) ^ (1 / 7 : ℝ) = 2 := by
          rw [← Real.rpow_natCast (2 : ℝ) 7, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        linarith [h5, h6]
      have h4b : 2 * cvk ^ (-(6 / 7 : ℝ)) ≤ 1000 ^ (1 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ)) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hcvk0.le (-(6 / 7 : ℝ)))
      linarith [h2, h3, h4b]
    have h7 : cvk ^ (-(6 / 7 : ℝ)) ≤ L ^ (1 / 7 : ℝ) / 2 := by linarith
    have h8 : L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ)) ≤ L ^ (6 / 7 : ℝ) * (L ^ (1 / 7 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left h7 (Real.rpow_nonneg hLpos.le (6 / 7 : ℝ))
    have h9 : L ^ (6 / 7 : ℝ) * (L ^ (1 / 7 : ℝ) / 2) = L / 2 := by
      rw [← mul_div_assoc, ← Real.rpow_add hLpos]
      norm_num
    rw [hκex]; linarith
  set K₀ : ℕ := Nat.ceil (Real.exp κ) with hK₀def
  have hK₀lo : Real.exp κ ≤ (K₀ : ℝ) := Nat.le_ceil _
  have hK₀hi : (K₀ : ℝ) < Real.exp κ + 1 := Nat.ceil_lt_add_one (Real.exp_pos κ).le
  have hK₀log : κ ≤ Real.log (K₀ : ℝ) := by
    rw [← Real.log_exp κ]; exact Real.log_le_log (Real.exp_pos κ) hK₀lo
  have hK₀2 : 2 ≤ K₀ := by
    have h1 : (2 : ℝ) < (K₀ : ℝ) := lt_of_lt_of_le (by
      have h2 : Real.exp 1 ≤ Real.exp κ := Real.exp_le_exp.mpr hκ1
      have h3 : (2 : ℝ) < Real.exp 1 := by
        rw [← Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
        linarith [Real.log_two_lt_d9]
      linarith) hK₀lo
    have h1' : (2 : ℕ) < K₀ := by exact_mod_cast h1
    omega
  have hK₀2R : (2 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀2
  have hK₀1R : (1 : ℝ) ≤ (((K₀ + 1 : ℕ)) : ℝ) := by push_cast; linarith [hK₀2R]
  have hK₀leExp : (K₀ : ℝ) ≤ Real.exp κ + 2 := by linarith
  set Nt : ℕ := Nat.ceil |t| with hNtdef
  have hNtge : |t| ≤ (Nt : ℝ) := Nat.le_ceil _
  have hNtlt : (Nt : ℝ) < |t| + 1 := Nat.ceil_lt_add_one (abs_nonneg t)
  have hNt1 : 1 ≤ Nt := by
    have h : (1 : ℝ) ≤ (Nt : ℝ) := by linarith
    exact_mod_cast h
  have hK₀Nt : K₀ ≤ Nt := by
    have hexp : Real.exp κ ≤ Real.sqrt (|t| + 3) := by
      calc Real.exp κ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hκle
        _ = Real.sqrt (Real.exp L) := Real.exp_half L
        _ = Real.sqrt (|t| + 3) := by rw [hLdef, Real.exp_log (by linarith [abs_nonneg t])]
    have hsqrt : Real.sqrt (|t| + 3) ≤ |t| := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith [abs_nonneg t], by nlinarith [ht]⟩
    have h1 : (K₀ : ℝ) < |t| + 1 := lt_of_lt_of_le hK₀hi (by linarith)
    by_contra hcon
    push_neg at hcon
    have h2 : (Nt : ℝ) + 1 ≤ (K₀ : ℝ) := by exact_mod_cast hcon
    linarith [hNtge]
  set M : ℕ := Nt * Nt + 1 with hMdef
  have hMge : (|t| : ℝ) * |t| ≤ (M : ℝ) := by
    have h2 : |t| * |t| ≤ (Nt : ℝ) * Nt := mul_self_le_mul_self (abs_nonneg t) hNtge
    have h3 : ((M : ℕ) : ℝ) = (Nt : ℝ) * Nt + 1 := by rw [hMdef]; push_cast; ring
    rw [h3]; linarith
  have hNtM : Nt ≤ M := by
    rw [hMdef]
    calc Nt = Nt * 1 := (mul_one Nt).symm
      _ ≤ Nt * Nt := Nat.mul_le_mul_left Nt hNt1
      _ ≤ Nt * Nt + 1 := Nat.le_succ _
  set X : ℝ := a ^ (-σ) + L ^ (6 / 7 : ℝ) with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    have h1 : 1 ≤ a ^ (-σ) := by
      rw [Real.rpow_neg ha.le]
      exact (one_le_inv₀ (Real.rpow_pos_of_pos ha σ)).mpr
        (Real.rpow_le_one ha.le ha1 hσpos.le)
    have h2 : 1 ≤ L ^ (6 / 7 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    linarith
  have hsre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  have hs0 : 0 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by rw [hsre]; exact hσpos
  have hsplit := shiftTerm_split ha ha1 hs0 (M + 1)
  have hd1 : Disjoint (Finset.range K₀) ({K₀} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_range, Finset.mem_singleton] at hx1 hx2
    omega
  have hd2 : Disjoint (Finset.range K₀ ∪ ({K₀} : Finset ℕ)) (Finset.Ioc K₀ Nt) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ioc] at hx1 hx2
    omega
  have hd3 : Disjoint ((Finset.range K₀ ∪ ({K₀} : Finset ℕ)) ∪ Finset.Ioc K₀ Nt)
      (Finset.Ioc Nt M) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ioc] at hx1 hx2
    omega
  have hsumdec : (∑ m ∈ Finset.range (M + 1), shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
      = (∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
        + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)
        + (∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
        + (∑ m ∈ Finset.Ioc Nt M, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hset : Finset.range (M + 1) =
        Finset.range K₀ ∪ {K₀} ∪ Finset.Ioc K₀ Nt ∪ Finset.Ioc Nt M := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioc]
      omega
    rw [hset, Finset.sum_union hd3, Finset.sum_union hd2, Finset.sum_union hd1,
      Finset.sum_singleton]
  have hHead : ‖∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Bhd * X := by
    refine le_trans (Work.BMF.VKChain.shift_head_bound (K₀ := K₀) (a := a) (σ := σ) (t := t)
      (κ := κ) ha hσpos hσ2 hκ0 ?_ hK₀leExp) ?_
    · have h1 : (1 - σ) * κ = (1 - σ) * (L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ))) := by
        rw [hκex]
      have h2 : L ^ (-(6 / 7 : ℝ)) * L ^ (6 / 7 : ℝ) = 1 := by
        rw [← Real.rpow_add hLpos]; norm_num
      have h3 : (cvk / 4) * cvk ^ (-(6 / 7 : ℝ)) ≤ 1 / 4 := by
        have h4 : cvk * cvk ^ (-(6 / 7 : ℝ)) = cvk ^ (1 / 7 : ℝ) := by
          have h5 : (1 : ℝ) + (-(6 / 7 : ℝ)) = 1 / 7 := by norm_num
          calc cvk * cvk ^ (-(6 / 7 : ℝ)) = cvk ^ (1 : ℝ) * cvk ^ (-(6 / 7 : ℝ)) := by
                rw [Real.rpow_one]
            _ = cvk ^ (1 + -(6 / 7 : ℝ)) := (Real.rpow_add hcvk0 1 (-(6 / 7 : ℝ))).symm
            _ = cvk ^ (1 / 7 : ℝ) := by rw [h5]
        have h4b : (cvk / 4) * cvk ^ (-(6 / 7 : ℝ)) = (1 / 4) * (cvk * cvk ^ (-(6 / 7 : ℝ))) := by
          ring
        rw [h4b, h4]
        linarith [hcvk17b]
      have h7 : (1 - σ) * (L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ)))
          ≤ ((cvk / 4) * L ^ (-(6 / 7 : ℝ))) * (L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (Real.rpow_nonneg hLpos.le (6 / 7 : ℝ))
            (Real.rpow_nonneg hcvk0.le (-(6 / 7 : ℝ))))
        linarith [hσlo]
      have h8 : ((cvk / 4) * L ^ (-(6 / 7 : ℝ))) * (L ^ (6 / 7 : ℝ) * cvk ^ (-(6 / 7 : ℝ)))
          = (cvk / 4) * (L ^ (-(6 / 7 : ℝ)) * L ^ (6 / 7 : ℝ)) * cvk ^ (-(6 / 7 : ℝ)) := by
        ring
      rw [h8, h2] at h7
      rw [h1]
      linarith [h7, h3]
    · exact hBhd a σ L κ ha ha1 hσpos hL1 hκ0 hκcvk
  have hSing : ‖shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * X := by
    have h0 : ‖shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 := by
      rw [shiftTerm]
      refine le_trans (norm_sub_le _ _) ?_
      have h1 : ‖((((K₀ : ℝ) + a : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (K₀ : ℝ) + a)]
        have h4 : (((K₀ : ℝ) + a)) ^ (-σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hK₀2R]) (by linarith)
        simpa using h4
      have h2 : ‖((((K₀ + 1 : ℕ)) : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos
          (by positivity : (0 : ℝ) < (((K₀ + 1 : ℕ)) : ℝ))]
        have h4 : ((((K₀ + 1 : ℕ)) : ℝ)) ^ (-σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hK₀1R]) (by linarith)
        simpa using h4
      linarith
    nlinarith [hX1, h0]
  have hVKbd : ‖∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Bvk * X := by
    have h2 : cvk / 4 ≤ cvk ^ (6 / 7 : ℝ) / 2 := by
      have h13 : cvk ^ (1 / 7 : ℝ) * cvk ^ (6 / 7 : ℝ) = cvk := by
        rw [← Real.rpow_add hcvk0]; norm_num
      have h12 : cvk ≤ 2 * cvk ^ (6 / 7 : ℝ) := by
        calc cvk = cvk ^ (1 / 7 : ℝ) * cvk ^ (6 / 7 : ℝ) := h13.symm
          _ ≤ 2 * cvk ^ (6 / 7 : ℝ) :=
              mul_le_mul_of_nonneg_right hcvk17 (Real.rpow_nonneg hcvk0.le (6 / 7 : ℝ))
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have h14 : (cvk ^ (6 / 7 : ℝ) / 2) * 4 = 2 * cvk ^ (6 / 7 : ℝ) := by ring
      rw [h14]; exact h12
    refine le_trans (Work.BMF.VKChain.shift_vk_range_bound hVK hcvk0 hcvk1 ha ha1 ht hσpos
      hσ2 ?_ hK₀2 (le_of_lt hNtlt) hK₀Nt hK₀log (hAbound L hL1)) ?_
    · calc 1 - σ ≤ (cvk / 4) * L ^ (-(6 / 7 : ℝ)) := by linarith [hσlo]
        _ ≤ (cvk ^ (6 / 7 : ℝ) / 2) * L ^ (-(6 / 7 : ℝ)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLpos.le (-(6 / 7 : ℝ)))
    · rw [hBvkdef]; exact le_mul_of_one_le_right hBvk0.le hX1
  have hKL : ‖∑ m ∈ Finset.Ioc Nt M, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Akl * X := by
    refine le_trans (Work.BMF.VKChain.shiftTerm_kl_range_le
      (hkl := fun {u σ t} hu hu1 hσ ht =>
        fun {K R} hRK hR2K htK => Work.BMF.VKChain.kl_tail_block_bound hu hu1 hσ ht hRK hR2K htK)
      ha ha1 hσpos ht (by linarith [hσ34]) hNtge hNt1 hNtM) ?_
    refine le_trans (hAkl t ht) ?_
    exact le_mul_of_one_le_right hAkl0.le hX1
  have hTail : ‖∑' m : ℕ, shiftTerm a ((M + 1) + m) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ At * X := by
    refine le_trans (shiftTerm_tail_le (a := a) (σ := σ) (t := t) ha ha1 hσpos (M + 1)) ?_
    have h3 : (((M + 1 : ℕ) : ℝ) + a) ^ (-σ) ≤ (((M + 1 : ℕ) : ℝ)) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [ha.le]) (by linarith)
    have h4 : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ * (((M + 1 : ℕ) : ℝ)) ^ (-σ) ≤ At :=
      hAt σ t ht hσ12
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ * (((M + 1 : ℕ) : ℝ) + a) ^ (-σ)
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ / σ * (((M + 1 : ℕ) : ℝ)) ^ (-σ) :=
          mul_le_mul_of_nonneg_left h3 (div_nonneg (norm_nonneg _) hσpos.le)
      _ ≤ At := h4
      _ ≤ At * X := le_mul_of_one_le_right hAt0.le hX1
  have hfin : ‖∑ m ∈ Finset.range (M + 1), shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Bhd + 2 + Bvk + Akl) * X := by
    rw [hsumdec]
    set S1 : ℝ := ‖∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ with hS1
    set S2 : ℝ := ‖shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ with hS2
    set S3 : ℝ := ‖∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ with hS3
    have h1 : S1 ≤ Bhd * X := hS1 ▸ hHead
    have h2 : S2 ≤ 2 * X := hS2 ▸ hSing
    have h3 : S3 ≤ Bvk * X := hS3 ▸ hVKbd
    have h5 := norm_add_le ((∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
      + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I))
      (∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
    have h6 := norm_add_le (∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
      (shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I))
    calc ‖((∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
            + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I))
            + ∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)
            + ∑ m ∈ Finset.Ioc Nt M, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ‖((∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
            + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I))
            + ∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          + ‖∑ m ∈ Finset.Ioc Nt M, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
          norm_add_le _ _
      _ ≤ ((Bhd * X + 2 * X) + Bvk * X) + Akl * X := by
          have hinner : ‖((∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
              + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I))
              + ∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              ≤ (Bhd * X + 2 * X) + Bvk * X := by
            have h7 : ‖((∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
                + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I))
                + ∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ ‖(∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
                    + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
                  + ‖∑ m ∈ Finset.Ioc K₀ Nt, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
                norm_add_le _ _
            have h8 : ‖(∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
                    + shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
                ≤ ‖∑ m ∈ Finset.range K₀, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
                  + ‖shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
                norm_add_le _ _
            linarith [h7, h8, hHead, hSing, hVKbd]
          have h7 : ‖∑ m ∈ Finset.Ioc Nt M, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              ≤ Akl * X := hKL
          linarith [hinner, h7]
      _ = (Bhd + 2 + Bvk + Akl) * X := by ring
  rw [hsplit]
  calc ‖(∑ m ∈ Finset.range (M + 1), shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
        + ∑' m : ℕ, shiftTerm a ((M + 1) + m) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ‖∑ m ∈ Finset.range (M + 1), shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        + ‖∑' m : ℕ, shiftTerm a ((M + 1) + m) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ (Bhd + 2 + Bvk + Akl) * X + At * X := add_le_add hfin hTail
    _ = (Bhd + 2 + Bvk + Akl + At) * X := by ring

/-- **The shift-difference series in the VK strip.** -/
lemma shift_series_bound {Cvk cvk : ℝ} (hVK : VKExpInput Cvk cvk) (hcvk0 : 0 < cvk)
    (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) :
    ∃ As : ℝ, 0 < As ∧ ∀ (a σ t : ℝ), 0 < a → a ≤ 1 → 3 ≤ |t| →
      1 - (cvk / 4) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖∑' m : ℕ, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        As * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨As1, hAs1, h1⟩ := shift_series_gated hVK hcvk0 hcvk1 hCvk
  refine ⟨max As1 (4 * (2 + Real.exp (1000 / cvk ^ 6))), by positivity, ?_⟩
  intro a σ t ha ha1 ht hσlo hσ2
  have hXnn : 0 ≤ a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
    have h2 : 0 ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) (6 / 7 : ℝ)
    have := Real.rpow_nonneg ha.le (-σ)
    linarith
  rcases le_or_gt (Real.exp (1000 / cvk ^ 6)) |t| with hgate | hlt
  · exact le_trans (h1 a σ t ha ha1 ht hgate hσlo hσ2)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn)
  · have hσ12 : 1 / 2 ≤ σ := by
      have hL1 : 1 ≤ Real.log (|t| + 3) := by
        rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
        linarith [Real.exp_one_lt_three, abs_nonneg t]
      have h2 : Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have h3 : (cvk / 4) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ 1 / 4 := by
        nlinarith [h2, Real.rpow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) (6 / 7 : ℝ), hcvk0, hcvk1]
      linarith
    exact le_trans (shift_series_small ha ha1 hσ12 hσ2 hlt)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hXnn)

/-- **The Hurwitz-zeta growth bound in the VK strip.** -/
lemma hurwitz_growth_v7 {Cvk cvk : ℝ} (hVK : VKExpInput Cvk cvk) (hcvk0 : 0 < cvk)
    (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1 / 4 ∧
      ∀ (a σ t : ℝ), 0 ≤ a → a ≤ 1 → 3 ≤ |t| →
        1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨Az, cz, hAz, hcz0, hcz4, hzeta⟩ := zeta_growth_v7 hVK
  obtain ⟨As, hAs0, hshift⟩ := shift_series_bound hVK hcvk0 hcvk1 hCvk
  set c₀ : ℝ := min (min cz (cvk / 4)) (1 / 4) with hc₀def
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; exact lt_min (lt_min hcz0 (by positivity)) (by norm_num)
  have hc₀4 : c₀ ≤ 1 / 4 := by rw [hc₀def]; exact min_le_right _ _
  have hc₀z : c₀ ≤ cz := by rw [hc₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₀c : c₀ ≤ cvk / 4 := by rw [hc₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  refine ⟨Az + As + 4 * (2 + Real.exp (1000 / cvk ^ 6)) + 1, c₀,
    by nlinarith [hAz, hAs0, Real.exp_pos (1000 / cvk ^ 6)],
    hc₀0, hc₀4, ?_⟩
  intro a σ t ha0 ha1 ht hσ hσ2
  set L : ℝ := Real.log (|t| + 3) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    linarith [Real.exp_one_lt_three, abs_nonneg t]
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hLn67 : 0 ≤ L ^ (-(6 / 7 : ℝ)) := Real.rpow_nonneg hLnn _
  have hL67 : 0 ≤ L ^ (6 / 7 : ℝ) := Real.rpow_nonneg hLnn _
  have hLm67 : c₀ * L ^ (-(6 / 7 : ℝ)) ≤ 1 / 4 := by
    have h2 : L ^ (-(6 / 7 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    nlinarith [h2, hLn67, hc₀0, hc₀4]
  have hσ34 : 3 / 4 ≤ σ := by linarith
  have hσpos : 0 < σ := by linarith
  have hσz : 1 - cz * L ^ (-(6 / 7 : ℝ)) ≤ σ := by
    have h1 := mul_le_mul_of_nonneg_right hc₀z hLn67
    linarith [hσ, h1]
  have hσc : 1 - (cvk / 4) * L ^ (-(6 / 7 : ℝ)) ≤ σ := by
    have h1 := mul_le_mul_of_nonneg_right hc₀c hLn67
    linarith [hσ, h1]
  have hζ : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Az * L ^ (6 / 7 : ℝ) := by
    have h := hzeta σ t ht (by rw [← hLdef]; exact hσz) hσ2
    rwa [← hLdef] at h
  rcases eq_or_lt_of_le ha0 with ha_eq | ha_pos
  · have h0eq : ((0 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_zero 1
    rw [← ha_eq, h0eq, HurwitzZeta.hurwitzZeta_zero,
      Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
    refine le_trans hζ ?_
    nlinarith [hAs0, hL67, Real.exp_pos (1000 / cvk ^ 6)]
  · have hs0 : 0 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
      have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
      rw [hre]; exact hσpos
    have hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
      intro hcon
      have him : t = 0 := by
        have := congrArg Complex.im hcon
        simpa using this
      have : |t| = 0 := by rw [him]; simp
      linarith
    have hdec := hurwitzZeta_sub_riemannZeta_eq_tsum ha_pos ha1 hs0 hs1
    rw [sub_eq_iff_eq_add] at hdec
    rw [hdec]
    refine le_trans (norm_add_le _ _) ?_
    have hann : 0 ≤ a ^ (-σ) := Real.rpow_nonneg ha_pos.le _
    have hXnn : 0 ≤ a ^ (-σ) + L ^ (6 / 7 : ℝ) := by linarith
    have hζ' : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Az * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
      refine le_trans hζ ?_
      nlinarith [hAz, hann, hL67]
    have hs := hshift a σ t ha_pos ha1 ht hσc hσ2
    rw [← hLdef] at hs
    calc ‖∑' m : ℕ, shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ As * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) + Az * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) :=
          add_le_add hs hζ'
      _ ≤ (Az + As + 4 * (2 + Real.exp (1000 / cvk ^ 6)) + 1) * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
          nlinarith [hAz, hAs0, hXnn, Real.exp_pos (1000 / cvk ^ 6)]

/-- **The Vinogradov–Korobov growth bound for `L(s,χ)` (node V2).**

There are `A, c > 0` with `‖L(σ+it,χ)‖ ≤ A N (log(|t|+3))^{6/7}` for every character `χ` mod `N`,
every `3 ≤ |t|`, `σ ≤ 2` and `σ ≥ 1 − c (log(|t|+3))^{-6/7}` (this is `Work.BMF.VKGrowth A c`).

Available cleanly in the workspace:
* V1 (`VKExpSumRestrictedN7`) as `Work.BMF.vk_exp_sum`;
* the ζ-growth in the VK region as `Work.BMF.N7.zeta_strip_bound_of_vk_aux` (in
  `Submission/Work/BMF/N7/V2_zeta_strip.lean`);
* the Hurwitz-shift identity `Work.BMF.hurwitzZeta_sub_riemannZeta_eq_tsum`;
* the shift-difference block bounds `Work.BMF.VKChain.shiftTerm_kl_range_le`,
  `shiftTerm_head_norm_sum`, `head_rpow_sum_bound`, `kl_tail_block_bound`;
* `Work.BMF.LFunction_growth_of_hurwitz` (in `Submission/Work/BMF/VKGrowth.lean`), which converts a
  Hurwitz growth bound `‖hurwitzZeta a (σ+it)‖ ≤ Ah (a^{-σ} + (log(|t|+3))^{6/7})` in the same
  region into the statement below.

A direct alternative for the `χ ≠ 1` case: split `Σ_{n≤M} χ(n) n^{-it}` into residue classes mod
`N`, giving shifted VK sums `Σ_m (m + a/N)^{-it}` to which V1 applies verbatim. -/
theorem v7chi_VKGrowth : ∃ A c : ℝ, VKGrowth A c := by
  obtain ⟨Cvk, cvk, hCvk, hcvk0, hbody⟩ := vk_exp_sum
  have hVK0 : VKExpInput Cvk cvk := ⟨hCvk, hcvk0, hbody⟩
  have hcvkm0 : 0 < min cvk 1 := lt_min hcvk0 zero_lt_one
  have hcvkm1 : min cvk 1 ≤ 1 := min_le_right _ _
  have hVK : VKExpInput Cvk (min cvk 1) :=
    VKExpInput_mono hVK0 hcvkm0 (min_le_left _ _)
  obtain ⟨Ah, ch, hAh, hch, hch4, hHur⟩ := hurwitz_growth_v7 hVK hcvkm0 hcvkm1 hCvk
  exact ⟨2 * Ah, ch, by positivity, hch,
    LFunction_growth_of_hurwitz hAh hch (by linarith) hHur⟩

end

end Work.BMF
