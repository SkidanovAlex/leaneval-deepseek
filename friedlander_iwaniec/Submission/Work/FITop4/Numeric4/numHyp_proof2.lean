import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Numeric4.log_dominance

set_option maxHeartbeats 4000000

namespace Work.FITop4.Numeric4

open Filter
open scoped Topology

/-! ## rpow utilities -/

lemma rpow_natpow {a : ℝ} (ha : 0 ≤ a) (r : ℝ) (n : ℕ) : (a ^ r) ^ n = a ^ (r * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]

lemma rpow_half_sq (a : ℝ) (ha : 0 ≤ a) : (a ^ ((1:ℝ)/2)) ^ (2:ℕ) = a := by
  rw [rpow_natpow ha (1/2) 2, show (1/2) * ((2:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]

lemma rpow_sixteen_half : (16:ℝ) ^ ((1:ℝ)/2) = 4 := by
  rw [show (16:ℝ) = 4^(2:ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4),
      show (((2:ℕ):ℝ) * (1/2)) = 1 by norm_num, Real.rpow_one]

lemma rpow_eighth_pow (a : ℝ) (ha : 0 ≤ a) : ((a)^((1:ℝ)/8))^(8:ℕ) = a := by
  rw [rpow_natpow ha (1/8) 8, show (1:ℝ)/8*((8:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]

/-! ## Eventual lemmas -/

lemma ev_log_pow_le_rpow (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, (Real.log (x:ℝ))^C ≤ (x:ℝ)^δ :=
  eventually_atTop.2 (log_dominance.1 C δ hC hδ)

lemma ev_log_pow_le_exp_logsq (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x:ℝ))^C ≤ Real.exp ((Real.log (Real.log (x:ℝ)))^2) :=
  eventually_atTop.2 (log_dominance.2.1 C hC)

lemma ev_const_le_log (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ x : ℕ in atTop, D ≤ Real.log (x:ℝ) :=
  eventually_atTop.2 (log_dominance.2.2.2.1 D hD)

lemma ev_const_le_loglog (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ x : ℕ in atTop, D ≤ Real.log (Real.log (x:ℝ)) :=
  eventually_atTop.2 (log_dominance.2.2.2.2 D hD)

lemma ev_const_le_rpow (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, c ≤ (x:ℝ)^δ :=
  tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop c))

lemma ev_const_le_log_pow (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ x : ℕ in atTop, c ≤ (Real.log (x:ℝ))^C := by
  have hD : ∀ᶠ x : ℕ in atTop,
      max 0 (Real.log c / C) ≤ Real.log (Real.log (x:ℝ)) :=
    ev_const_le_loglog _ (le_max_left _ _)
  filter_upwards [hD, ev_const_le_log 1 zero_le_one] with x hDx hx1
  have hLx : 0 < Real.log (x:ℝ) := lt_of_lt_of_le one_pos hx1
  have hllx : 0 ≤ Real.log (Real.log (x:ℝ)) := Real.log_nonneg hx1
  rw [Real.rpow_def_of_pos hLx, ← Real.exp_log hc]
  apply Real.exp_le_exp.mpr
  by_cases h : Real.log c ≤ 0
  · have : Real.log c ≤ C * Real.log (Real.log (x:ℝ)) :=
      le_trans h (mul_nonneg (le_of_lt hC) hllx)
    linarith
  · push_neg at h
    have h2 : Real.log c / C ≤ Real.log (Real.log (x:ℝ)) := by
      rw [max_eq_right (by positivity)] at hDx; exact hDx
    rw [div_le_iff₀ (by linarith)] at h2
    linarith

lemma ev_const_log_pow_mul_rpow_neg_le (c C δ : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, c * (Real.log (x:ℝ))^C * (x:ℝ)^(-δ) ≤ 1 := by
  have hx1 : ∀ᶠ x : ℕ in atTop, (1:ℝ) ≤ (x:ℝ) :=
    eventually_atTop.2 ⟨1, fun b hb => by exact_mod_cast hb⟩
  filter_upwards [ev_log_pow_le_rpow C (δ/2) hC (by positivity),
      ev_const_le_rpow c (δ/2) hc (by positivity), hx1] with x h1 h2 hx1
  have hxpos : (0:ℝ) < (x:ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hxnn : (0:ℝ) ≤ (x:ℝ) := le_of_lt hxpos
  have hLxnn : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_natCast_nonneg x
  have hstep : c * (Real.log (x:ℝ))^C ≤ (x:ℝ)^(δ/2) * (x:ℝ)^(δ/2) :=
    mul_le_mul h2 h1 (Real.rpow_nonneg hLxnn C) (Real.rpow_nonneg hxnn (δ/2))
  have hmul : (x:ℝ)^(δ/2) * (x:ℝ)^(δ/2) = (x:ℝ)^δ := by
    rw [← Real.rpow_add hxpos, show δ/2 + δ/2 = δ by ring]
  have hlast : (x:ℝ)^δ * (x:ℝ)^(-δ) = 1 := by
    rw [← Real.rpow_add hxpos, show δ + -δ = 0 by ring, Real.rpow_zero]
  calc c * (Real.log (x:ℝ))^C * (x:ℝ)^(-δ)
      = (c * (Real.log (x:ℝ))^C) * (x:ℝ)^(-δ) := by ring
    _ ≤ ((x:ℝ)^(δ/2) * (x:ℝ)^(δ/2)) * (x:ℝ)^(-δ) :=
        mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hxnn (-δ))
    _ = (x:ℝ)^δ * (x:ℝ)^(-δ) := by rw [hmul]
    _ = 1 := hlast

lemma ev_const_log_pow_mul_exp_neg_loglog_sq_le (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ x : ℕ in atTop,
      c * (Real.log (x:ℝ))^C * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) ≤ 1 := by
  have hx1 : ∀ᶠ x : ℕ in atTop, (1:ℝ) ≤ (x:ℝ) :=
    eventually_atTop.2 ⟨1, fun b hb => by exact_mod_cast hb⟩
  filter_upwards [ev_log_pow_le_exp_logsq (C+1) (by linarith),
      ev_const_le_log_pow c 1 hc one_pos, hx1] with x h1 h2 hx1
  have hcx : c ≤ Real.log (x:ℝ) := by simpa using h2
  have hLxpos : 0 < Real.log (x:ℝ) := lt_of_lt_of_le hc hcx
  have hLxnn : (0:ℝ) ≤ Real.log (x:ℝ) := le_of_lt hLxpos
  have hstep : c * (Real.log (x:ℝ))^C ≤ (Real.log (x:ℝ))^(C+1) := by
    calc c * (Real.log (x:ℝ))^C ≤ (Real.log (x:ℝ)) * (Real.log (x:ℝ))^C :=
          mul_le_mul_of_nonneg_right hcx (Real.rpow_nonneg hLxnn C)
      _ = (Real.log (x:ℝ))^(1 + C) := by
          rw [show (Real.log (x:ℝ))*(Real.log (x:ℝ))^C
              = (Real.log (x:ℝ))^(1:ℝ)*(Real.log (x:ℝ))^C by rw [Real.rpow_one],
              ← Real.rpow_add hLxpos]
      _ = (Real.log (x:ℝ))^(C + 1) := by
          rw [show (1:ℝ) + C = C + 1 by ring]
  have hExp : Real.exp ((Real.log (Real.log (x:ℝ)))^2)
        * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) = 1 := by
    rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  calc c * (Real.log (x:ℝ))^C * Real.exp (-(Real.log (Real.log (x:ℝ)))^2)
      ≤ Real.exp ((Real.log (Real.log (x:ℝ)))^2)
          * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) :=
        mul_le_mul_of_nonneg_right (le_trans hstep h1) (Real.exp_nonneg _)
    _ = 1 := hExp

/-! ## The threshold on `x` -/

lemma numHyp_threshold (η c1 Cb C3 : ℝ) (hη : 0 < η) (hc1 : 0 < c1) (hCb : 0 < Cb)
    (hC3 : 0 < C3) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (1 ≤ (x:ℝ)) ∧ (4 ≤ Real.log (x:ℝ)) ∧
      ((Real.log (x:ℝ))^Astar ≤ (x:ℝ)^((1:ℝ)/4)) ∧
      (16*C3 ≤ ((3/4) * Real.log (x:ℝ))^8) ∧
      (32*Cb * (Real.log (x:ℝ))^(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30) ≤ 1) ∧
      (8*c1 * (Real.log (x:ℝ))^(2*Astar + 6*Aprime Astar + 516) * (x:ℝ)^(-η) ≤ 1) ∧
      (8*c1 * (Real.log (x:ℝ))^(2*Astar + 6*Aprime Astar + 516)
          * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) ≤ 1) ∧
      (16 * (Real.log (x:ℝ))^(2*Astar + 4*Aprime Astar + 1)
          * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) ≤ 1) := by
  have hx1 : ∀ᶠ x : ℕ in atTop, (1:ℝ) ≤ (x:ℝ) :=
    eventually_atTop.2 ⟨1, fun b hb => by exact_mod_cast hb⟩
  have hL4 : ∀ᶠ x : ℕ in atTop, (4:ℝ) ≤ Real.log (x:ℝ) := ev_const_le_log 4 (by norm_num)
  have hLA : ∀ᶠ x : ℕ in atTop, (Real.log (x:ℝ))^Astar ≤ (x:ℝ)^((1:ℝ)/4) :=
    ev_log_pow_le_rpow Astar (1/4) (by norm_num [Astar]) (by norm_num)
  have hpow8 : ∀ᶠ x : ℕ in atTop, (16:ℝ)*C3 ≤ ((3/4) * Real.log (x:ℝ))^8 := by
    have h0 : (0:ℝ) ≤ 16*C3 := by positivity
    have hC8nn : (0:ℝ) ≤ ((16*C3))^((1:ℝ)/8) := Real.rpow_nonneg h0 _
    filter_upwards [ev_const_le_log (max 0 ((4:ℝ)/3*((16*C3))^((1:ℝ)/8)))
        (le_max_left _ _)] with x hx
    have hxle : (4:ℝ)/3*((16*C3))^((1:ℝ)/8) ≤ Real.log (x:ℝ) :=
      le_trans (le_max_right _ _) hx
    have h1 : ((16*C3))^((1:ℝ)/8) ≤ (3/4)*Real.log (x:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hxle (by norm_num : (0:ℝ) ≤ 3/4)
      rwa [show (3:ℝ)/4*((4:ℝ)/3*((16*C3))^((1:ℝ)/8)) = ((16*C3))^((1:ℝ)/8) by ring] at h
    calc (16:ℝ)*C3 = (((16*C3))^((1:ℝ)/8))^(8:ℕ) := (rpow_eighth_pow (16*C3) h0).symm
      _ ≤ ((3/4)*Real.log (x:ℝ))^8 := pow_le_pow_left₀ hC8nn h1 8
  have he6neg : 3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30 < 0 := by
    norm_num [Astar, Aprime]
  have hCb6 : ∀ᶠ x : ℕ in atTop,
      32*Cb * (Real.log (x:ℝ))^(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30) ≤ 1 := by
    have h := ev_const_le_log_pow (32*Cb)
      (-(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30)) (by positivity) (by linarith)
    filter_upwards [h, ev_const_le_log 1 (by norm_num)] with x hx hxlog
    have hLx : 0 < Real.log (x:ℝ) := lt_of_lt_of_le one_pos hxlog
    calc 32*Cb * (Real.log (x:ℝ))^(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30)
        ≤ (Real.log (x:ℝ))^(-(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30))
            * (Real.log (x:ℝ))^(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30) :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (le_of_lt hLx) _)
      _ = 1 := by
          rw [← Real.rpow_add hLx,
            show -(3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30)
              + (3*Astar + 6*Aprime Astar + Astar/2 - (2:ℝ)^30) = 0 by ring, Real.rpow_zero]
  have hE3nn : (0:ℝ) ≤ 2*Astar + 6*Aprime Astar + 516 := by norm_num [Astar, Aprime]
  have hE4nn : (0:ℝ) ≤ 2*Astar + 4*Aprime Astar + 1 := by norm_num [Astar, Aprime]
  have hcxNeg : ∀ᶠ x : ℕ in atTop,
      8*c1 * (Real.log (x:ℝ))^(2*Astar + 6*Aprime Astar + 516) * (x:ℝ)^(-η) ≤ 1 :=
    ev_const_log_pow_mul_rpow_neg_le (8*c1) _ η (by positivity) hE3nn hη
  have hcxExp : ∀ᶠ x : ℕ in atTop,
      8*c1 * (Real.log (x:ℝ))^(2*Astar + 6*Aprime Astar + 516)
        * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) ≤ 1 :=
    ev_const_log_pow_mul_exp_neg_loglog_sq_le (8*c1) _ (by positivity) hE3nn
  have hE4exp : ∀ᶠ x : ℕ in atTop,
      16 * (Real.log (x:ℝ))^(2*Astar + 4*Aprime Astar + 1)
        * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) ≤ 1 :=
    ev_const_log_pow_mul_exp_neg_loglog_sq_le 16 _ (by norm_num) hE4nn
  have hall := hx1.and (hL4.and (hLA.and (hpow8.and (hCb6.and (hcxNeg.and (hcxExp.and hE4exp))))))
  rw [eventually_atTop] at hall
  obtain ⟨x₀, hx₀⟩ := hall
  exact ⟨x₀, fun x hx => hx₀ x hx⟩

/-! ## The main theorem -/

theorem numHyp_proof2 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 3 / 32)
    (c1 Cb C3 c : ℝ) (hc1 : 0 < c1) (hCb : 0 < Cb) (hC3 : 0 < C3) (hc : 0 ≤ c) :
    ∃ x₀ : ℕ, ∀ (x : ℕ) (Pa : Work.FITop.Params) (N σ : ℝ), x₀ ≤ x →
      Pa.x = x → Pa.η = η → Pa.A = Astar → Pa.A' = Aprime Astar →
      Pa.θ = thetaOf x Astar → Pa.ϑ = varthetaOf x Astar → Pa.τ = tauOf x Astar →
      N ≤ (Pa.N : ℝ) → (Pa.N : ℝ) ≤ 2 * N →
      N < 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Bmax η))) →
      (16 * (Real.log (Pa.M * Pa.N)) ^ (8 : ℕ) * (Real.log (x : ℝ)) ^ (2 * Astar + 4 * Aprime Astar)
          ≤ (Real.log Pa.N) ^ σ) →
      NumHyp η x Pa σ c1 Cb C3 c := by
  obtain ⟨x₀, hthr⟩ := numHyp_threshold η c1 Cb C3 hη0 hc1 hCb hC3
  refine ⟨x₀, ?_⟩
  intro x Pa N σ hx hxeq hηeq hAeq hApeq hθeq hϑeq hτeq hNle hNle2 hNhi hσ
  obtain ⟨hx1, hLx4, hLxA, hC3le, hCb6, hcxNeg, hcxExp, hE4exp⟩ := hthr x hx
  have hxpos : (0:ℝ) < (x:ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hLxpos : 0 < Real.log (x:ℝ) := by linarith
  have hLxnn : 0 ≤ Real.log (x:ℝ) := le_of_lt hLxpos
  have hθ' : Pa.θ = (Real.log (x:ℝ))^(-(Aprime Astar)) := by rw [hθeq]; rfl
  have hϑ' : Pa.ϑ = (Real.log (x:ℝ))^(-Astar) := by rw [hϑeq]; rfl
  have hτ' : Pa.τ = (Real.log (x:ℝ))^(Aprime Astar) := by rw [hτeq]; rfl
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hMpos : 0 < Pa.M := lt_of_lt_of_le zero_lt_one Pa.hM1
  have hNpos : 0 < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  -- facts on Pa.N
  have hNlo' : (x:ℝ)^((1:ℝ)/4 + η) < Pa.N := by
    have h := Pa.hNlo; rw [hxeq, hηeq] at h; exact h
  have hMNx' : Pa.M * Pa.N ≤ (x:ℝ) := by
    have h := Pa.hMNx; rw [hxeq] at h; exact h
  have hMN' : Pa.ϑ * (x:ℝ) < Pa.M * Pa.N := by
    have h := Pa.hMN; rw [hxeq] at h; exact h
  have hPlo' : (Real.log (Real.log (x:ℝ)))^2 ≤ Real.log (Pa.Pz:ℝ) := by
    have h := Pa.hPlo; rw [hxeq] at h; exact h
  have hPzpos : (0:ℝ) < (Pa.Pz:ℝ) := by
    have h : (0:ℕ) < Pa.Pz := lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) Pa.hP2
    exact_mod_cast h
  have hPNgt2 : (2:ℝ) < Pa.N := by
    have h1 : (x:ℝ)^((1:ℝ)/4) ≤ (x:ℝ)^((1:ℝ)/4 + η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (2:ℝ) < (x:ℝ)^((1:ℝ)/4) := by
      rw [Real.rpow_def_of_pos hxpos]
      have h3 : (1:ℝ) ≤ Real.log (x:ℝ) * (1/4) := by linarith
      calc (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
        _ ≤ Real.exp (Real.log (x:ℝ)*(1/4)) := Real.exp_le_exp.mpr h3
    exact lt_of_lt_of_le (lt_trans h2 (lt_of_le_of_lt h1 hNlo')) (le_refl _)
  have hPNltx : Pa.N < (x:ℝ) := by
    have h := Pa.hNhi
    rw [hxeq] at h
    have hBpos : (0:ℝ) < Pa.B := Pa.hB
    have hLxinv : (Real.log (x:ℝ))^(-(Pa.B)) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt hLxpos)]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (le_of_lt hBpos))
    have hhalf : (x:ℝ)^((1:ℝ)/2) ≤ (x:ℝ) := by
      calc (x:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (x:ℝ) := Real.rpow_one _
    calc Pa.N < (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(Pa.B)) := h
      _ ≤ (x:ℝ)^((1:ℝ)/2) * 1 := mul_le_mul_of_nonneg_left hLxinv (Real.rpow_nonneg (le_of_lt hxpos) _)
      _ = (x:ℝ)^((1:ℝ)/2) := by ring
      _ ≤ (x:ℝ) := hhalf
  have hlogPNnn : 0 ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
  have hlogPNpos : 0 < Real.log Pa.N := Real.log_pos (lt_trans one_lt_two hPNgt2)
  have hlogPNle : Real.log Pa.N ≤ Real.log (x:ℝ) := Real.log_le_log hNpos (le_of_lt hPNltx)
  have hlogMNnn : 0 ≤ Real.log (Pa.M*Pa.N) := by
    apply Real.log_nonneg
    calc (1:ℝ) = 1*1 := by ring
      _ ≤ Pa.M*Pa.N := mul_le_mul Pa.hM1 Pa.hN1 (by norm_num) (le_of_lt hMpos)
  have hlogMNle : Real.log (Pa.M*Pa.N) ≤ Real.log (x:ℝ) :=
    Real.log_le_log (by positivity) hMNx'
  have hMNlo : (x:ℝ)^((3:ℝ)/4) ≤ Pa.M*Pa.N := by
    have h3 : (x:ℝ)^(-((1:ℝ)/4))*(x:ℝ) = (x:ℝ)^((3:ℝ)/4) := by
      have e : (x:ℝ)^(-((1:ℝ)/4))*(x:ℝ)^(1:ℝ) = (x:ℝ)^((3:ℝ)/4) := by
        rw [← Real.rpow_add hxpos, show -((1:ℝ)/4) + 1 = (3:ℝ)/4 by norm_num]
      rwa [Real.rpow_one] at e
    have hϑge : (x:ℝ)^(-((1:ℝ)/4)) ≤ Pa.ϑ := by
      rw [hϑ', Real.rpow_neg (le_of_lt hLxpos) Astar, Real.rpow_neg (le_of_lt hxpos) ((1:ℝ)/4)]
      exact inv_anti₀ (Real.rpow_pos_of_pos hLxpos Astar) hLxA
    calc (x:ℝ)^((3:ℝ)/4) = (x:ℝ)^(-((1:ℝ)/4))*(x:ℝ) := h3.symm
      _ ≤ Pa.ϑ*(x:ℝ) := mul_le_mul_of_nonneg_right hϑge (le_of_lt hxpos)
      _ ≤ Pa.M*Pa.N := le_of_lt hMN'
  have hx1lt : (1:ℝ) < (x:ℝ) := by
    rw [← Real.exp_log hxpos]; exact Real.one_lt_exp_iff.mpr hLxpos
  have hlogMNpos : 0 < Real.log (Pa.M*Pa.N) := by
    apply Real.log_pos
    exact lt_of_lt_of_le (Real.one_lt_rpow hx1lt (by norm_num)) hMNlo
  have hlogMNge34 : (3:ℝ)/4*Real.log (x:ℝ) ≤ Real.log (Pa.M*Pa.N) := by
    rw [← Real.log_rpow hxpos]
    exact Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hMNlo
  have hlogMNge2 : (2:ℝ) ≤ Real.log (Pa.M*Pa.N) := by
    have hx34 : Real.exp 2 ≤ (x:ℝ)^((3:ℝ)/4) := by
      rw [Real.rpow_def_of_pos hxpos]
      apply Real.exp_le_exp.mpr
      nlinarith [hLx4]
    calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (Pa.M*Pa.N) := Real.log_le_log (Real.exp_pos 2) (le_trans hx34 hMNlo)
  have hMN8ge1 : (1:ℝ) ≤ (Real.log (Pa.M*Pa.N))^8 := by
    calc (1:ℝ) = 1^8 := by norm_num
      _ ≤ (Real.log (Pa.M*Pa.N))^8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have hMN8ge2 : (2:ℝ) ≤ (Real.log (Pa.M*Pa.N))^8 :=
    le_trans (by norm_num : (2:ℝ) ≤ 2^8) (pow_le_pow_left₀ (by norm_num) hlogMNge2 8)
  have hMNpow16 : (2:ℝ) ≤ (Real.log (Pa.M*Pa.N))^(16:ℕ) :=
    le_trans (by norm_num : (2:ℝ) ≤ 2^16) (pow_le_pow_left₀ (by norm_num) hlogMNge2 16)
  -- power identities
  have hϑsq : Pa.ϑ^(2:ℕ) = (Real.log (x:ℝ))^(-(2*Astar)) := by
    rw [hϑ', rpow_natpow hLxnn (-Astar) 2]
    congr 1; ring
  have hθ4 : Pa.θ^(4:ℕ) = (Real.log (x:ℝ))^(-(4*(Aprime Astar))) := by
    rw [hθ', rpow_natpow hLxnn (-(Aprime Astar)) 4]
    congr 1; ring
  have hτ2 : Pa.τ^(2:ℕ) = (Real.log (x:ℝ))^(2*(Aprime Astar)) := by
    rw [hτ', rpow_natpow hLxnn (Aprime Astar) 2]
    congr 1; ring
  have hϑinv : Pa.ϑ⁻¹ = (Real.log (x:ℝ))^(Astar) := by
    rw [hϑ', Real.rpow_neg (le_of_lt hLxpos) Astar, inv_inv]
  have hPzinv : (Pa.Pz:ℝ)⁻¹ ≤ Real.exp (-(Real.log (Real.log (x:ℝ)))^2) := by
    have hexp : Real.exp ((Real.log (Real.log (x:ℝ)))^2) ≤ (Pa.Pz:ℝ) := by
      rw [← Real.le_log_iff_exp_le hPzpos]
      exact hPlo'
    calc (Pa.Pz:ℝ)⁻¹ ≤ (Real.exp ((Real.log (Real.log (x:ℝ)))^2))⁻¹ :=
          inv_anti₀ (Real.exp_pos _) hexp
      _ = Real.exp (-(Real.log (Real.log (x:ℝ)))^2) := by rw [Real.exp_neg]
  -- combination identities
  have hLxsplit2 : (Real.log (x:ℝ))^(Astar+2*(Aprime Astar))
      = (Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
        * (Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar))) := by
    rw [← Real.rpow_add hLxpos]
    rw [show 3*Astar+6*(Aprime Astar) + (-(2*Astar+4*(Aprime Astar))) = Astar+2*(Aprime Astar) by ring]
  have hLxsplit3 : (Real.log (x:ℝ))^(2*(Aprime Astar))
      = (Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
        * (Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar))) := by
    rw [← Real.rpow_add hLxpos]
    rw [show 2*Astar+6*(Aprime Astar) + (-(2*Astar+4*(Aprime Astar))) = 2*(Aprime Astar) by ring]
  have hLxcombine : (Real.log (x:ℝ))^(-(2*Astar)) * (Real.log (x:ℝ))^(-(4*(Aprime Astar)))
      = (Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar))) := by
    rw [← Real.rpow_add hLxpos]; congr 1; ring
  have hLx24 : (Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
      * (Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar))) = 1 := by
    rw [← Real.rpow_add hLxpos]; ring_nf; rw [Real.rpow_zero]
  -- ### Conjunct 1
  have hτinv : Pa.τ⁻¹ = Pa.θ := by
    rw [hτ', hθ', ← Real.rpow_neg (le_of_lt hLxpos) (Aprime Astar)]
  have hC3' : 16*C3 ≤ (Real.log (Pa.M*Pa.N))^8 :=
    le_trans hC3le (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ (3:ℝ)/4*Real.log (x:ℝ)) hlogMNge34 8)
  have hθLx : Pa.θ * (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ)) = Pa.ϑ^(2:ℕ) := by
    rw [← Real.rpow_natCast (Real.log (x:ℝ)) ((2:ℕ)^(20:ℕ)),
        ← Real.rpow_natCast Pa.ϑ 2, hθ', hϑ']
    rw [← Real.rpow_add hLxpos, ← Real.rpow_mul hLxnn]
    have hh : -(Aprime Astar) + (((2:ℕ)^(20:ℕ) : ℕ) : ℝ) = -(Astar) * ((2:ℕ) : ℝ) := by
      norm_num [Aprime, Astar]
    rw [hh]
  have hscalar1 : 16*C3*Pa.θ*(Real.log Pa.N)^((2:ℕ)^(20:ℕ))
      ≤ Pa.ϑ^(2:ℕ)*(Real.log (Pa.M*Pa.N))^8 := by
    have hLNpow : (Real.log Pa.N)^((2:ℕ)^(20:ℕ)) ≤ (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ)) :=
      pow_le_pow_left₀ hlogPNnn hlogPNle _
    have hLx20nn : (0:ℝ) ≤ (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ)) := pow_nonneg hLxnn _
    have hLHSaux : 16*C3*(Real.log Pa.N)^((2:ℕ)^(20:ℕ))
        ≤ (Real.log (Pa.M*Pa.N))^8 * (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ)) :=
      calc (16*C3*(Real.log Pa.N)^((2:ℕ)^(20:ℕ)))
          ≤ 16*C3*(Real.log (x:ℝ))^((2:ℕ)^(20:ℕ)) :=
            mul_le_mul_of_nonneg_left hLNpow (by positivity)
        _ ≤ (Real.log (Pa.M*Pa.N))^8 * (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ)) :=
            mul_le_mul_of_nonneg_right hC3' hLx20nn
    calc 16*C3*Pa.θ*(Real.log Pa.N)^((2:ℕ)^(20:ℕ))
        = Pa.θ * (16*C3*(Real.log Pa.N)^((2:ℕ)^(20:ℕ))) := by ring
      _ ≤ Pa.θ * ((Real.log (Pa.M*Pa.N))^8 * (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ))) :=
          mul_le_mul_of_nonneg_left hLHSaux (le_of_lt hθ0)
      _ = (Real.log (Pa.M*Pa.N))^8 * (Pa.θ * (Real.log (x:ℝ))^((2:ℕ)^(20:ℕ))) := by ring
      _ = (Real.log (Pa.M*Pa.N))^8 * Pa.ϑ^(2:ℕ) := by rw [hθLx]
      _ = Pa.ϑ^(2:ℕ)*(Real.log (Pa.M*Pa.N))^8 := by ring
  have hconj1 : 8 * C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4:ℕ) * Pa.M ^ ((1:ℝ)/2) * Pa.N ^ ((3:ℝ)/2)
        * (Real.log Pa.N) ^ ((2:ℕ)^(20:ℕ)) ≤ Tbudget Pa := by
    rw [Tbudget]
    have hWnn : (0:ℝ) ≤ Pa.θ^4 * (Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)) :=
      mul_nonneg (pow_nonneg (le_of_lt hθ0) 4)
        (mul_nonneg (Real.rpow_nonneg (le_of_lt hMpos) _) (Real.rpow_nonneg (le_of_lt hNpos) _))
    calc 8 * C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4:ℕ) * Pa.M ^ ((1:ℝ)/2) * Pa.N ^ ((3:ℝ)/2)
          * (Real.log Pa.N) ^ ((2:ℕ)^(20:ℕ))
        = (16*C3*Pa.θ*(Real.log Pa.N)^((2:ℕ)^(20:ℕ))) * (Pa.θ^4 * (Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by
            rw [hτinv]; ring
      _ ≤ (Pa.ϑ^(2:ℕ)*(Real.log (Pa.M*Pa.N))^8) * (Pa.θ^4 * (Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) :=
            mul_le_mul_of_nonneg_right hscalar1 hWnn
      _ = Pa.ϑ^(2:ℕ)*Pa.θ^(4:ℕ)*Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)*(Real.log (Pa.M*Pa.N))^(8:ℕ) := by ring
  -- ### Conjunct 2
  have hxlt : (x:ℝ) < Pa.M*Pa.N*(Real.log (x:ℝ))^(Astar) := by
    have h1 : Pa.ϑ⁻¹ * (Pa.ϑ*(x:ℝ)) < Pa.ϑ⁻¹ * (Pa.M*Pa.N) :=
      mul_lt_mul_of_pos_left hMN' (inv_pos.mpr Pa.hϑ0)
    have h2 : Pa.ϑ⁻¹ * (Pa.ϑ*(x:ℝ)) = (x:ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt Pa.hϑ0), one_mul]
    have h3 : Pa.ϑ⁻¹ * (Pa.M*Pa.N) = (Real.log (x:ℝ))^(Astar)*(Pa.M*Pa.N) := by rw [hϑinv]
    rw [h2, h3] at h1
    calc (x:ℝ) < (Real.log (x:ℝ))^(Astar)*(Pa.M*Pa.N) := h1
      _ = Pa.M*Pa.N*(Real.log (x:ℝ))^(Astar) := by ring
  have hstep1 : Pa.N/Pa.M < Pa.N^2*(Real.log (x:ℝ))^(Astar)/(x:ℝ) := by
    rw [div_lt_div_iff₀ hMpos hxpos]
    calc Pa.N*(x:ℝ) < Pa.N*(Pa.M*Pa.N*(Real.log (x:ℝ))^(Astar)) :=
          mul_lt_mul_of_pos_left hxlt hNpos
      _ = Pa.N^2*(Real.log (x:ℝ))^(Astar)*Pa.M := by ring
  have hPNlt : Pa.N < 4*((x:ℝ)^((1:ℝ)/2)*(Real.log (x:ℝ))^(-(Bmax η))) := by
    calc Pa.N ≤ 2*N := hNle2
      _ < 2*(2*((x:ℝ)^((1:ℝ)/2)*(Real.log (x:ℝ))^(-(Bmax η)))) := by linarith [hNhi]
      _ = 4*((x:ℝ)^((1:ℝ)/2)*(Real.log (x:ℝ))^(-(Bmax η))) := by ring
  have hstep2 : Pa.N^2 < 16*(x:ℝ)*(Real.log (x:ℝ))^(-(2*Bmax η)) := by
    have h := pow_lt_pow_left₀ hPNlt (le_of_lt hNpos) (by norm_num : (2:ℕ) ≠ 0)
    calc Pa.N^2 < (4*((x:ℝ)^((1:ℝ)/2)*(Real.log (x:ℝ))^(-(Bmax η))))^(2:ℕ) := h
      _ = 16*((x:ℝ)^((1:ℝ)/2))^(2:ℕ)*((Real.log (x:ℝ))^(-(Bmax η)))^(2:ℕ) := by ring
      _ = 16*(x:ℝ)*(Real.log (x:ℝ))^(-(2*Bmax η)) := by
          rw [rpow_half_sq (x:ℝ) (le_of_lt hxpos), rpow_natpow hLxnn]
          congr 1; ring
  have hstep3 : Pa.N/Pa.M < 16*(Real.log (x:ℝ))^(Astar-2*Bmax η) := by
    have hstep2' : Pa.N^2*(Real.log (x:ℝ))^(Astar)
        < 16*(x:ℝ)*(Real.log (x:ℝ))^(-(2*Bmax η))*(Real.log (x:ℝ))^(Astar) :=
      mul_lt_mul_of_pos_right hstep2 (Real.rpow_pos_of_pos hLxpos _)
    have hle : 16*(x:ℝ)*(Real.log (x:ℝ))^(-(2*Bmax η))*(Real.log (x:ℝ))^(Astar)/(x:ℝ)
        ≤ 16*(Real.log (x:ℝ))^(Astar-2*Bmax η) := by
      rw [div_le_iff₀ hxpos]
      rw [show 16*(x:ℝ)*(Real.log (x:ℝ))^(-(2*Bmax η))*(Real.log (x:ℝ))^(Astar)
          = 16*(Real.log (x:ℝ))^(Astar-2*Bmax η)*(x:ℝ) by
        rw [show 16*(x:ℝ)*(Real.log (x:ℝ))^(-(2*Bmax η))*(Real.log (x:ℝ))^(Astar)
            = 16*((Real.log (x:ℝ))^(-(2*Bmax η))*(Real.log (x:ℝ))^(Astar))*(x:ℝ) by ring]
        rw [← Real.rpow_add hLxpos,
            show -(2*Bmax η)+Astar = Astar-2*Bmax η by ring]]
    exact lt_of_lt_of_le (lt_trans hstep1 (div_lt_div_of_pos_right hstep2' hxpos)) hle
  have hNMhalf : (Pa.N/Pa.M)^((1:ℝ)/2) ≤ 4*(Real.log (x:ℝ))^(Astar/2-Bmax η) := by
    have h := Real.rpow_le_rpow (le_of_lt (div_pos hNpos hMpos)) (le_of_lt hstep3)
      (by norm_num : (0:ℝ) ≤ 1/2)
    have heq : (16*(Real.log (x:ℝ))^(Astar-2*Bmax η))^((1:ℝ)/2)
        = 4*(Real.log (x:ℝ))^(Astar/2-Bmax η) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hLxnn _), rpow_sixteen_half,
          ← Real.rpow_mul hLxnn]
      rw [show (Astar-2*Bmax η)*((1:ℝ)/2) = Astar/2-Bmax η by ring]
    rwa [heq] at h
  have hlogPNb : (Real.log Pa.N)^(bFun η) ≤ (Real.log (x:ℝ))^(bFun η) :=
    Real.rpow_le_rpow hlogPNnn hlogPNle (le_of_lt (bFun_pos η))
  have hE1 : (8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
        *(4*(Real.log (x:ℝ))^(Astar/2-Bmax η)))*((Real.log (x:ℝ))^(bFun η))
      = 32*Cb*(((Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
        *(Real.log (x:ℝ))^(Astar/2-Bmax η))*(Real.log (x:ℝ))^(bFun η)) := by ring
  have hE2 : ((Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
        *(Real.log (x:ℝ))^(Astar/2-Bmax η))*(Real.log (x:ℝ))^(bFun η)
      = (Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar)+Astar/2-Bmax η+bFun η) := by
    rw [← Real.rpow_add hLxpos, ← Real.rpow_add hLxpos]
    congr 1; ring
  have hscalar2 : 8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
        *((Pa.N/Pa.M)^((1:ℝ)/2))*(Real.log Pa.N)^(bFun η)
      ≤ (Real.log (Pa.M*Pa.N))^8 := by
    have hBmax : (Bmax η) = bFun η + (2:ℝ)^30 := rfl
    have hA1 : 8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))*((Pa.N/Pa.M)^((1:ℝ)/2))
        ≤ 8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
          *(4*(Real.log (x:ℝ))^(Astar/2-Bmax η)) :=
      mul_le_mul_of_nonneg_left hNMhalf (by positivity)
    have hA2 : 8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))*((Pa.N/Pa.M)^((1:ℝ)/2))
          *(Real.log Pa.N)^(bFun η)
        ≤ (8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
          *(4*(Real.log (x:ℝ))^(Astar/2-Bmax η)))*((Real.log (x:ℝ))^(bFun η)) :=
      mul_le_mul hA1 hlogPNb (Real.rpow_nonneg hlogPNnn _) (by positivity)
    calc 8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
          *((Pa.N/Pa.M)^((1:ℝ)/2))*(Real.log Pa.N)^(bFun η)
        ≤ (8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
          *(4*(Real.log (x:ℝ))^(Astar/2-Bmax η)))*((Real.log (x:ℝ))^(bFun η)) := hA2
      _ = 32*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar)+Astar/2-Bmax η+bFun η) := by
            rw [hE1, hE2]
      _ = 32*Cb*(Real.log (x:ℝ))^(3*Astar+6*Aprime Astar+Astar/2-(2:ℝ)^30) := by
            rw [show 3*Astar+6*(Aprime Astar)+Astar/2-Bmax η+bFun η
                = 3*Astar+6*Aprime Astar+Astar/2-(2:ℝ)^30 by rw [hBmax]; ring]
      _ ≤ 1 := hCb6
      _ ≤ (Real.log (Pa.M*Pa.N))^8 := hMN8ge1
  have hLN2 : Pa.N^2 = (Pa.N/Pa.M)^((1:ℝ)/2)*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)) := by
    rw [Real.div_rpow (le_of_lt hNpos) (le_of_lt hMpos)]
    rw [← Real.rpow_natCast Pa.N 2]
    rw [show (((2:ℕ):ℝ)) = (3:ℝ)/2 + 1/2 by norm_num, Real.rpow_add hNpos]
    field_simp
  have hconj2 : 8 * Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2:ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun η)
      ≤ Tbudget Pa := by
    rw [Tbudget, hτ2, hϑsq, hθ4, hϑinv]
    calc 8 * Cb * (Real.log (x:ℝ))^(Astar) * (Real.log (x:ℝ))^(2*(Aprime Astar))
          * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun η)
        = (8*Cb*(Real.log (x:ℝ))^(3*Astar+6*(Aprime Astar))
            *((Pa.N/Pa.M)^((1:ℝ)/2))*(Real.log Pa.N)^(bFun η))
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by
            rw [show 8 * Cb * (Real.log (x:ℝ))^(Astar) * (Real.log (x:ℝ))^(2*(Aprime Astar))
                * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun η)
              = 8*Cb*((Real.log (x:ℝ))^(Astar)*(Real.log (x:ℝ))^(2*(Aprime Astar)))
                *Pa.N^2*(Real.log Pa.N)^(bFun η) by ring]
            rw [← Real.rpow_add hLxpos, hLxsplit2, hLN2]
            ring
      _ ≤ (Real.log (Pa.M*Pa.N))^8
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by
            apply mul_le_mul_of_nonneg_right hscalar2
            exact mul_nonneg (Real.rpow_nonneg hLxnn _)
              (mul_nonneg (Real.rpow_nonneg (le_of_lt hMpos) _) (Real.rpow_nonneg (le_of_lt hNpos) _))
      _ = (Real.log (x:ℝ))^(-(2*Astar))*(Real.log (x:ℝ))^(-(4*(Aprime Astar)))
            *Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)*(Real.log (Pa.M*Pa.N))^(8:ℕ) := by
            rw [← hLxcombine]; ring
  -- ### Conjunct 3
  have hM14 : Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) ≤ (x:ℝ)^(-η) := by
    have hMNq : Pa.M^((1:ℝ)/4)*Pa.N^((1:ℝ)/4) ≤ (x:ℝ)^((1:ℝ)/4) := by
      have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ Pa.M*Pa.N) hMNx' (by norm_num : (0:ℝ) ≤ 1/4)
      rwa [Real.mul_rpow (le_of_lt hMpos) (le_of_lt hNpos)] at h
    have hp : Pa.M^((1:ℝ)/4)*Pa.N^((1:ℝ)/4)*Pa.N^(-((1:ℝ)/4)) = Pa.M^((1:ℝ)/4) := by
      rw [mul_assoc, ← Real.rpow_add hNpos,
          show (1:ℝ)/4 + (-((1:ℝ)/4)) = 0 by ring, Real.rpow_zero, mul_one]
    have hMq : Pa.M^((1:ℝ)/4) ≤ (x:ℝ)^((1:ℝ)/4)*Pa.N^(-((1:ℝ)/4)) := by
      calc Pa.M^((1:ℝ)/4) = Pa.M^((1:ℝ)/4)*Pa.N^((1:ℝ)/4)*Pa.N^(-((1:ℝ)/4)) := hp.symm
        _ ≤ (x:ℝ)^((1:ℝ)/4)*Pa.N^(-((1:ℝ)/4)) :=
              mul_le_mul_of_nonneg_right hMNq (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hp2 : (x:ℝ)^((1:ℝ)/4) * Pa.N^(-(1:ℝ)) ≤ (x:ℝ)^(-η) := by
      have h2 : Pa.N^(-(1:ℝ)) ≤ (x:ℝ)^(-((1:ℝ)/4+η)) := by
        rw [Real.rpow_neg (le_of_lt hNpos) (1:ℝ),
            Real.rpow_neg (le_of_lt hxpos) ((1:ℝ)/4+η), Real.rpow_one]
        exact inv_anti₀ (Real.rpow_pos_of_pos hxpos _) (le_of_lt hNlo')
      calc (x:ℝ)^((1:ℝ)/4) * Pa.N^(-(1:ℝ))
          ≤ (x:ℝ)^((1:ℝ)/4) * (x:ℝ)^(-((1:ℝ)/4+η)) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (le_of_lt hxpos) _)
        _ = (x:ℝ)^(-η) := by rw [← Real.rpow_add hxpos]; congr 1; ring
    calc Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4)
        ≤ ((x:ℝ)^((1:ℝ)/4)*Pa.N^(-((1:ℝ)/4)))*Pa.N^(-(3:ℝ)/4) :=
          mul_le_mul_of_nonneg_right hMq (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = (x:ℝ)^((1:ℝ)/4) * (Pa.N^(-((1:ℝ)/4))*Pa.N^(-(3:ℝ)/4)) := by ring
      _ = (x:ℝ)^((1:ℝ)/4) * Pa.N^(-(1:ℝ)) := by
            congr 1
            rw [← Real.rpow_add hNpos]
            congr 1; ring
      _ ≤ (x:ℝ)^(-η) := hp2
  have hcomb3 : (Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar)) * (Real.log (x:ℝ))^(516:ℕ)
      = (Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar)+516) := by
    rw [← Real.rpow_natCast (Real.log (x:ℝ)) 516, ← Real.rpow_add hLxpos]
    congr 1
  have hC3scalar : 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
        *(Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹)*(Real.log (Pa.M*Pa.N))^(516:ℕ)
      ≤ (Real.log (Pa.M*Pa.N))^8 := by
    have hsum : Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹
        ≤ (x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2) :=
      add_le_add hM14 hPzinv
    have h516 : (Real.log (Pa.M*Pa.N))^(516:ℕ) ≤ (Real.log (x:ℝ))^(516:ℕ) :=
      pow_le_pow_left₀ hlogMNnn hlogMNle _
    have hB1 : 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
          *(Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹)
        ≤ 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
          *((x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    calc 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
          *(Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹)*(Real.log (Pa.M*Pa.N))^(516:ℕ)
        ≤ (8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
          *((x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2)))*(Real.log (Pa.M*Pa.N))^(516:ℕ) :=
            mul_le_mul_of_nonneg_right hB1 (pow_nonneg hlogMNnn _)
      _ ≤ (8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
          *((x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2)))*(Real.log (x:ℝ))^(516:ℕ) :=
            mul_le_mul_of_nonneg_left h516 (by positivity)
      _ = 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar)+516)
          *((x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2)) := by
            rw [show (8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
                *((x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2)))*(Real.log (x:ℝ))^(516:ℕ)
              = 8*c1*((Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))*(Real.log (x:ℝ))^(516:ℕ))
                *((x:ℝ)^(-η) + Real.exp (-(Real.log (Real.log (x:ℝ)))^2)) by ring, hcomb3]
      _ = 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar)+516)*(x:ℝ)^(-η)
          + 8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar)+516)
            *Real.exp (-(Real.log (Real.log (x:ℝ)))^2) := by ring
      _ ≤ 1 + 1 := add_le_add hcxNeg hcxExp
      _ = 2 := by norm_num
      _ ≤ (Real.log (Pa.M*Pa.N))^8 := by linarith [hMN8ge2]
  have hfac : Pa.M ^ ((3:ℝ)/4) * Pa.N ^ ((3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹ * Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)
      = (Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹)
          * (Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)) := by
    rw [add_mul]
    congr 1
    · rw [show Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4)*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))
            = (Pa.M^((1:ℝ)/4)*Pa.M^((1:ℝ)/2))*(Pa.N^(-(3:ℝ)/4)*Pa.N^((3:ℝ)/2)) by ring]
      rw [← Real.rpow_add hMpos, ← Real.rpow_add hNpos]
      norm_num
    · ring
  have hconj3 : 8 * c1 * Pa.τ ^ (2:ℕ) * (Pa.M ^ ((3:ℝ)/4) * Pa.N ^ ((3:ℝ)/4)
        + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1:ℝ)/2) * Pa.N ^ ((3:ℝ)/2))
        * (Real.log (Pa.M * Pa.N)) ^ (516:ℕ) ≤ Tbudget Pa := by
    rw [Tbudget, hfac, hτ2, hϑsq, hθ4]
    calc 8 * c1 * (Real.log (x:ℝ))^(2*(Aprime Astar))
          * ((Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹)*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)))
          * (Real.log (Pa.M * Pa.N)) ^ (516:ℕ)
        = (8*c1*(Real.log (x:ℝ))^(2*Astar+6*(Aprime Astar))
            *(Pa.M^((1:ℝ)/4)*Pa.N^(-(3:ℝ)/4) + (Pa.Pz:ℝ)⁻¹)*(Real.log (Pa.M*Pa.N))^(516:ℕ))
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by
            rw [hLxsplit3]; ring
      _ ≤ (Real.log (Pa.M*Pa.N))^8
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by
            apply mul_le_mul_of_nonneg_right hC3scalar
            exact mul_nonneg (Real.rpow_nonneg hLxnn _)
              (mul_nonneg (Real.rpow_nonneg (le_of_lt hMpos) _) (Real.rpow_nonneg (le_of_lt hNpos) _))
      _ = (Real.log (x:ℝ))^(-(2*Astar))*(Real.log (x:ℝ))^(-(4*(Aprime Astar)))
            *Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)*(Real.log (Pa.M*Pa.N))^(8:ℕ) := by
            rw [← hLxcombine]; ring
  -- ### Conjunct 4
  have hsigma : 16*(Real.log (Pa.M*Pa.N))^(8:ℕ)*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
      ≤ (Real.log Pa.N)^σ := hσ
  have h4a : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Real.log Pa.N)^(-σ)
      ≤ (1/2)*(Real.log (Pa.M*Pa.N))^8 := by
    rw [Real.rpow_neg (le_of_lt hlogPNpos) σ]
    have hb : 0 < 16*(Real.log (Pa.M*Pa.N))^(8:ℕ)*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)) :=
      mul_pos (by positivity) (Real.rpow_pos_of_pos hLxpos _)
    have h1 : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          * ((Real.log Pa.N)^σ)⁻¹
        ≤ 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          * (16*(Real.log (Pa.M*Pa.N))^(8:ℕ)*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)))⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ hb hsigma) (by positivity)
    have h2 : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          * (16*(Real.log (Pa.M*Pa.N))^(8:ℕ)*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)))⁻¹
        = ((Real.log (Pa.M*Pa.N))^8)⁻¹ := by
      field_simp
    have hYpos2 : (0:ℝ) < (Real.log (Pa.M*Pa.N))^8 := pow_pos hlogMNpos 8
    have h3 : ((Real.log (Pa.M*Pa.N))^8)⁻¹ ≤ (1/2)*(Real.log (Pa.M*Pa.N))^8 := by
      rw [inv_le_iff_one_le_mul₀ hYpos2]
      rw [show (1:ℝ)/2*(Real.log (Pa.M*Pa.N))^8*(Real.log (Pa.M*Pa.N))^8
          = (1/2)*((Real.log (Pa.M*Pa.N))^8*(Real.log (Pa.M*Pa.N))^8) by ring]
      have h4 : (Real.log (Pa.M*Pa.N))^(8:ℕ)*(Real.log (Pa.M*Pa.N))^(8:ℕ)
          = (Real.log (Pa.M*Pa.N))^(16:ℕ) := by ring
      rw [h4]; linarith [hMNpow16]
    linarith [h1, h2, h3]
  have h4b : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)
      ≤ (1/2)*(Real.log (Pa.M*Pa.N))^8 := by
    have h1 : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)
        ≤ 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          *Real.exp (-(Real.log (Real.log (x:ℝ)))^2)*(Real.log (x:ℝ)) := by
      calc 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)
          ≤ 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
            *Real.exp (-(Real.log (Real.log (x:ℝ)))^2)*(Real.log Pa.N) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hPzinv (by positivity)) hlogPNnn
        _ ≤ 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
            *Real.exp (-(Real.log (Real.log (x:ℝ)))^2)*(Real.log (x:ℝ)) :=
            mul_le_mul_of_nonneg_left hlogPNle (by positivity)
    have h2 : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) * (Real.log (x:ℝ))
        = 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)+1)
          * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) := by
      have e1 : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
            * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) * (Real.log (x:ℝ))
          = 16*((Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Real.log (x:ℝ)))
            * Real.exp (-(Real.log (Real.log (x:ℝ)))^2) := by ring
      rw [e1]
      have e2 : (Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Real.log (x:ℝ))
          = (Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)+1) := by
        rw [show (Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)+1)
            = (Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Real.log (x:ℝ))^(1:ℝ) by
              rw [Real.rpow_add hLxpos]]
        rw [Real.rpow_one]
      rw [e2]
    calc 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))*(Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)
        ≤ 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          *Real.exp (-(Real.log (Real.log (x:ℝ)))^2)*(Real.log (x:ℝ)) := h1
      _ = 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar)+1)
          *Real.exp (-(Real.log (Real.log (x:ℝ)))^2) := h2
      _ ≤ 1 := hE4exp
      _ ≤ (1/2)*(Real.log (Pa.M*Pa.N))^8 := by linarith [hMN8ge2]
  have hC4scalar : 16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
        *((Real.log Pa.N)^(-σ) + (Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)) ≤ (Real.log (Pa.M*Pa.N))^8 := by
    rw [mul_add]
    linarith [h4a, h4b]
  have hconj4 : 16 * Pa.M ^ ((1:ℝ)/2) * Pa.N ^ ((3:ℝ)/2)
        * ((Real.log Pa.N) ^ (-σ) + (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N) ≤ Tbudget Pa := by
    rw [Tbudget, hϑsq, hθ4]
    have hWnn : (0:ℝ) ≤ Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hMpos) _) (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hfac4 : 16 * Pa.M ^ ((1:ℝ)/2) * Pa.N ^ ((3:ℝ)/2)
          * ((Real.log Pa.N) ^ (-σ) + (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N)
        = (16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
            *((Real.log Pa.N)^(-σ) + (Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)))
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by
      calc 16 * Pa.M ^ ((1:ℝ)/2) * Pa.N ^ ((3:ℝ)/2)
            * ((Real.log Pa.N) ^ (-σ) + (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N)
          = 16*((Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
                *(Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar))))
              *(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))
              *((Real.log Pa.N)^(-σ) + (Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)) := by
                rw [hLx24]; ring
        _ = (16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
              *((Real.log Pa.N)^(-σ) + (Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)))
            * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) := by ring
    rw [hfac4]
    calc (16*(Real.log (x:ℝ))^(2*Astar+4*(Aprime Astar))
          *((Real.log Pa.N)^(-σ) + (Pa.Pz:ℝ)⁻¹*(Real.log Pa.N)))
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)))
        ≤ (Real.log (Pa.M*Pa.N))^8
          * ((Real.log (x:ℝ))^(-(2*Astar+4*(Aprime Astar)))*(Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2))) :=
            mul_le_mul_of_nonneg_right hC4scalar
              (mul_nonneg (Real.rpow_nonneg hLxnn _) hWnn)
      _ = (Real.log (x:ℝ))^(-(2*Astar))*(Real.log (x:ℝ))^(-(4*(Aprime Astar)))
            *Pa.M^((1:ℝ)/2)*Pa.N^((3:ℝ)/2)*(Real.log (Pa.M*Pa.N))^(8:ℕ) := by
            rw [← hLxcombine]; ring
  exact ⟨hconj1, hconj2, hconj3, hconj4⟩

end Work.FITop4.Numeric4
