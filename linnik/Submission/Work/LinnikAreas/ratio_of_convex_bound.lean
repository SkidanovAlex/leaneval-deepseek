import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SelbergSieveAux
import Submission.Work.LinnikAreas.perrErr_tendsto_zero
import Submission.Work.LinnikAreas.BGTZ.Ssm_le_res_add_J
import Submission.Work.LinnikAreas.ratio_convex_const

namespace Work.LinnikAreas

open DirichletCharacter Complex MeasureTheory Filter
open scoped BigOperators

theorem ratio_of_convex_bound (C6 : ℝ) (hC6 : 0 < C6)
    (hJconv : ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {β x : ℝ}, 3 / 4 ≤ β → β < 1 → 1 ≤ x →
      MeasureTheory.Integrable
          (fun y : ℝ => Work.LinnikAreas.triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) ∧
      ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
        ≤ C6 * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β))
    (hperr : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ {β x : ℝ}, 0 < β → 0 < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr χ β x T) Filter.atTop (nhds 0))
    (hH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {β x : ℝ}, 1 / 2 < β → β < 1 → 0 < x →
      Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun χ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun χ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ : DirichletCharacter ℂ q),
      χ ^ 2 = 1 → χ ≠ 1 → ∀ {β : ℝ}, β < 1 → Work.LinnikContract.zeroMult χ (β : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β →
        c * (1 - β) ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re := by
  obtain ⟨N, hN3, hNbound⟩ := ratio_convex_const C6 hC6
  refine ⟨Real.exp (-((N : ℝ) / 10)) / 4, by positivity, ?_⟩
  intro q inst hq χ hχ2 hχne β hβ1 hzm hβ'
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq3 : 3 ≤ q := by omega
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hq400 : (400001 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 400001 ≤ q)
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_three]
  have hlogqpos : (0 : ℝ) < Real.log (q : ℝ) := by linarith
  have h1mβ : 1 - β < 1 / (10 * Real.log (q : ℝ)) := by linarith [hβ']
  have hdiv : 1 / (10 * Real.log (q : ℝ)) ≤ 1 / 10 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 10) (by linarith)
  have hβpos : 0 < β := by linarith
  have hβ34 : 3 / 4 ≤ β := by linarith
  have hβhalf : 1 / 2 < β := by linarith
  have h1mβlog : (1 - β) * Real.log (q : ℝ) < 1 / 10 := by
    have h := mul_lt_mul_of_pos_right h1mβ hlogqpos
    have h2 : (1 / (10 * Real.log (q : ℝ))) * Real.log (q : ℝ) = 1/10 := by
      field_simp
    linarith
  set x : ℝ := (q : ℝ) ^ N + 1 / 2 with hxdef
  have hqNge1 : (1 : ℝ) ≤ (q : ℝ) ^ N := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hqR N
  have hqle : (q : ℝ) ≤ (q : ℝ) ^ N := by
    simpa using pow_le_pow_right₀ hqR (by omega : 1 ≤ N)
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hxpos : 0 < x := by linarith
  have hx4 : 4 ≤ x := by rw [hxdef]; linarith
  have hqNpos : (0:ℝ) < (q:ℝ)^N := by positivity
  have hxqN : (q:ℝ)^N ≤ x := by rw [hxdef]; linarith
  have hxnn : ∀ n : ℕ, (n : ℝ) ≠ x := by
    intro n hn
    have hqNcast : (q:ℝ)^N = ((q^N : ℕ) : ℝ) := by push_cast; ring
    have h2 : (2 * (n:ℝ)) = 2 * (q:ℝ)^N + 1 := by rw [hn, hxdef]; ring
    have h4 : (2 * n : ℕ) = 2 * q^N + 1 := by
      have h5 : ((2 * n : ℕ) : ℝ) = ((2 * q^N + 1 : ℕ) : ℝ) := by
        push_cast
        rw [hqNcast] at h2
        linarith
      exact_mod_cast h5
    omega
  have hL0 : DirichletCharacter.LFunction χ (β : ℂ) = 0 :=
    Work.LinnikAreas.LFunction_eq_zero_of_zeroMult χ hχne hβpos hβ1 hzm
  have hJb := hJconv q hq3 χ hχne hβ34 hβ1 (le_of_lt hx1)
  -- ---- the bound on the critical-line integral
  have hβlt : 1 / 2 - β < 0 := by linarith
  have hqNpow : (q:ℝ) ^ ((N:ℝ) * (1 - β)) ≤ Real.exp ((N:ℝ)/10) := by
    have hle := mul_le_mul_of_nonneg_left h1mβlog.le (Nat.cast_nonneg N)
    have hstep : Real.log (q:ℝ) * ((N:ℝ)*(1-β)) ≤ (N:ℝ)/10 := by nlinarith [hle]
    rw [Real.rpow_def_of_pos hqpos]
    exact Real.exp_le_exp.mpr hstep
  have hxqhalf : x ^ (1/2 - β) ≤ Real.exp ((N:ℝ)/10) * (q:ℝ) ^ (-((N:ℝ)/2)) := by
    have h1 : x ^ (1/2 - β) ≤ ((q:ℝ)^N) ^ (1/2 - β) :=
      Real.rpow_le_rpow_of_nonpos hqNpos hxqN hβlt.le
    have h2 : ((q:ℝ)^N) ^ (1/2 - β) = (q:ℝ) ^ ((N:ℝ)*(1/2-β)) := by
      rw [← Real.rpow_natCast (q:ℝ) N, ← Real.rpow_mul hqpos.le]
    have h3 : (q:ℝ) ^ ((N:ℝ)*(1/2-β)) = (q:ℝ)^((N:ℝ)*(1-β)) * (q:ℝ)^(-((N:ℝ)/2)) := by
      rw [← Real.rpow_add hqpos]
      congr 1
      ring
    calc x ^ (1/2-β) ≤ (q:ℝ)^((N:ℝ)*(1/2-β)) := by rw [← h2]; exact h1
      _ = (q:ℝ)^((N:ℝ)*(1-β)) * (q:ℝ)^(-((N:ℝ)/2)) := h3
      _ ≤ Real.exp ((N:ℝ)/10) * (q:ℝ)^(-((N:ℝ)/2)) :=
          mul_le_mul_of_nonneg_right hqNpow (Real.rpow_nonneg hqpos.le _)
  have hlogb : Real.log (2*(q:ℝ)+2) ≤ 3 * (q:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2*(q:ℝ)+2 by positivity)
    linarith
  have hqpow : (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) ≤ (400001:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) := by
    have hN3R : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
    have hexp : (4:ℝ)/3 - (N:ℝ)/2 ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hq400 hexp
  have hK : C6 * (q:ℝ)^((1:ℝ)/3) * Real.log (2*(q:ℝ)+2) * x^(1/2-β) ≤ 1/4 := by
    have hC6q : 0 ≤ C6 * (q:ℝ)^((1:ℝ)/3) :=
      mul_nonneg hC6.le (Real.rpow_nonneg hqpos.le _)
    have step1 : C6 * (q:ℝ)^((1:ℝ)/3) * Real.log (2*(q:ℝ)+2) * x^(1/2-β)
        ≤ C6 * (q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ)) * (Real.exp ((N:ℝ)/10) * (q:ℝ)^(-((N:ℝ)/2))) := by
      calc C6 * (q:ℝ)^((1:ℝ)/3) * Real.log (2*(q:ℝ)+2) * x^(1/2-β)
          = (C6 * (q:ℝ)^((1:ℝ)/3)) * (Real.log (2*(q:ℝ)+2) * x^(1/2-β)) := by ring
        _ ≤ (C6 * (q:ℝ)^((1:ℝ)/3))
              * ((3*(q:ℝ)) * (Real.exp ((N:ℝ)/10) * (q:ℝ)^(-((N:ℝ)/2)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hlogb hxqhalf (Real.rpow_nonneg hxpos.le _) (by positivity)) hC6q
        _ = C6 * (q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ))
              * (Real.exp ((N:ℝ)/10) * (q:ℝ)^(-((N:ℝ)/2))) := by ring
    have step2 : C6 * (q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ))
          * (Real.exp ((N:ℝ)/10) * (q:ℝ)^(-((N:ℝ)/2)))
        = 3 * C6 * (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) * Real.exp ((N:ℝ)/10) := by
      have h4 : (q:ℝ)^((1:ℝ)/3) * (q:ℝ) * (q:ℝ)^(-((N:ℝ)/2))
          = (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) := by
        nth_rewrite 2 [show (q:ℝ) = (q:ℝ)^((1:ℝ)) from (Real.rpow_one (q:ℝ)).symm]
        rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
        congr 1
        ring
      have h4' : (q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ)) * (q:ℝ)^(-((N:ℝ)/2))
          = 3 * (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) := by
        rw [show (q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ)) * (q:ℝ)^(-((N:ℝ)/2))
              = 3 * ((q:ℝ)^((1:ℝ)/3) * (q:ℝ) * (q:ℝ)^(-((N:ℝ)/2))) by ring, h4]
      calc C6 * (q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ))
              * (Real.exp ((N:ℝ)/10) * (q:ℝ)^(-((N:ℝ)/2)))
          = C6 * ((q:ℝ)^((1:ℝ)/3) * (3*(q:ℝ)) * (q:ℝ)^(-((N:ℝ)/2)))
              * Real.exp ((N:ℝ)/10) := by ring
        _ = C6 * (3 * (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2)) * Real.exp ((N:ℝ)/10) := by rw [h4']
        _ = 3 * C6 * (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) * Real.exp ((N:ℝ)/10) := by ring
    have step3 : 3 * C6 * (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) * Real.exp ((N:ℝ)/10)
        ≤ 3 * C6 * (400001:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) * Real.exp ((N:ℝ)/10) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left hqpow
      positivity
    calc C6 * (q:ℝ)^((1:ℝ)/3) * Real.log (2*(q:ℝ)+2) * x^(1/2-β)
        ≤ 3 * C6 * (q:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) * Real.exp ((N:ℝ)/10) := by
          rw [← step2]; exact step1
      _ ≤ 3 * C6 * (400001:ℝ)^((4:ℝ)/3 - (N:ℝ)/2) * Real.exp ((N:ℝ)/10) := step3
      _ ≤ 1/4 := hNbound
  -- ---- the Hecke-type lower bound
  have hmain := Work.LinnikAreas.BGTZ.Ssm_le_res_add_J (β := β) (x := x) (K := 1/4)
      χ hχne hχ2 hβhalf hβ1 hx1 hxnn hL0 hJb.1
      (hperr q χ hχ2 hβpos hxpos hxnn) (hH q χ hχne hβhalf hβ1 hxpos) (le_trans hJb.2 hK)
  have hssm : 1 - 1/x ≤ Work.LinnikAreas.Ssm χ β x :=
    Work.LinnikAreas.BGTZ.Ssm_ge_one' χ hχ2 β (le_of_lt hx1)
  have h1divx : 1/x ≤ 1/4 := by
    rw [div_le_div_iff₀ hxpos (by norm_num : (0:ℝ) < 4)]
    linarith
  have hkey : (1:ℝ)/2 ≤ (DirichletCharacter.LFunction χ (1:ℂ)).re
      * (x^(1-β)/((1-β)*(2-β))) := by
    linarith [hmain, hssm, h1divx]
  have h1mβpos : 0 < 1 - β := by linarith
  have hdenpos : 0 < (1-β)*(2-β) := by nlinarith
  have hxpowpos : 0 < x^(1-β) := Real.rpow_pos_of_pos hxpos _
  have hBpos : 0 < (1-β)*(2-β)/x^(1-β) := div_pos hdenpos hxpowpos
  have hratio : x^(1-β)/((1-β)*(2-β)) = 1/((1-β)*(2-β)/x^(1-β)) := by
    rw [one_div, inv_div]
  rw [hratio, mul_one_div, le_div_iff₀ hBpos] at hkey
  have hxpow_le : x^(1-β) ≤ 2 * Real.exp ((N:ℝ)/10) := by
    have hx2 : x ≤ 2 * (q:ℝ)^N := by
      rw [hxdef]; linarith [hqNge1]
    have h1 : x^(1-β) ≤ (2*(q:ℝ)^N)^(1-β) :=
      Real.rpow_le_rpow hxpos.le hx2 h1mβpos.le
    have h2 : (2*(q:ℝ)^N)^(1-β) = 2^(1-β) * ((q:ℝ)^N)^(1-β) :=
      Real.mul_rpow (by norm_num) (le_of_lt hqNpos)
    have h3 : (2:ℝ)^(1-β) ≤ 2 := by
      calc (2:ℝ)^(1-β) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : ((q:ℝ)^N)^(1-β) ≤ Real.exp ((N:ℝ)/10) := by
      rw [← Real.rpow_natCast (q:ℝ) N, ← Real.rpow_mul hqpos.le]
      exact hqNpow
    calc x^(1-β) ≤ (2*(q:ℝ)^N)^(1-β) := h1
      _ = 2^(1-β) * ((q:ℝ)^N)^(1-β) := h2
      _ ≤ 2 * Real.exp ((N:ℝ)/10) :=
          mul_le_mul h3 h4 (Real.rpow_nonneg (by positivity) _) (by norm_num)
  have hgoal : Real.exp (-((N:ℝ)/10))/4 * (1-β) ≤ (1/2) * ((1-β)*(2-β)/x^(1-β)) := by
    have hkey2 : Real.exp (-((N:ℝ)/10)) * x^(1-β) ≤ 2*(2-β) := by
      rw [Real.exp_neg]
      have h1 : (Real.exp ((N:ℝ)/10))⁻¹ * x^(1-β)
          ≤ (Real.exp ((N:ℝ)/10))⁻¹ * (2 * Real.exp ((N:ℝ)/10)) :=
        mul_le_mul_of_nonneg_left hxpow_le (by positivity)
      have h2 : (Real.exp ((N:ℝ)/10))⁻¹ * (2 * Real.exp ((N:ℝ)/10)) = 2 := by
        rw [mul_comm ((Real.exp ((N:ℝ)/10))⁻¹) (2 * Real.exp ((N:ℝ)/10)), mul_assoc,
          mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]
      linarith
    have step : Real.exp (-((N:ℝ)/10)) * (1-β) ≤ 2*(1-β)*(2-β)/x^(1-β) := by
      rw [le_div_iff₀ hxpowpos]
      calc Real.exp (-((N:ℝ)/10)) * (1-β) * x^(1-β)
          = (1-β) * (Real.exp (-((N:ℝ)/10)) * x^(1-β)) := by ring
        _ ≤ (1-β) * (2*(2-β)) := mul_le_mul_of_nonneg_left hkey2 h1mβpos.le
        _ = 2*(1-β)*(2-β) := by ring
    calc Real.exp (-((N:ℝ)/10))/4 * (1-β)
        = (1/4) * (Real.exp (-((N:ℝ)/10)) * (1-β)) := by ring
      _ ≤ (1/4) * (2*(1-β)*(2-β)/x^(1-β)) := mul_le_mul_of_nonneg_left step (by norm_num)
      _ = (1/2) * ((1-β)*(2-β)/x^(1-β)) := by ring
  exact le_trans hgoal hkey

end Work.LinnikAreas
