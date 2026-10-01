import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le

open Filter

namespace Commons.NumberTheory.Chebyshev

/-- Effective PNT for Chebyshev's `θ` with a log-power error term: for every `A > 0`
there is `x₀ ≥ 1` with `|θ t − t| ≤ t / (log t)^A` for all `t ≥ x₀`.

Derived from the de la Vallée Poussin estimate for `ψ`
(`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real`) together with the classical
bound `ψ − θ ≤ 1.099 √·` (`psi_sub_theta_eventually_le`); the latter is applied at
`⌊t⌋₊` and pulled back to real `t` via `psi_eq_psi_coe_floor`/`theta_eq_theta_coe_floor`.
The condition `√t = o(t / (log t)^A)` is Littlewood's `log = o(√·)` in the form
`isLittleO_log_rpow_rpow_atTop`. -/
theorem theta_abs_sub_id_le (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ t : ℝ, x₀ ≤ t →
      |Chebyshev.theta t - t| ≤ t / (Real.log t) ^ A := by
  obtain ⟨x₁, hx₁⟩ :=
    Commons.NumberTheory.Zeta.psi_sub_id_powLog_real (A + 1) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
  have hlittle : (fun t : ℝ => Real.log t ^ A) =o[Filter.atTop]
      (fun t : ℝ => t ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) A (by norm_num)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (Asymptotics.isLittleO_iff.mp hlittle (by norm_num : (0 : ℝ) < 1 / 2.199))
  refine ⟨max (max x₁ (max (Real.exp 4) T)) ((N : ℝ) + 1), ?_, ?_⟩
  · have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
    have h1 : Real.exp 4 ≤ max (max x₁ (max (Real.exp 4) T)) ((N : ℝ) + 1) :=
      le_trans (le_trans (le_max_left (Real.exp 4) T) (le_max_right x₁ _)) (le_max_left _ _)
    linarith
  · intro t ht
    have hx₁t : x₁ ≤ t := le_trans (le_trans (le_max_left x₁ _) (le_max_left _ _)) ht
    have hexp4t : Real.exp 4 ≤ t :=
      le_trans (le_trans (le_trans (le_max_left (Real.exp 4) T) (le_max_right x₁ _))
        (le_max_left _ _)) ht
    have hTt : T ≤ t :=
      le_trans (le_trans (le_trans (le_max_right (Real.exp 4) T) (le_max_right x₁ _))
        (le_max_left _ _)) ht
    have ht1 : 1 ≤ t := by
      have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith
    have htpos : 0 < t := by linarith
    have hlog4 : 4 ≤ Real.log t := by
      rw [← Real.log_exp 4]
      exact Real.log_le_log (Real.exp_pos 4) hexp4t
    have hlogpos : 0 < Real.log t := by linarith
    have hlogApos : 0 < (Real.log t) ^ A := Real.rpow_pos_of_pos hlogpos A
    have hψ := hx₁ t hx₁t
    have htN : (N : ℝ) + 1 ≤ t := le_trans (le_max_right _ _) ht
    have hfl : N ≤ ⌊t⌋₊ := Nat.le_floor (by linarith : (N : ℝ) ≤ t)
    have hsub : Chebyshev.psi t - Chebyshev.theta t ≤ 1.099 * Real.sqrt t := by
      rw [Chebyshev.psi_eq_psi_coe_floor t, Chebyshev.theta_eq_theta_coe_floor t]
      refine (hN ⌊t⌋₊ hfl).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast Nat.floor_le (le_of_lt htpos))) (by norm_num)
    have hsqrt : (Real.log t) ^ A ≤ (1 / 2.199) * Real.sqrt t := by
      have h := hT t hTt
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hlogpos) A),
        Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt htpos) (1 / 2 : ℝ))] at h
      rwa [Real.sqrt_eq_rpow]
    have hkey : 2.198 * Real.sqrt t ≤ t / (Real.log t) ^ A := by
      rw [le_div_iff₀ hlogApos]
      have haux : 2.198 * (Real.log t) ^ A ≤ Real.sqrt t := by nlinarith [hsqrt]
      nlinarith [haux, Real.sq_sqrt (le_of_lt htpos), Real.sqrt_nonneg t, hlogApos]
    have hsqrtle : 1.099 * Real.sqrt t ≤ (1 / 2) * (t / (Real.log t) ^ A) := by linarith
    have hψterm : t / (Real.log t) ^ (A + 1) ≤ (1 / 2) * (t / (Real.log t) ^ A) := by
      rw [Real.rpow_add hlogpos A 1, Real.rpow_one]
      have hdiv : 1 / Real.log t ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith)
      calc t / ((Real.log t) ^ A * Real.log t)
          = (t / (Real.log t) ^ A) * (1 / Real.log t) := by field_simp
        _ ≤ (t / (Real.log t) ^ A) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = (1 / 2) * (t / (Real.log t) ^ A) := by ring
    have hsplit : |Chebyshev.theta t - t|
        ≤ (Chebyshev.psi t - Chebyshev.theta t) + |Chebyshev.psi t - t| := by
      have hθψ : Chebyshev.theta t ≤ Chebyshev.psi t := Chebyshev.theta_le_psi t
      have hid : Chebyshev.theta t - t
          = (Chebyshev.theta t - Chebyshev.psi t) + (Chebyshev.psi t - t) := by ring
      rw [hid]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_of_nonpos (by linarith)]
      ring
    calc |Chebyshev.theta t - t|
        ≤ (Chebyshev.psi t - Chebyshev.theta t) + |Chebyshev.psi t - t| := hsplit
      _ ≤ (1 / 2) * (t / (Real.log t) ^ A) + (1 / 2) * (t / (Real.log t) ^ A) := by
          linarith [hsub, hsqrtle, hψ, hψterm]
      _ = t / (Real.log t) ^ A := by ring

/-- Effective PNT for Chebyshev's `θ` in its cleanest form, with constant `C = 1`:
there is `x₀ ≥ 2` such that `|θ t − t| ≤ t / log t` for all `t ≥ x₀`. -/
theorem theta_sub_id_le_log :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ t : ℝ, x₀ ≤ t →
      |Chebyshev.theta t - t| ≤ t / Real.log t := by
  obtain ⟨x₀, _hx₀1, hθ⟩ := theta_abs_sub_id_le 1 (by norm_num)
  refine ⟨max x₀ 2, le_max_right _ _, ?_⟩
  intro t ht
  have h := hθ t (le_trans (le_max_left _ _) ht)
  rwa [Real.rpow_one] at h

end Commons.NumberTheory.Chebyshev
