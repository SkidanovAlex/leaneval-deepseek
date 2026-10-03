import Mathlib

namespace Work.KMTAreas.A7

open Filter Asymptotics

/-- The helper fact that `√x = o(x)` at `+∞`, proved directly from the epsilon definition
(so that it does not depend on any rpow asymptotics). -/
private lemma sqrt_isLittleO_id :
    (fun x : ℝ => Real.sqrt x) =o[atTop] (fun x : ℝ => x) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (max 1 (1 / c ^ 2))] with x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hcx : (1 : ℝ) ≤ c ^ 2 * x := by
    have hle : 1 / c ^ 2 ≤ x := le_trans (le_max_right _ _) hx
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    have := (div_le_iff₀ hc2).mp hle
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg hx0.le]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow]
  nlinarith [hcx, hx0]

lemma exists_sqrt_logb_lt (A B : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      A * Real.sqrt ((M : ℝ) + 2) + B * Real.logb 2 ((M : ℝ) + 2) + 1 < (M : ℝ) := by
  have hlogb : (fun x : ℝ => Real.logb 2 x) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_logb_id_atTop
  -- the whole left-hand side is `o(x)`
  have h : (fun x : ℝ => A * Real.sqrt x + B * Real.logb 2 x + 1) =o[atTop]
      (fun x : ℝ => x) :=
    ((sqrt_isLittleO_id.const_mul_left A).add (hlogb.const_mul_left B)).add
      (isLittleO_const_id_atTop 1)
  have hb := h.def (show (0 : ℝ) < 1 / 4 by norm_num)
  rw [eventually_atTop] at hb
  obtain ⟨a, ha⟩ := hb
  obtain ⟨M₀, hM₀⟩ := exists_nat_ge (max a 3)
  refine ⟨M₀, fun M hM => ?_⟩
  have hMM : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hge : max a 3 ≤ (M : ℝ) + 2 := by linarith
  have ha' : a ≤ (M : ℝ) + 2 := le_trans (le_max_left a 3) hge
  have h3 : (3 : ℝ) ≤ (M : ℝ) + 2 := le_trans (le_max_right a 3) hge
  have hb' := ha ((M : ℝ) + 2) ha'
  have hx0 : (0 : ℝ) ≤ (M : ℝ) + 2 := by linarith
  have hquarter : (1 / 4 : ℝ) * ((M : ℝ) + 2) < (M : ℝ) := by linarith
  have hle : A * Real.sqrt ((M : ℝ) + 2) + B * Real.logb 2 ((M : ℝ) + 2) + 1
      ≤ (1 / 4 : ℝ) * ((M : ℝ) + 2) := by
    calc A * Real.sqrt ((M : ℝ) + 2) + B * Real.logb 2 ((M : ℝ) + 2) + 1
        ≤ ‖A * Real.sqrt ((M : ℝ) + 2) + B * Real.logb 2 ((M : ℝ) + 2) + 1‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ (1 / 4 : ℝ) * ‖((M : ℝ) + 2)‖ := hb'
      _ = (1 / 4 : ℝ) * ((M : ℝ) + 2) := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]
  linarith

end Work.KMTAreas.A7
