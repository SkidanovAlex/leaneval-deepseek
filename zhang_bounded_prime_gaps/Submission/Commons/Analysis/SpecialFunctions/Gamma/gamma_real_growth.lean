import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound

open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-!
# Polynomial-exponential growth of Γ on the real axis

We show there is a constant `c` such that for every real `σ ≥ 1`,
`‖Γ(σ)‖ ≤ exp (c · σ · log (σ + 2))`, where `Γ` is the complex Gamma function.

The proof is completely elementary:

* for `1 ≤ σ ≤ 2`, the functional equation `Γ(σ+1) = σ Γ(σ)` together with
  monotonicity of `Γ` on `[2, ∞)` gives `Γ(σ) ≤ Γ(σ+1) ≤ Γ 3 = 2`, and
  `2 ≤ exp (σ log (σ+2))` for `σ ≥ 1`;
* for `σ ≥ 2`, monotonicity on `[2, ∞)` reduces the bound to the integer
  `⌊σ⌋ + 1`, where `Γ (⌊σ⌋+1) = ⌊σ⌋! ≤ ⌊σ⌋^⌊σ⌋ ≤ σ^σ ≤ exp (σ log (σ+2))`.
-/

/-- On `[1, 2]` the Gamma function is bounded by `Γ 3 = 2` (via the functional
equation and monotonicity on `[2, ∞)`). -/
lemma real_gamma_le_two_of_le_two {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) :
    Real.Gamma σ ≤ 2 := by
  have hσpos : 0 < σ := by linarith
  have hΓrec : Real.Gamma (σ + 1) = σ * Real.Gamma σ :=
    Real.Gamma_add_one (by linarith : σ ≠ 0)
  have hmono : Real.Gamma (σ + 1) ≤ Real.Gamma 3 := by
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by simp only [Set.mem_Ici]; linarith)
      (by norm_num)
      (by linarith)
  have hG3 : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial (n := 2) using 1 <;> norm_num
  have hdiv : Real.Gamma (σ + 1) / σ = Real.Gamma σ := by
    rw [hΓrec]
    field_simp [ne_of_gt hσpos]
  have hle1 : Real.Gamma σ ≤ Real.Gamma 3 / σ := by
    rw [← hdiv]
    exact div_le_div_of_nonneg_right hmono (le_of_lt hσpos)
  have hle2 : Real.Gamma 3 / σ ≤ Real.Gamma 3 := by
    have hGpos : 0 ≤ Real.Gamma 3 := by
      rw [hG3]
      norm_num
    have hinv : σ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc
      Real.Gamma 3 / σ = Real.Gamma 3 * σ⁻¹ := by ring
      _ ≤ Real.Gamma 3 * 1 := by
        exact mul_le_mul_of_nonneg_left hinv hGpos
      _ = Real.Gamma 3 := by ring
  calc
    Real.Gamma σ ≤ Real.Gamma 3 / σ := hle1
    _ ≤ Real.Gamma 3 := hle2
    _ = 2 := hG3

/-- On `[1, 2]` the crude bound `2 ≤ exp (σ log (σ+2))` holds. -/
lemma two_le_exp_of_le_two {σ : ℝ} (h1 : 1 ≤ σ) :
    2 ≤ Real.exp (σ * Real.log (σ + 2)) := by
  have hlog3 : Real.log 3 ≤ Real.log (σ + 2) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hLpos : 0 < Real.log (σ + 2) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : 1 < (3 : ℝ))) hlog3
  have harg : Real.log 3 ≤ σ * Real.log (σ + 2) := by
    calc
      Real.log 3 ≤ Real.log (σ + 2) := hlog3
      _ = 1 * Real.log (σ + 2) := by ring
      _ ≤ σ * Real.log (σ + 2) := by
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt hLpos)
  calc
    2 ≤ Real.exp (Real.log 3) := by
      rw [Real.exp_log (by norm_num : 0 < (3 : ℝ))]
      norm_num
    _ ≤ Real.exp (σ * Real.log (σ + 2)) := Real.exp_le_exp.mpr harg

/-- On `[1, 2]` the claimed exponential bound holds for the real Gamma function. -/
lemma real_gamma_growth_small {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) :
    Real.Gamma σ ≤ Real.exp (σ * Real.log (σ + 2)) := by
  exact le_trans (real_gamma_le_two_of_le_two h1 h2) (two_le_exp_of_le_two h1)

/-- The `n! ≤ n^n` bound as an inequality between reals. -/
lemma factorial_le_pow_real (n : ℕ) : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast Nat.factorial_le_pow n

/-- For `σ ≥ 2`, the Gamma function is bounded by `σ^σ`: reduce by monotonicity
to the integer `⌊σ⌋ + 1`, where the bound is `⌊σ⌋! ≤ ⌊σ⌋^⌊σ⌋ ≤ σ^σ`. -/
lemma real_gamma_le_self_rpow {σ : ℝ} (h2 : 2 ≤ σ) :
    Real.Gamma σ ≤ σ ^ σ := by
  let n : ℕ := Nat.floor σ
  have hσpos : 0 < σ := by linarith
  have hσfloor : (n : ℝ) ≤ σ := by
    simpa [n] using Nat.floor_le (by linarith : 0 ≤ σ)
  have hσlt : σ < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one σ
  have hn : 1 ≤ n := by
    have hn2 : 2 ≤ n := by
      simpa [n] using (Nat.le_floor (by simpa using h2 : (2 : ℝ) ≤ σ))
    omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (by omega : 2 ≤ n + 1)
  have hmono : Real.Gamma σ ≤ Real.Gamma ((n : ℝ) + 1) := by
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by simpa using h2)
      (by simpa [Set.mem_Ici] using hn2R)
      (le_of_lt hσlt)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1σ : (1 : ℝ) ≤ σ := by linarith
  calc
    Real.Gamma σ ≤ Real.Gamma ((n : ℝ) + 1) := hmono
    _ = (n.factorial : ℝ) := by
      simpa using Real.Gamma_nat_eq_factorial n
    _ ≤ (n : ℝ) ^ n := factorial_le_pow_real n
    _ = (n : ℝ) ^ ((n : ℝ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ σ ^ (n : ℝ) := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ)) hσfloor
        (by positivity : 0 ≤ (n : ℝ))
    _ ≤ σ ^ σ := by
      exact Real.rpow_le_rpow_of_exponent_le h1σ hσfloor

/-- The main real-analytic bound: for every `σ ≥ 1`,
`Γ(σ) ≤ exp (σ log (σ+2))`. -/
lemma real_gamma_growth {σ : ℝ} (h1 : 1 ≤ σ) :
    Real.Gamma σ ≤ Real.exp (σ * Real.log (σ + 2)) := by
  by_cases h2 : σ ≤ 2
  · exact real_gamma_growth_small h1 h2
  · have hσ2 : 2 ≤ σ := by linarith
    have hσpos : 0 < σ := by linarith
    have h1σ : 1 ≤ σ := h1
    have hlogle : Real.log σ ≤ Real.log (σ + 2) := by
      exact Real.log_le_log hσpos (by linarith)
    calc
      Real.Gamma σ ≤ σ ^ σ := real_gamma_le_self_rpow hσ2
      _ = Real.exp (Real.log σ * σ) := by rw [Real.rpow_def_of_pos hσpos]
      _ ≤ Real.exp (σ * Real.log (σ + 2)) := by
        apply Real.exp_le_exp.mpr
        calc
          Real.log σ * σ ≤ Real.log (σ + 2) * σ := by
            exact mul_le_mul_of_nonneg_right hlogle (le_of_lt hσpos)
          _ = σ * Real.log (σ + 2) := by ring

/-- **Growth of the complex Gamma function on the real axis**: there is a
constant `c` such that for every `σ ≥ 1`,
`‖Γ(σ)‖ ≤ exp (c · σ · log (σ+2))`. -/
theorem gamma_real_growth :
    ∃ c : ℝ, ∀ σ : ℝ, 1 ≤ σ →
      ‖Complex.Gamma (σ : ℂ)‖ ≤ Real.exp (c * σ * Real.log (σ + 2)) := by
  refine ⟨1, ?_⟩
  intro σ hσ1
  have hΓpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos (by linarith)
  calc
    ‖Complex.Gamma (σ : ℂ)‖ = ‖(Real.Gamma σ : ℂ)‖ := by rw [Complex.Gamma_ofReal]
    _ = Real.Gamma σ := Complex.norm_of_nonneg hΓpos.le
    _ ≤ Real.exp (σ * Real.log (σ + 2)) := real_gamma_growth hσ1
    _ = Real.exp (1 * σ * Real.log (σ + 2)) := by
      congr 1
      ring

end Commons.Analysis.SpecialFunctions.Gamma
