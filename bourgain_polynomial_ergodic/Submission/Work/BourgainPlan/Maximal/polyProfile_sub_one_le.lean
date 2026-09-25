import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs

/-!
# The elementary Lipschitz bound for the polynomial profile

The profile of a polynomial `P ∈ ℤ[X]` at scale `N` is

  `Φ_N(β) = polyProfile P N β = ∫_0^1 exp(2πi β P(N s)) ds`,

so `Φ_N(0) = 1` and the phase in the exponent is `2π β P(N s)` with `|N s| ≤ N` for
`s ∈ [0,1]`.  Since `‖exp(iθ) - 1‖ ≤ |θ|` for real `θ`, and
`|P(x)| ≤ (∑_i |c_i|) N ^ deg P` for `|x| ≤ N`, `N ≥ 1`, we get the **Lipschitz bound**

  `‖Φ_N(β) - 1‖ ≤ 2π (∑_i |c_i|) |β| N^{deg P} ≤ 4π (∑_i |c_i|) |β| N^{deg P}`.

The factor `4π` (rather than `2π`) is the constant used by the callers; it is the reason the
bound is stated with `4`.

The main auxiliary facts are the pointwise bound `norm_polyProfileIntegrand_sub_one_le` and the
polynomial evaluation bound `abs_toRealPoly_eval_le`, both of which are reusable elsewhere.
-/

open Polynomial

namespace Work.BourgainPlan.Maximal

/-- **Evaluation bound for the real polynomial attached to `P`.**  If `1 ≤ R` and `|x| ≤ R` then
`|P(x)| ≤ (∑_{i ≤ deg P} |c_i|) R^{deg P}`. -/
lemma abs_toRealPoly_eval_le (P : Polynomial ℤ) {x R : ℝ} (hR : 1 ≤ R) (hx : |x| ≤ R) :
    |(toRealPoly P).eval x| ≤
      (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) * R ^ P.natDegree := by
  have hdeg : (toRealPoly P).natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
  have heval : (toRealPoly P).eval x =
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℝ) * x ^ i := by
    rw [Polynomial.eval_eq_sum_range' (p := toRealPoly P) (n := P.natDegree + 1) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [toRealPoly, Polynomial.coeff_map]
    rfl
  rw [heval]
  calc |∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℝ) * x ^ i|
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ) * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| * |x| ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| * R ^ P.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ P.natDegree := by
          have := Finset.mem_range.mp hi; omega
        exact mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ (abs_nonneg x) hx i)
          (pow_le_pow_right₀ hR hi')) (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) * R ^ P.natDegree := by
        rw [Finset.sum_mul]

/-- The integrand of the profile: `s ↦ exp(2πi β P(N s))`. -/
noncomputable def polyProfileIntegrand (P : Polynomial ℤ) (N : ℕ) (β : ℝ) : ℝ → ℂ :=
  fun s => Complex.exp (2 * Real.pi * Complex.I *
    ((β * Polynomial.eval ((N : ℝ) * s) (toRealPoly P) : ℝ) : ℂ))

/-- The profile is the integral of the integrand over `[0,1]`. -/
lemma polyProfile_eq_integral (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    polyProfile P N β = ∫ s in (0:ℝ)..1, polyProfileIntegrand P N β s := rfl

lemma continuous_polyProfileIntegrand (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    Continuous (polyProfileIntegrand P N β) := by
  unfold polyProfileIntegrand
  fun_prop

/-- Pointwise Lipschitz bound for the profile integrand: for `|s| ≤ 1` and `N ≥ 1`,
`‖exp(2πi β P(N s)) - 1‖ ≤ 2π (∑_i |c_i|) |β| N^{deg P}`. -/
lemma norm_polyProfileIntegrand_sub_one_le (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) (β : ℝ)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖polyProfileIntegrand P N β s - 1‖ ≤
      2 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
        * (|β| * (N : ℝ) ^ P.natDegree) := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hxs : |(N:ℝ) * s| ≤ (N:ℝ) := by
    rw [abs_mul, abs_of_nonneg hN0]
    nlinarith [hs, hN0]
  have hT : |(toRealPoly P).eval ((N:ℝ)*s)| ≤
      (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) * (N:ℝ)^P.natDegree :=
    abs_toRealPoly_eval_le P hNR hxs
  have hph : (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((β * Polynomial.eval ((N:ℝ)*s) (toRealPoly P) : ℝ) : ℂ)
      = Complex.I * (((2 * Real.pi * (β * Polynomial.eval ((N:ℝ)*s) (toRealPoly P)) : ℝ)) : ℂ) := by
    push_cast; ring
  have hkey : polyProfileIntegrand P N β s = Complex.exp (Complex.I *
      (((2 * Real.pi * (β * Polynomial.eval ((N:ℝ)*s) (toRealPoly P)) : ℝ)) : ℂ)) := by
    simp only [polyProfileIntegrand]; rw [hph]
  rw [hkey]
  have h1 : ‖Complex.exp (Complex.I * (((2 * Real.pi *
      (β * Polynomial.eval ((N:ℝ)*s) (toRealPoly P)) : ℝ)) : ℂ)) - 1‖
      ≤ |(2 * Real.pi * (β * Polynomial.eval ((N:ℝ)*s) (toRealPoly P)) : ℝ)| :=
    Real.norm_exp_I_mul_ofReal_sub_one_le
  refine h1.trans ?_
  have hnorm : |(2 * Real.pi * (β * Polynomial.eval ((N:ℝ)*s) (toRealPoly P)) : ℝ)|
      = 2 * Real.pi * |β| * |(toRealPoly P).eval ((N:ℝ)*s)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg Real.pi_nonneg,
      abs_mul]
    ring
  rw [hnorm]
  calc 2 * Real.pi * |β| * |(toRealPoly P).eval ((N:ℝ)*s)|
      ≤ 2 * Real.pi * |β| * ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
          * (N:ℝ)^P.natDegree) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 2 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
          * (|β| * (N:ℝ)^P.natDegree) := by ring

/-- **The profile is Lipschitz at the origin**: for `N ≥ 1`,
`‖Φ_N(β) - 1‖ ≤ 4π (∑_i |c_i|) |β| N^{deg P}`. -/
theorem polyProfile_sub_one_le (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    ‖polyProfile P N β - 1‖
      ≤ 4 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
          * (|β| * (N : ℝ) ^ P.natDegree) := by
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hint : IntervalIntegrable (polyProfileIntegrand P N β) MeasureTheory.volume (0:ℝ) 1 :=
    (continuous_polyProfileIntegrand P N β).intervalIntegrable _ _
  have hconst : (∫ s in (0:ℝ)..1, (1:ℂ)) = 1 := by
    rw [intervalIntegral.integral_const]; norm_num
  have hsub : polyProfile P N β - 1 =
      ∫ s in (0:ℝ)..1, (polyProfileIntegrand P N β s - 1) := by
    rw [polyProfile_eq_integral]
    nth_rewrite 1 [← hconst]
    rw [← intervalIntegral.integral_sub hint intervalIntegrable_const]
  rw [hsub]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * Real.pi *
      (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
        * (|β| * (N:ℝ)^P.natDegree)) ?_) ?_
  · intro s hs
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    have hs' : |s| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hs.1.le], hs.2⟩
    refine (norm_polyProfileIntegrand_sub_one_le P N hN β hs').trans ?_
    have hprod : 0 ≤ 2 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
        * (|β| * (N:ℝ)^P.natDegree) := by positivity
    linarith
  · rw [sub_zero, abs_one, mul_one]

end Work.BourgainPlan.Maximal
