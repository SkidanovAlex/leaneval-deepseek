import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.prod_formula_log
import Submission.Work.BW.logHeight_prod_zpow_le
import Submission.Work.BW.phi_prod_zpow_exp
import Submission.Work.BW.liouville_place

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# liouville_logForm — BW L3 (p. 25–26), ~400–800 lines, low risk

**Claim.** Take nonzero `αᵢ ∈ K`, arbitrary logarithms `ℓᵢ` (`exp ℓᵢ = φ αᵢ`), and `y ∈ ℤⁿ` with
`Λ = ∑ yᵢℓᵢ ≠ 0`. Then `log|Λ| ≥ -∑|yᵢ| h(αᵢ) - d log 2`, where `h = logHeight₁` is the relative height.

**Proof (BW p. 25).**
1. If `|Λ| ≥ log 2`, then `log|Λ| ≥ log log 2 > -log 2 ≥ -d log 2`.
2. Otherwise let `a = ∏ αᵢ^{yᵢ}` (zpow), so `φ a = exp Λ`.
   * If `a = 1`, then `Λ ∈ 2πiℤ \ {0}` and `|Λ| ≥ 2π`, a contradiction. So `a' = a - 1 ≠ 0`.
3. `|φ a'| = |e^Λ - 1| ≤ |Λ| e^{|Λ|}`.
4. Let `v₀` be the place of `φ`. The product formula (`NumberField.prod_abs_eq_one`) gives
   `mult(v₀)·log|φa'| = -∑_{v≠v₀} log|a'|_v ≥ -∑_{v≠v₀} log⁺|a'|_v`.
5. Bound `log⁺|a'|_v` by `log⁺|a|_v` at finite places, and by `log⁺|a|_v + mult(v)·log 2` at
   infinite places.
6. The bound from step 5 is at most `h(a) + (d - mult v₀) log 2`, and
   `h(a) ≤ ∑|yᵢ|h(αᵢ)` (`logHeight₁_zpow`, `logHeight₁_mul_le`).
7. Divide by `mult v₀ ≥ 1` and combine with step 3.
-/

namespace Work.BW

open Complex

/-- BW L3 (Liouville estimate), for arbitrary determinations `ℓᵢ` of `log φ(αᵢ)`:
`log|Λ| ≥ -∑ |yᵢ| h(αᵢ) - d log 2` with `h` the relative height. -/
theorem liouville_logForm {K : Type*} [Field K] [NumberField K] {n : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin n → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) (y : Fin n → ℤ)
    (hΛ : ∑ i, (y i : ℂ) * ℓ i ≠ 0) :
    Real.log ‖∑ i, (y i : ℂ) * ℓ i‖ ≥
      -(∑ i, ((y i).natAbs : ℝ) * Height.logHeight₁ (α i))
        - (Module.finrank ℚ K : ℝ) * Real.log 2 := by
  classical
  set Λ : ℂ := ∑ i, (y i : ℂ) * ℓ i with hΛdef
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hddef
  set H : ℝ := ∑ i, ((y i).natAbs : ℝ) * Height.logHeight₁ (α i) with hHdef
  have hΛne : Λ ≠ 0 := by rw [hΛdef]; exact hΛ
  have hd1 : (1 : ℝ) ≤ d := by
    rw [hddef]
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have hd0 : (0 : ℝ) ≤ d := le_trans zero_le_one hd1
  have hH0 : 0 ≤ H := by
    rw [hHdef]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt (Real.log 2) ‖Λ‖ with hbig | hsmall
  · -- Case 1: `log 2 ≤ ‖Λ‖`
    have h1 : Real.log (Real.log 2) ≤ Real.log ‖Λ‖ := Real.log_le_log hlog2 hbig
    have h2 : -Real.log 2 ≤ Real.log (Real.log 2) := by
      have h3 : Real.log ((1 : ℝ) / 2) ≤ Real.log (Real.log 2) :=
        Real.log_le_log (by norm_num) (by linarith [Real.log_two_gt_d9])
      rw [one_div, Real.log_inv] at h3
      exact h3
    have h4 : -d * Real.log 2 ≤ -Real.log 2 := by nlinarith
    linarith
  · -- Case 2: `‖Λ‖ < log 2`
    have hlog2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hnorm1 : ‖Λ‖ < 1 := lt_trans hsmall hlog2lt1
    let a : K := ∏ i, α i ^ y i
    have hφa : φ a = Complex.exp Λ := by
      change φ (∏ i, α i ^ y i) = Complex.exp Λ
      rw [hΛdef]
      exact phi_prod_zpow_exp φ α hα ℓ hℓ y
    -- `a ≠ 1`
    have hexp_ne : Complex.exp Λ - 1 ≠ 0 := by
      intro h
      have hexp1 : Complex.exp Λ = 1 := sub_eq_zero.mp h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hΛne (by rw [hk]; simp)
      have hknorm : ‖Λ‖ = |(k : ℝ)| * (2 * Real.pi) := by
        rw [hk]
        have h1 : (2 : ℂ) * (Real.pi : ℂ) * I = ((2 * Real.pi : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [h1, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Complex.norm_intCast, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hk0
      have h2 : (6 : ℝ) ≤ ‖Λ‖ := by rw [hknorm]; nlinarith [Real.pi_gt_three]
      linarith [Real.log_two_lt_d9]
    have hane1 : a ≠ 1 := by
      intro h
      rw [h, map_one] at hφa
      exact hexp_ne (by rw [← hφa, sub_self])
    -- the local Liouville estimate
    have hHa : Height.logHeight₁ a ≤ H := by
      change Height.logHeight₁ (∏ i, α i ^ y i) ≤ H
      rw [hHdef]
      exact logHeight_prod_zpow_le α y
    have hHa0 : 0 ≤ Height.logHeight₁ a := Height.zero_le_logHeight₁ a
    set m : ℝ := ((NumberField.InfinitePlace.mk φ).mult : ℝ) with hmdef
    have hm1 : (1 : ℝ) ≤ m := by
      rw [hmdef]
      have hpos : 0 < (NumberField.InfinitePlace.mk φ).mult :=
        NumberField.InfinitePlace.mult_pos
      have : 1 ≤ (NumberField.InfinitePlace.mk φ).mult := by omega
      exact_mod_cast this
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm1
    have hmd : m ≤ d := by
      rw [hmdef, hddef]
      have hsum : (NumberField.InfinitePlace.mk φ).mult ≤ Module.finrank ℚ K := by
        have h1 : (NumberField.InfinitePlace.mk φ).mult ≤
            ∑ v : NumberField.InfinitePlace K, v.mult :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        rwa [NumberField.InfinitePlace.sum_mult_eq] at h1
      exact_mod_cast hsum
    have hLI : m * Real.log ‖φ (a - 1)‖ ≥
        -(Height.logHeight₁ a + (d - m) * Real.log 2) := by
      have h := liouville_place φ a hane1
      rw [← hmdef, ← hddef] at h
      exact h
    have hK1 : Real.log ‖φ (a - 1)‖ ≥ -(H + (d - 1) * Real.log 2) := by
      have hA : Height.logHeight₁ a + (d - m) * Real.log 2 ≤
          (H + (d - 1) * Real.log 2) * m := by
        have h1 : Height.logHeight₁ a ≤ H * m := by nlinarith [hHa, hH0, hm1]
        have hdm : d - m ≤ (d - 1) * m := by nlinarith [hmd, hm1]
        have h2 : (d - m) * Real.log 2 ≤ ((d - 1) * m) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hdm (le_of_lt hlog2)
        have h3 : (H + (d - 1) * Real.log 2) * m = H * m + ((d - 1) * m) * Real.log 2 := by
          ring
        linarith
      have h2 : -(H + (d - 1) * Real.log 2) * m ≤ Real.log ‖φ (a - 1)‖ * m := by
        linarith
      exact le_of_mul_le_mul_right h2 hm0
    -- the exponential bound
    have hnorm_le : ‖Complex.exp Λ - 1‖ ≤ 2 * ‖Λ‖ :=
      Complex.norm_exp_sub_one_le (le_of_lt hnorm1)
    have hK2 : Real.log ‖Λ‖ ≥ Real.log ‖φ (a - 1)‖ - Real.log 2 := by
      have hsub : φ (a - 1) = Complex.exp Λ - 1 := by rw [map_sub, hφa, map_one]
      have h1 : Real.log ‖φ (a - 1)‖ ≤ Real.log (2 * ‖Λ‖) := by
        rw [hsub]
        exact Real.log_le_log (norm_pos_iff.mpr hexp_ne) hnorm_le
      have h2 : Real.log (2 * ‖Λ‖) = Real.log 2 + Real.log ‖Λ‖ :=
        Real.log_mul (by norm_num) (ne_of_gt (norm_pos_iff.mpr hΛne))
      linarith
    linarith

end Work.BW
