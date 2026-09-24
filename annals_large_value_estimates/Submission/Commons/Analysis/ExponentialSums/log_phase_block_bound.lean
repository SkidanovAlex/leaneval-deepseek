import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

/-!
# Dyadic-block van der Corput (second derivative) bound for the log phase

For `2 ≤ M`, `1 ≤ t` we bound the exponential sum over the block `M < n ≤ 2M`
of `n^{−it} = exp(−i·t·log n)`:

    |Σ_{M<n≤2M} exp(−i·t·log n)| ≤ C·(√t + M/√t)

with an absolute constant `C`.  This is the second-derivative (van der Corput)
test: the phase `f(x) = −(t/(2π))·log x` has second derivative
`f''(x) = t/(2πx²) ∈ [t/(8πM²), t/(2πM²)] = [r, 4r]` on `[M, 2M]`, so the
two-sided second-derivative test `second_derivative_test` (ratio bound `B = 4`)
applies, and the bound `C·(N√r + 1/√r) = C·(√(t/(8π)) + √(8π)·M/√t)` is
dominated by `C·√(8π)·(√t + M/√t)`.
-/

open Complex Filter
open scoped Real BigOperators Topology Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Commons.Analysis.ExponentialSums

noncomputable section

/-- Phase with positive second derivative: the summand is `e(2π f(n)) = n^{−it}`
for `f(x) = −(t/(2π))·log x`. -/
def negLogPhase (t : ℝ) : ℝ → ℝ := fun x => -(t / (2 * Real.pi)) * Real.log x

/-- The two phase writings agree: `2π·(negLogPhase t x) = −(t·log x)`. -/
lemma negLogPhase_two_pi_mul {t x : ℝ} :
    2 * Real.pi * negLogPhase t x = -(t * Real.log x) := by
  unfold negLogPhase
  field_simp [Real.pi_ne_zero]

/-- `deriv (negLogPhase t) x = −(t/(2π))·x⁻¹` for `x ≠ 0`. -/
lemma deriv_negLogPhase {t x : ℝ} (hx : x ≠ 0) :
    deriv (negLogPhase t) x = -(t / (2 * Real.pi)) * x⁻¹ := by
  change deriv (fun y : ℝ => -(t / (2 * Real.pi)) * Real.log y) x = -(t / (2 * Real.pi)) * x⁻¹
  rw [deriv_const_mul (-(t / (2 * Real.pi))) (Real.differentiableAt_log hx)]
  rw [Real.deriv_log]

/-- `deriv (deriv (negLogPhase t)) x = (t/(2π))·(x^2)⁻¹` for `x ≠ 0`. -/
lemma deriv_deriv_negLogPhase {t x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (negLogPhase t)) x = (t / (2 * Real.pi)) * (x ^ 2)⁻¹ := by
  let c : ℝ := -(t / (2 * Real.pi))
  -- φ := deriv (negLogPhase t) agrees with y ↦ c·y⁻¹ on a punctured neighbourhood of x
  have hne : {y : ℝ | y ≠ 0} ∈ 𝓝 x := by
    exact (isOpen_ne (x := (0 : ℝ))).mem_nhds (by simpa using hx)
  have hφ : (fun y : ℝ => c * y⁻¹) =ᶠ[𝓝 x] deriv (negLogPhase t) := by
    filter_upwards [hne]
    intro y hy
    dsimp [c]
    exact (deriv_negLogPhase (t := t) hy).symm
  -- derivative of y ↦ c·y⁻¹ at x
  have hdlog : DifferentiableAt ℝ (fun y : ℝ => y⁻¹) x := by
    exact differentiableAt_inv (𝕜 := ℝ) hx
  have hdv : deriv (fun y : ℝ => c * y⁻¹) x = c * (-(x ^ 2)⁻¹) := by
    rw [deriv_const_mul (c := c) hdlog]
    rw [deriv_inv]
  calc
    deriv (deriv (negLogPhase t)) x
        = deriv (fun y : ℝ => c * y⁻¹) x := (Filter.EventuallyEq.deriv_eq hφ).symm
    _ = c * (-(x ^ 2)⁻¹) := hdv
    _ = (t / (2 * Real.pi)) * (x ^ 2)⁻¹ := by
          dsimp [c]
          ring

/-- `negLogPhase t` is `C²` on any set on which `x ≠ 0` everywhere. -/
lemma contDiffOn_negLogPhase {t : ℝ} {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContDiffOn ℝ 2 (negLogPhase t) s := by
  have hlog : ContDiffOn ℝ 2 Real.log s := by
    refine ContDiffOn.mono Real.contDiffOn_log ?_
    intro x hx
    simpa [Set.compl_singleton_eq] using hs x hx
  have hconst : ContDiffOn ℝ 2 (fun _ : ℝ => (-(t / (2 * Real.pi)) : ℝ)) s := contDiffOn_const
  change ContDiffOn ℝ 2 (fun x : ℝ => (-(t / (2 * Real.pi)) : ℝ) * Real.log x) s
  exact ContDiffOn.mul hconst hlog

/-- Pointwise lower+upper bound on the second derivative of the log phase on the
interval `(M, M+M)`: `r ≤ f'' ≤ 4r` with `r := t/(8πM²)`. -/
lemma second_deriv_two_sided {t : ℝ} (_ht : 1 ≤ t) {M : ℕ} (_hM : 2 ≤ M) :
    ∀ x : ℝ, x ∈ Set.Ioo (M : ℝ) ((M : ℝ) + (M : ℝ)) →
      (t / (8 * Real.pi * (M : ℝ) ^ 2)) ≤ deriv (deriv (negLogPhase t)) x ∧
      deriv (deriv (negLogPhase t)) x ≤ 4 * (t / (8 * Real.pi * (M : ℝ) ^ 2)) := by
  intro x hx
  have hMt0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hxm : (M : ℝ) < x := (Set.mem_Ioo.mp hx).1
  have hx2m : x < (M : ℝ) + (M : ℝ) := (Set.mem_Ioo.mp hx).2
  have hx0 : x ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hMt0 (le_of_lt hxm))
  have hval := deriv_deriv_negLogPhase (t := t) (x := x) hx0
  have hxpos : 0 < x := lt_of_lt_of_le hMt0 (le_of_lt hxm)
  have hm2pos : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMt0
  have hx2pos : 0 < x ^ 2 := sq_pos_of_pos hxpos
  have hsq_le : (M : ℝ) ^ 2 ≤ x ^ 2 := by
    have hxge : (M : ℝ) ≤ x := le_of_lt hxm
    have hf : 0 ≤ (x - (M : ℝ)) * (x + (M : ℝ)) := by
      exact mul_nonneg (sub_nonneg.mpr hxge) (add_nonneg hxpos.le hMt0.le)
    nlinarith
  have hxle : x ≤ 2 * (M : ℝ) := by
    nlinarith
  have hsq_ge : x ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by
    have hf : 0 ≤ (2 * (M : ℝ) - x) * (2 * (M : ℝ) + x) := by
      exact mul_nonneg (sub_nonneg.mpr hxle) (add_nonneg (mul_nonneg (by norm_num) (le_of_lt hMt0)) hxpos.le)
    nlinarith
  constructor
  · rw [hval]
    -- t/(2π) · 1/x² ≥ t/(8πM²) : it suffices 1/x² ≥ 1/(4M²)
    have h4m2pos : 0 < 4 * (M : ℝ) ^ 2 := by positivity
    have hinv : (4 * (M : ℝ) ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ := by
      exact (inv_le_inv₀ h4m2pos hx2pos).mpr hsq_ge
    have hc : (t / (2 * Real.pi)) * (4 * (M : ℝ) ^ 2)⁻¹ = t / (8 * Real.pi * (M : ℝ) ^ 2) := by
      field_simp [Real.pi_ne_zero, pow_ne_zero 2 hMt0.ne']
      ring
    have hmain : (t / (2 * Real.pi)) * (x ^ 2)⁻¹ ≥ t / (8 * Real.pi * (M : ℝ) ^ 2) := by
      rw [← hc]
      exact mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ t / (2 * Real.pi))
    exact hmain
  · rw [hval]
    -- t/(2π)·1/x² ≤ 4·t/(8πM²) : it suffices 1/x² ≤ 1/M²
    have hinv : (x ^ 2)⁻¹ ≤ ((M : ℝ) ^ 2)⁻¹ := by
      exact (inv_le_inv₀ hx2pos hm2pos).mpr hsq_le
    have hc : (t / (2 * Real.pi)) * ((M : ℝ) ^ 2)⁻¹ = 4 * (t / (8 * Real.pi * (M : ℝ) ^ 2)) := by
      field_simp [Real.pi_ne_zero, pow_ne_zero 2 hMt0.ne']
      ring
    have hmain : (t / (2 * Real.pi)) * (x ^ 2)⁻¹ ≤ 4 * (t / (8 * Real.pi * (M : ℝ) ^ 2)) := by
      rw [← hc]
      exact mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ t / (2 * Real.pi))
    exact hmain

/-- Second-derivative (van der Corput) bound for the block `M < n ≤ 2M` of the
log-phase exponential sum `Σ n^{−it}`: for `M ≥ 2`, `t ≥ 1`,

    |Σ_{M<n≤2M} exp(−i·t·log n)| ≤ C·(√t + M/√t)

with an absolute constant `C`.  (Note the summand
`cexp(((−(t·log n) : ℝ) : ℂ)·I) = n^{−it}`.) -/
theorem log_phase_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (_hM : 2 ≤ M) (t : ℝ) (_ht : 1 ≤ t),
      ‖∑ n ∈ Finset.Icc ((M : ℤ) + 1) (2 * (M : ℤ)),
          cexp ((((-(t * Real.log (n : ℝ))) : ℝ) : ℂ) * I)‖
        ≤ C * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  classical
  obtain ⟨C4, hC4pos, hSdt⟩ :=
    second_derivative_test (B := 4) (by norm_num : (1 : ℝ) ≤ 4)
  refine ⟨C4 * Real.sqrt (8 * Real.pi), by positivity, ?_⟩
  intro M _hM t _ht
  have hM1 : (1 : ℕ) ≤ M := by omega
  have hMt0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  let r : ℝ := t / (8 * Real.pi * (M : ℝ) ^ 2)
  have hr : 0 < r := by
    dsimp [r]
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) _ht
    positivity
  have hfC : ContDiffOn ℝ 2 (negLogPhase t) (Set.Icc (M : ℝ) ((M : ℝ) + (M : ℝ))) := by
    refine contDiffOn_negLogPhase ?_
    intro x hx
    have hxM : (M : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    exact ne_of_gt (lt_of_lt_of_le hMt0 hxM)
  have hpp : ∀ x : ℝ, x ∈ Set.Ioo (M : ℝ) ((M : ℝ) + (M : ℝ)) →
      r ≤ deriv (deriv (negLogPhase t)) x ∧ deriv (deriv (negLogPhase t)) x ≤ 4 * r := by
    intro x hx
    have hb := second_deriv_two_sided (t := t) _ht (M := M) _hM x hx
    dsimp [r] at hb ⊢
    exact hb
  have hs := hSdt (a := (M : ℤ)) (N := M) (by exact_mod_cast hM1) (negLogPhase t) (r := r) hr hfC hpp
  -- hs : ‖∑ n ∈ Icc (↑M + 1) (↑M + ↑M), cexp (2π·negLogPhase t n · I)‖ ≤ C4·(M√r + 1/√r)
  have hIcc : Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (M : ℤ)) =
      Finset.Icc ((M : ℤ) + 1) (2 * (M : ℤ)) := by
    ext n
    simp
    omega
  rw [hIcc] at hs
  -- the summand in our statement equals the summand in the derivative-test statement
  have hsum_eq :
      (∑ n ∈ Finset.Icc ((M : ℤ) + 1) (2 * (M : ℤ)),
          cexp ((((-(t * Real.log (n : ℝ))) : ℝ) : ℂ) * I)) =
      (∑ n ∈ Finset.Icc ((M : ℤ) + 1) (2 * (M : ℤ)),
          cexp ((((2 * Real.pi * negLogPhase t (n : ℝ)) : ℝ) : ℂ) * I)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    congr 2
    exact congrArg (fun y : ℝ => (y : ℂ)) (negLogPhase_two_pi_mul (t := t) (x := (n : ℝ))).symm
  have hnorm :
      ‖∑ n ∈ Finset.Icc ((M : ℤ) + 1) (2 * (M : ℤ)),
          cexp ((((-(t * Real.log (n : ℝ))) : ℝ) : ℂ) * I)‖
        ≤ C4 * ((M : ℝ) * Real.sqrt r + 1 / Real.sqrt r) := by
    rw [hsum_eq]
    exact hs
  -- bound: C4·(M√r + 1/√r) ≤ C4·√(8π)·(√t + M/√t)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) _ht
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos_of_pos ht0
  have h8ge : (1 : ℝ) ≤ Real.sqrt (8 * Real.pi) := by
    have hm : Real.sqrt (1 : ℝ) ≤ Real.sqrt (8 * Real.pi) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    simpa using hm
  have hsqrt : Real.sqrt r = Real.sqrt t / (Real.sqrt (8 * Real.pi) * (M : ℝ)) := by
    have hsqrt_main : Real.sqrt (8 * Real.pi * (M : ℝ) ^ 2) =
        Real.sqrt (8 * Real.pi) * (M : ℝ) := by
      calc
        Real.sqrt (8 * Real.pi * (M : ℝ) ^ 2)
            = Real.sqrt (8 * Real.pi) * Real.sqrt ((M : ℝ) ^ 2) :=
              Real.sqrt_mul (by positivity : 0 ≤ 8 * Real.pi) ((M : ℝ) ^ 2)
        _ = Real.sqrt (8 * Real.pi) * (M : ℝ) := by
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hMt0)]
    dsimp [r]
    calc
      Real.sqrt (t / (8 * Real.pi * (M : ℝ) ^ 2))
          = Real.sqrt t / Real.sqrt (8 * Real.pi * (M : ℝ) ^ 2) :=
            Real.sqrt_div (le_of_lt ht0) _
      _ = Real.sqrt t / (Real.sqrt (8 * Real.pi) * (M : ℝ)) := by rw [hsqrt_main]
  have hAeq : (M : ℝ) * Real.sqrt r = Real.sqrt t / Real.sqrt (8 * Real.pi) := by
    rw [hsqrt]
    field_simp [hMt0.ne']
  have hA : (M : ℝ) * Real.sqrt r ≤ Real.sqrt t := by
    rw [hAeq]
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by positivity : 0 < 8 * Real.pi))]
    have h1 : Real.sqrt t ≤ Real.sqrt (8 * Real.pi) * Real.sqrt t := by
      simpa using mul_le_mul_of_nonneg_right h8ge (Real.sqrt_nonneg t)
    nlinarith
  have hBeq : 1 / Real.sqrt r = Real.sqrt (8 * Real.pi) * (M : ℝ) / Real.sqrt t := by
    rw [hsqrt]
    field_simp [hsqrtpos.ne', hMt0.ne']
  have hB : 1 / Real.sqrt r ≤ Real.sqrt (8 * Real.pi) * ((M : ℝ) / Real.sqrt t) := by
    rw [hBeq]
    have hEq : Real.sqrt (8 * Real.pi) * (M : ℝ) / Real.sqrt t =
        Real.sqrt (8 * Real.pi) * ((M : ℝ) / Real.sqrt t) := by
      rw [mul_div_assoc]
    exact le_of_eq hEq
  have hA2 : Real.sqrt t ≤ Real.sqrt (8 * Real.pi) * Real.sqrt t := by
    simpa using mul_le_mul_of_nonneg_right h8ge (Real.sqrt_nonneg t)
  have hsum : (M : ℝ) * Real.sqrt r + 1 / Real.sqrt r ≤
      Real.sqrt (8 * Real.pi) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
    have hMsqrt : 0 ≤ Real.sqrt (8 * Real.pi) * ((M : ℝ) / Real.sqrt t) := by positivity
    nlinarith [hA, hB, hA2]
  have hb2 : C4 * ((M : ℝ) * Real.sqrt r + 1 / Real.sqrt r) ≤
      (C4 * Real.sqrt (8 * Real.pi)) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
    calc
      C4 * ((M : ℝ) * Real.sqrt r + 1 / Real.sqrt r)
          ≤ C4 * (Real.sqrt (8 * Real.pi) * (Real.sqrt t + (M : ℝ) / Real.sqrt t)) :=
            mul_le_mul_of_nonneg_left hsum (le_of_lt hC4pos)
      _ = (C4 * Real.sqrt (8 * Real.pi)) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by ring
  exact le_trans hnorm hb2

end
end Commons.Analysis.ExponentialSums
