import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog

open Filter Asymptotics
open scoped Topology Nat.Prime

namespace Work.NumberTheory.Chen.BTermCount

/-!
# The sharp upper bound for `π`: `π(t) ≤ (1 + ε) t / log t` eventually

The Prime Number Theorem for the prime counting function, in the sharp *upper-bound* form.  The
constant `1` is the one given by the PNT (it is *not* Chebyshev's elementary constant `log 4`).

The proof only uses two ingredients:

* the sharp form of the PNT with a power-of-log error term, `θ x = x + O(x / (log x)^A)` for every
  `A > 0`, available in this workspace as
  `Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog`;
* Mathlib's `Chebyshev.primeCounting_sub_theta_div_log_isBigO`, which encodes
  `π ⌊x⌋₊ = θ x / log x + O(x / (log x)^2)` (Chebyshev's relation between `π` and `θ`, together
  with the trivial bound `θ t ≪ t` for the integral term).

Both error terms are `o(x / log x)`, so `π(x) ≤ (1 + ε) x / log x` for all large `x`, as claimed.
-/

/-- The sharp upper bound for the prime counting function, stated on the reals: for every
`ε > 0` and all large real `x`, `π ⌊x⌋₊ ≤ (1 + ε) x / log x`. -/
private lemma pi_counting_real_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1 + ε) * x / Real.log x := by
  -- `π ⌊x⌋₊ = θ x / log x + O(x / log² x)` (Mathlib).
  obtain ⟨C, hC⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.bound
  -- We may assume the implicit constant is nonnegative.
  set C' : ℝ := max C 0 with hC'def
  have hC'nn : 0 ≤ C' := le_max_right C 0
  have hCC' : C ≤ C' := le_max_left C 0
  have hε2 : 0 < ε / 2 := by linarith
  -- `θ x = x + O(x / log² x)` (the sharp PNT with `A = 2`).
  obtain ⟨x₀, hx₀⟩ := Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog 2 (by norm_num)
  -- We will take `x` so large that `log x ≥ max (√(2/ε)) (2C'/ε)` and `x ≥ 3`.
  set R : ℝ := max (Real.sqrt (2 / ε)) (2 * C' / ε) with hRdef
  filter_upwards [hC, Filter.eventually_ge_atTop (max x₀ 3),
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop R)] with x hCx hxge hlogR
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right x₀ 3) hxge
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : 0 < x := by linarith
  have hxle : x₀ ≤ x := le_trans (le_max_left x₀ 3) hxge
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlog2pos : 0 < Real.log x ^ 2 := by positivity
  -- `(log x)^2 ≥ 2/ε`.
  have hsq : 2 / ε ≤ Real.log x ^ 2 := by
    have h0 : (0 : ℝ) ≤ 2 / ε := by positivity
    have hs : Real.sqrt (2 / ε) ≤ Real.log x := le_trans (le_max_left _ _) hlogR
    have hsq2 : Real.sqrt (2 / ε) ^ 2 = 2 / ε := Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (2 / ε), hs, hsq2]
  -- `log x ≥ 2 C' / ε`.
  have htwoC : 2 * C' / ε ≤ Real.log x := le_trans (le_max_right _ _) hlogR
  -- The sharp bound `θ x ≤ (1 + ε/2) x`.
  have hθraw : |Chebyshev.theta x - x| ≤ x / Real.log x ^ 2 := by
    have h := hx₀ x hxle
    rwa [Real.rpow_two] at h
  have hθle : Chebyshev.theta x ≤ (1 + ε / 2) * x := by
    have h1 : Chebyshev.theta x - x ≤ x / Real.log x ^ 2 := le_trans (le_abs_self _) hθraw
    have h2 : x / Real.log x ^ 2 ≤ (ε / 2) * x := by
      rw [div_le_iff₀ hlog2pos]
      have h3 : (1 : ℝ) ≤ (ε / 2) * Real.log x ^ 2 := by
        have he : ε / 2 * (2 / ε) = 1 := by field_simp
        calc (1 : ℝ) = ε / 2 * (2 / ε) := he.symm
          _ ≤ ε / 2 * Real.log x ^ 2 := mul_le_mul_of_nonneg_left hsq (le_of_lt hε2)
      nlinarith
    linarith
  -- `π ⌊x⌋₊ ≤ θ x / log x + C' x / log² x`.
  have hCx' : (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x
      ≤ C' * (x / Real.log x ^ 2) := by
    have h1 : (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x
        ≤ ‖(Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x‖ := le_abs_self _
    have h2 : ‖(Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x‖
        ≤ C * ‖x / Real.log x ^ 2‖ := hCx
    have h4 : ‖x / Real.log x ^ 2‖ = x / Real.log x ^ 2 :=
      Real.norm_of_nonneg (by positivity)
    rw [h4] at h2
    have h3 : C * (x / Real.log x ^ 2) ≤ C' * (x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right hCC' (by positivity)
    linarith
  have hA : Chebyshev.theta x / Real.log x ≤ (1 + ε / 2) * x / Real.log x :=
    div_le_div_of_nonneg_right hθle hlogpos.le
  -- `C' x / log² x ≤ (ε/2) · x / log x`, since `C' / log x ≤ ε/2`.
  have hB : C' * (x / Real.log x ^ 2) ≤ (ε / 2) * (x / Real.log x) := by
    have hClog : C' / Real.log x ≤ ε / 2 := by
      rw [div_le_iff₀ hlogpos]
      have h := mul_le_mul_of_nonneg_left htwoC (le_of_lt hε2)
      have he : ε / 2 * (2 * C' / ε) = C' := by field_simp
      rwa [he] at h
    have hxdiv : 0 ≤ x / Real.log x := div_nonneg hx0.le hlogpos.le
    have heq : C' * (x / Real.log x ^ 2) = (C' / Real.log x) * (x / Real.log x) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hClog hxdiv
  calc (Nat.primeCounting ⌊x⌋₊ : ℝ)
      ≤ Chebyshev.theta x / Real.log x + C' * (x / Real.log x ^ 2) := by linarith
    _ ≤ (1 + ε / 2) * x / Real.log x + (ε / 2) * (x / Real.log x) := add_le_add hA hB
    _ = (1 + ε) * x / Real.log x := by field_simp; ring

/-- The Prime Number Theorem in the sharp upper-bound form for `π`: for every `ε > 0` and all
large `t`, the number of primes `≤ t` is at most `(1 + ε) t / log t`.

A proof can be assembled from the commons module
`Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog`, which gives
`|θ x − x| ≤ x / (log x)^A` for every `A > 0` and all large real `x` (where `θ` is Chebyshev's
theta function, `θ x = ∑_{p ≤ x} log p`).  Chebyshev's θ is related to `Nat.primesLE` by
`Chebyshev.theta_eq_sum_primesLE_log` (check the exact name in Mathlib).  From `θ(T) ≤ (1+δ)T`
one gets the sharp bound on `π` by a dyadic (or partial-summation) argument, since for
`p ∈ (T/2^{j+1}, T/2^j]` we have `log p ≥ log(T/2^{j+1})`, so the dyadic blocks contribute a
geometric series summing to `(1+o(1)) T / log T`. -/
theorem pi_upper_sharp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ((Nat.primesLE t).card : ℝ) ≤ (1 + ε) * (t : ℝ) / Real.log (t : ℝ) := by
  have h := pi_counting_real_upper ε hε
  -- Transfer the real statement along `ℕ → ℝ`.
  have h' : ∀ᶠ t : ℕ in Filter.atTop,
      (Nat.primeCounting ⌊(t : ℝ)⌋₊ : ℝ) ≤ (1 + ε) * (t : ℝ) / Real.log (t : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [h'] with t ht
  rw [Nat.floor_natCast] at ht
  rw [Nat.primesLE_card_eq_primeCounting]
  exact ht

end Work.NumberTheory.Chen.BTermCount
