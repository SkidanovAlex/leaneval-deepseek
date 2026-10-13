/-
# Row 19: the weighted derivative bound for the radial factor `H₂(z) = 2z²(1-z)/(1+z)⁴`

The pointwise `η`- and `γ`-families of row 19
(`Submission/Work/FTS/Nonlinear/Open/Row19Prep/{EtaPt,GamPt}.lean`) need, for every
`j ≤ m ≤ 4`, the bound

  `(1+z)·w(z)·z^m/(1+z)^{m-j} · |∂_z^j H₂(z)| ≤ C`,   `w(z) = (1+z)²/z²`, `z > 0`.

Since `(1+z)·w(z) = (1+z)³/z²`, the quantity is `(1+z)³z^{m-2}(1+z)^{-(m-j)}|∂_z^jH₂|`: the
`z^{-2}` of the weight at the origin is exactly cancelled by the double zero of `H₂` there.

## The route

With `u := (1+z)⁻¹`, `H₂` has the partial fractions

  `H₂(z) = -2u + 8u² - 10u³ + 4u⁴`

(the expansion of `-2z³+2z²` in powers of `u`; valid *everywhere*, since Lean's `0⁻¹ = 0`
makes both sides vanish at `z = -1`).  Writing `P_k(j) := ∏_{i<j}(k+i)`,

  `∂_z^j H₂(z) = (-1)^j·(-2P₁(j)u^{j+1} + 8P₂(j)u^{j+2} - 10P₃(j)u^{j+3} + 4P₄(j)u^{j+4})`

(`deriv_iter_H2b`, by induction from `∂_z u = -u²` and `P_k(j+1) = (k+j)P_k(j)`).  Hence for
`j ≤ 4`, `z ≥ 0` (so that `u ∈ [0,1]`) and `|P_k(j)| ≤ 8^j` (since `k ≤ 4`, `i < j ≤ 4`),

  `|∂_z^j H₂(z)| ≤ 10^5·u^{j+1}`

(`abs_deriv_iter_H2b_le`).  Multiplying by the weight `(1+z)³z^{m-2}u^{m-j}` gives, for
`m ≥ 2`,

  `(1+z)w(z)z^m/(1+z)^{m-j}·|∂_z^jH₂| ≤ 10^5·z^{m-2}u^{m-2} = 10^5(z/(1+z))^{m-2} ≤ 10^5`,

while the cases `m ≤ 1` (where `j ≤ m ≤ 1`) are elementary: `(1+z)w(z)|H₂| ≤ 2` for `m = 0`
(`one_add_mul_w_mul_abs_H2b_le`), the same bound times `z/(1+z) ≤ 1` for `m = 1, j = 0`, and
`(1+z)w(z)z|H₂'| = 2|2-5z+z²|/(1+z)² ≤ 10` for `m = j = 1` (`H2b_deriv`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row19Prep

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The derivative of an inverse power -/

/-- `∂_z (c·(1+z)^{-N}) = -c·N·(1+z)^{-(N+1)}` for `z > -1`. -/
theorem deriv_inv_pow (N : ℕ) (c z : ℝ) (hz : 0 < 1 + z) :
    deriv (fun t : ℝ => c * ((1 + t)⁻¹) ^ N) z = -c * (N : ℝ) * ((1 + z)⁻¹) ^ (N + 1) := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
    simpa using (hasDerivAt_id z).const_add (1 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hv := h1.inv (ne_of_gt hz)
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rw [hval] at hv
    exact hv
  have h3 : HasDerivAt (fun t : ℝ => ((1 + t)⁻¹) ^ N)
      ((N : ℝ) * ((1 + z)⁻¹) ^ (N - 1) * (-((1 + z)⁻¹) ^ 2)) z := h2.pow N
  have h4 := h3.const_mul c
  rw [h4.deriv]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hp : ((1 + z)⁻¹) ^ (N - 1) * ((1 + z)⁻¹) ^ 2 = ((1 + z)⁻¹) ^ (N + 1) := by
      rw [← pow_add, show N - 1 + 2 = N + 1 by omega]
    rw [show (N : ℝ) * ((1 + z)⁻¹) ^ (N - 1) * (-((1 + z)⁻¹) ^ 2)
        = -((N : ℝ) * (((1 + z)⁻¹) ^ (N - 1) * ((1 + z)⁻¹) ^ 2)) by ring, hp]
    ring

/-! ## The partial fractions and the derivative chain -/

/-- `P_k(j) = ∏_{i<j}(k+i)`. -/
def Pk (k j : ℕ) : ℝ := ∏ i ∈ Finset.range j, ((k : ℝ) + i)

theorem Pk_succ (k j : ℕ) : Pk k (j + 1) = Pk k j * ((k : ℝ) + j) := by
  rw [Pk, Pk, Finset.prod_range_succ]

/-- The closed form of `∂_z^j H₂` (as a function): `j`-th derivative of the four-term partial
fraction expansion of `H₂`. -/
def Sfun (j : ℕ) : ℝ → ℝ := fun z =>
  ((Pk 1 j * (-2)) * ((1 + z)⁻¹) ^ (j + 1) + (Pk 2 j * 8) * ((1 + z)⁻¹) ^ (j + 2))
    + ((Pk 3 j * (-10)) * ((1 + z)⁻¹) ^ (j + 3) + (Pk 4 j * 4) * ((1 + z)⁻¹) ^ (j + 4))

/-- The closed form of `∂_z^j H₂`, with the sign of the `j`-th derivative pulled out. -/
def FB (j : ℕ) : ℝ → ℝ := fun z => (-1) ^ j * Sfun j z

/-- The derivative chain `∂_z (FB j) = FB (j+1)` for `z > -1`. -/
theorem deriv_FB (j : ℕ) {z : ℝ} (hz : 0 < 1 + z) : deriv (FB j) z = FB (j + 1) z := by
  have hz1 : (1 + z) ≠ 0 := ne_of_gt hz
  have hsum : Sfun j = ((fun t : ℝ => (Pk 1 j * (-2)) * ((1 + t)⁻¹) ^ (j + 1))
      + (fun t : ℝ => (Pk 2 j * 8) * ((1 + t)⁻¹) ^ (j + 2)))
      + ((fun t : ℝ => (Pk 3 j * (-10)) * ((1 + t)⁻¹) ^ (j + 3))
        + (fun t : ℝ => (Pk 4 j * 4) * ((1 + t)⁻¹) ^ (j + 4))) := rfl
  have hdS : DifferentiableAt ℝ (Sfun j) z := by
    rw [hsum]; fun_prop
  have hD : ∀ (k : ℕ) (C : ℝ), deriv (fun t : ℝ => C * ((1 + t)⁻¹) ^ (j + k)) z
      = -C * ((j + k : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + k + 1) := fun k C =>
    deriv_inv_pow (j + k) C z hz
  have hS : deriv (Sfun j) z
      = -(Pk 1 j * (-2)) * ((j + 1 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 1 + 1)
        + (-(Pk 2 j * 8) * ((j + 2 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 2 + 1)
        + (-(Pk 3 j * (-10)) * ((j + 3 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 3 + 1)
        + (-(Pk 4 j * 4) * ((j + 4 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 4 + 1)))) := by
    rw [hsum, deriv_add (by fun_prop) (by fun_prop),
      deriv_add (by fun_prop) (by fun_prop),
      deriv_add (by fun_prop) (by fun_prop),
      hD 1 (Pk 1 j * (-2)), hD 2 (Pk 2 j * 8), hD 3 (Pk 3 j * (-10)),
      hD 4 (Pk 4 j * 4)]
    ring
  have hFB : deriv (FB j) z = (-1) ^ j * deriv (Sfun j) z := by
    rw [show FB j = fun t : ℝ => (-1) ^ j * Sfun j t from rfl]
    exact deriv_const_mul ((-1) ^ j) hdS
  rw [hFB, hS]
  rw [show (FB (j + 1)) z = (-1) ^ (j + 1) * Sfun (j + 1) z from rfl]
  simp only [Sfun]
  rw [Pk_succ 1 j, Pk_succ 2 j, Pk_succ 3 j, Pk_succ 4 j, pow_succ]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  push_cast
  ring

/-- `∂_z^j H₂ = FB j` for `z > -1`. -/
theorem deriv_iter_H2b (j : ℕ) {z : ℝ} (hz : 0 < 1 + z) : deriv^[j] H2b z = FB j z := by
  induction j generalizing z with
  | zero =>
      show H2b z = FB 0 z
      rw [H2b]
      simp only [FB, Sfun, Pk, Finset.prod_range_zero]
      norm_num
      by_cases h : 1 + z = 0
      · rw [h]; simp
      · field_simp
        ring
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hev : (deriv^[j] H2b) =ᶠ[𝓝 z] (FB j) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (-1 : ℝ) < z by linarith)] with t ht
        have ht' : (0 : ℝ) < 1 + t := by
          have h := ht; rw [Set.mem_Ioi] at h; linarith
        exact ih ht'
      rw [hev.deriv_eq]
      exact deriv_FB j hz

/-! ## The bound `|∂_z^j H₂| ≤ 10^5·(1+z)^{-(j+1)}` -/

/-- `|P_k(j)| ≤ 8^j` for `k ≤ 4`, `j ≤ 4`. -/
theorem abs_Pk_le {k j : ℕ} (hk : k ≤ 4) (hj : j ≤ 4) : |Pk k j| ≤ (8 : ℝ) ^ j := by
  induction j with
  | zero => simp [Pk]
  | succ j ih =>
      have hj' : j ≤ 4 := by omega
      have h1 : |((k : ℝ) + j)| ≤ 8 := by
        have h2 : k + j ≤ 8 := by omega
        have h3 : (k : ℝ) + j ≤ 8 := by exact_mod_cast h2
        rw [abs_of_nonneg (by positivity)]
        exact h3
      have ih' : |Pk k j| ≤ (8 : ℝ) ^ j := ih hj'
      rw [Pk] at ih' ⊢
      rw [Finset.abs_prod] at ih' ⊢
      rw [Finset.prod_range_succ, pow_succ]
      exact mul_le_mul ih' h1 (abs_nonneg _) (by positivity)

/-- `|∂_z^j H₂(z)| ≤ 10^5·(1+z)^{-(j+1)}` for `j ≤ 4` and `z ≥ 0`. -/
theorem abs_deriv_iter_H2b_le {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 0 ≤ z) :
    |deriv^[j] H2b z| ≤ 10 ^ 6 * ((1 + z)⁻¹) ^ (j + 1) := by
  have hz1 : 0 < 1 + z := by linarith
  have hu0 : 0 ≤ (1 + z)⁻¹ := by positivity
  have hu1 : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1:ℝ) ≤ 1 + z)
  have h8 : ∀ k : ℕ, k ≤ 4 → |Pk k j| ≤ 10 ^ 4 := fun k hk =>
    le_trans (abs_Pk_le hk hj)
      (le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hj) (by norm_num))
  have hpow : ∀ n : ℕ, 1 ≤ n → ((1 + z)⁻¹) ^ (j + n) ≤ ((1 + z)⁻¹) ^ (j + 1) := fun n hn =>
    pow_le_pow_of_le_one hu0 hu1 (by omega)
  have hp0 : (0:ℝ) ≤ ((1 + z)⁻¹) ^ (j + 1) := pow_nonneg hu0 _
  rw [deriv_iter_H2b j hz1, FB]
  simp only [Sfun]
  have e1 : |Pk 1 j * (-2) * ((1 + z)⁻¹) ^ (j + 1)| ≤ 2 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hp0]
    have h := h8 1 (by norm_num)
    nlinarith [h, hp0]
  have e2 : |Pk 2 j * 8 * ((1 + z)⁻¹) ^ (j + 2)| ≤ 8 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8),
      abs_of_nonneg (pow_nonneg hu0 (j + 2))]
    have h := h8 2 (by norm_num)
    have h2 := hpow 2 (by norm_num)
    nlinarith [h, h2, hp0, abs_nonneg (Pk 2 j), pow_nonneg hu0 (j + 2)]
  have e3 : |Pk 3 j * (-10) * ((1 + z)⁻¹) ^ (j + 3)| ≤ 10 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10),
      abs_of_nonneg (pow_nonneg hu0 (j + 3))]
    have h := h8 3 (by norm_num)
    have h2 := hpow 3 (by norm_num)
    nlinarith [h, h2, hp0, abs_nonneg (Pk 3 j), pow_nonneg hu0 (j + 3)]
  have e4 : |Pk 4 j * 4 * ((1 + z)⁻¹) ^ (j + 4)| ≤ 4 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
      abs_of_nonneg (pow_nonneg hu0 (j + 4))]
    have h := h8 4 (by norm_num)
    have h2 := hpow 4 (by norm_num)
    nlinarith [h, h2, hp0, abs_nonneg (Pk 4 j), pow_nonneg hu0 (j + 4)]
  have e0 : |(-1 : ℝ) ^ j| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_mul, e0, one_mul]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) (abs_add_le _ _)) ?_
  have hsum : (|Pk 1 j * (-2) * ((1 + z)⁻¹) ^ (j + 1)|
        + |Pk 2 j * 8 * ((1 + z)⁻¹) ^ (j + 2)|)
      + (|Pk 3 j * (-10) * ((1 + z)⁻¹) ^ (j + 3)|
        + |Pk 4 j * 4 * ((1 + z)⁻¹) ^ (j + 4)|)
      ≤ 24 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    have hnn : (0:ℝ) ≤ 10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1) := mul_nonneg (by norm_num) hp0
    nlinarith [e1, e2, e3, e4]
  refine le_trans hsum ?_
  have hnn : (0:ℝ) ≤ 10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1) := mul_nonneg (by norm_num) hp0
  nlinarith [hnn]

/-! ## The value of `∂_z H₂` -/

/-- `∂_z H₂(z) = 2z(2-5z+z²)/(1+z)⁵` for `z > -1`. -/
theorem H2b_deriv {z : ℝ} (hz : 0 < 1 + z) :
    deriv H2b z = 2 * z * (2 - 5 * z + z ^ 2) / (1 + z) ^ 5 := by
  have h := deriv_iter_H2b 1 hz
  rw [Function.iterate_one] at h
  rw [h]
  simp only [FB, Sfun, Pk, Finset.range_one, Finset.prod_singleton]
  norm_num
  field_simp
  ring

/-! ## The weighted bound -/

theorem H2b_weight_le : ∃ C : ℝ, 0 < C ∧ ∀ (m j : ℕ), m ≤ 4 → j ≤ m → ∀ z : ℝ, 0 < z →
    (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
      * |deriv^[j] H2b z| ≤ C := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro m j hm hjm z hz
  have hz1 : 0 < 1 + z := by linarith
  have hWnn : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j) := by
    rw [Work.Spaces.w]; positivity
  rcases lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · -- `m = 0`, hence `j = 0`
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [pow_zero, Nat.sub_zero, div_one, mul_one, one_mul]
      rw [Function.iterate_zero, id_eq]
      have h2 := one_add_mul_w_mul_abs_H2b_le hz
      linarith
    · -- `m = 1`, so `j ∈ {0,1}`
      interval_cases j
      · -- `m = 1`, `j = 0`
        simp only [pow_one, Nat.sub_zero, div_one, Function.iterate_zero, id_eq]
        have h2 := one_add_mul_w_mul_abs_H2b_le hz
        have hzle : z / (1 + z) ≤ 1 := by rw [div_le_one hz1]; linarith
        have h3 : (1 + z) * Work.Spaces.w z * z / (1 + z) * |H2b z|
            = ((1 + z) * Work.Spaces.w z * |H2b z|) * (z / (1 + z)) := by
          field_simp
          try ring
        rw [h3]
        have h4 : 0 ≤ (1 + z) * Work.Spaces.w z * |H2b z| := by
          rw [Work.Spaces.w]; positivity
        calc ((1 + z) * Work.Spaces.w z * |H2b z|) * (z / (1 + z))
            ≤ ((1 + z) * Work.Spaces.w z * |H2b z|) * 1 :=
              mul_le_mul_of_nonneg_left hzle h4
          _ ≤ 10 ^ 7 := by linarith
      · -- `m = j = 1`
        rw [Function.iterate_one, show (1:ℕ) - 1 = 0 from rfl, pow_zero, div_one, pow_one]
        rw [H2b_deriv hz1, Work.Spaces.w]
        have hnum : |2 - 5 * z + z ^ 2| ≤ 5 * (1 + z) ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg z, hz.le, sq_nonneg (1 + z)]
        have hden : (0:ℝ) < (1 + z) ^ 5 := by positivity
        have hmain : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * z
              * |2 * z * (2 - 5 * z + z ^ 2) / (1 + z) ^ 5|
            = 2 * |2 - 5 * z + z ^ 2| / (1 + z) ^ 2 := by
          rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
            abs_of_pos hz, abs_of_pos hden]
          field_simp
          try ring
        rw [hmain]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
        nlinarith [hnum, sq_nonneg (1 + z)]
  · -- `2 ≤ m`
    have hj4 : j ≤ 4 := by omega
    have hkey := abs_deriv_iter_H2b_le hj4 hz.le
    have hId : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * ((1 + z)⁻¹) ^ (j + 1) = (z * (1 + z)⁻¹) ^ (m - 2) := by
      have hw : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
          = (1 + z) ^ 3 * (z ^ m / z ^ 2) * ((1 + z)⁻¹) ^ (m - j) := by
        rw [Work.Spaces.w, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]
        ring
      rw [hw]
      have h1 : ((1 + z)⁻¹) ^ (m - j) * ((1 + z)⁻¹) ^ (j + 1) = ((1 + z)⁻¹) ^ (m + 1) := by
        rw [← pow_add]; congr 1; omega
      have h4 : z ^ m / z ^ 2 = z ^ (m - 2) := by
        rw [div_eq_mul_inv, ← inv_pow, show m = (m - 2) + 2 by omega, pow_add]
        rw [show z ^ (m - 2) * z ^ 2 * z⁻¹ ^ 2 = z ^ (m - 2) by
          rw [mul_assoc,
            show z ^ 2 * z⁻¹ ^ 2 = 1 by
              rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hz), one_pow],
            mul_one]]
        rw [show m - 2 + 2 - 2 = m - 2 by omega]
      have h2 : (1 + z) ^ 3 * ((1 + z)⁻¹) ^ (m + 1) = ((1 + z)⁻¹) ^ (m - 2) := by
        have h3 : (1 + z) ^ 3 * ((1 + z)⁻¹) ^ 3 = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hz1), one_pow]
        rw [show m + 1 = (m - 2) + 3 by omega, pow_add]
        rw [show (1 + z) ^ 3 * (((1 + z)⁻¹) ^ (m - 2) * (1 + z)⁻¹ ^ 3)
            = ((1 + z)⁻¹) ^ (m - 2) * ((1 + z) ^ 3 * (1 + z)⁻¹ ^ 3) by ring, h3, mul_one]
      rw [h4, mul_assoc, h1]
      rw [show (1 + z) ^ 3 * z ^ (m - 2) * (1 + z)⁻¹ ^ (m + 1)
          = z ^ (m - 2) * ((1 + z) ^ 3 * (1 + z)⁻¹ ^ (m + 1)) by ring, h2, mul_pow]
    have hbound : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * |deriv^[j] H2b z|
        ≤ (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
          * (10 ^ 6 * ((1 + z)⁻¹) ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left hkey hWnn
    refine le_trans hbound ?_
    have h5 : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
          * (10 ^ 6 * ((1 + z)⁻¹) ^ (j + 1)) = 10 ^ 6 * (z * (1 + z)⁻¹) ^ (m - 2) := by
      rw [← hId]; ring
    rw [h5]
    have h6 : (z * (1 + z)⁻¹) ^ (m - 2) ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      rw [← div_eq_mul_inv, div_le_one hz1]
      linarith
    nlinarith [h6]

end Work.FTS.Nonlinear.Open.Row19Prep
