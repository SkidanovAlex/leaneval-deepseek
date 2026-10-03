/-
# The mollified log-sine function `-log(1/2 |sin α|)` (FI (15.5)–(15.7))

This file contains the *definitions* used to prove `Work.FIArea4.logSine_fourier`, together with
the elementary properties (smoothness, `2π`-periodicity, the value on the range
`2/N ≤ |α| ≤ 1`) that the main proof needs.

The mollifier is built from `τ = Real.smoothTransition`, i.e. the `C^∞` function which is `0` on
`(-∞,0]` and `1` on `[1,∞)`.

* `Psi N y = (1/2) · τ (2 N² y - 1) · log (2y)`:  the cut-off logarithmic factor.  It vanishes for
  `y ≤ 1/(2N²)` and equals `(1/2) log (2y)` for `y ≥ 1/N²`.
* `ufun N α = -Psi N (1 - cos α) - Psi N (1 + cos α) + 2 log 2`:  a smooth `2π`-periodic function
  with `ufun N α = -log(|sin α| / 2)` whenever `2/N ≤ |α| ≤ 1` (see `ufun_of_range`).

The singularities of `log|2 sin(α/2)|` at `α ∈ 2πℤ` (where `1 - cos α = 0`) and of
`log|2 cos(α/2)|` at `α ∈ π + 2πℤ` (where `1 + cos α = 0`) are killed by the cut-off `τ`, exactly
as described in the doc-string of `Work.FIArea4.logSine_fourier`.
-/
import Mathlib

namespace Work.FIArea4

open scoped BigOperators
open scoped Topology
open scoped ContDiff

noncomputable section

/-- The logarithmic mollifier factor `Ψ_N(y) = (1/2)·τ(2 N² y − 1)·log(2y)`, where
`τ = Real.smoothTransition`.  It is `C^∞`, vanishes for `y ≤ 1/(2N²)` and equals
`(1/2)·log(2y)` for `y ≥ 1/N²`. -/
def Psi (N : ℕ) (y : ℝ) : ℝ :=
  (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * Real.log (2 * y)

/-- The mollified log-sine function on the line. -/
def ufun (N : ℕ) (α : ℝ) : ℝ :=
  -Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α) + 2 * Real.log 2

/-- `ufun` viewed as a complex valued function (for the Fourier analysis). -/
def ufunC (N : ℕ) (α : ℝ) : ℂ := (ufun N α : ℂ)

/-- `τ` vanishes where its argument is `≤ 0`. -/
lemma phi_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : Real.smoothTransition x = 0 :=
  Real.smoothTransition.zero_of_nonpos hx

/-- `τ` equals `1` where its argument is `≥ 1`. -/
lemma phi_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.smoothTransition x = 1 :=
  Real.smoothTransition.one_of_one_le hx

/-- `Ψ_N (y) = 0` for `y ≤ 1/(2 N²)`. -/
lemma Psi_eq_zero {N : ℕ} {y : ℝ} (h : 2 * (N : ℝ) ^ 2 * y - 1 ≤ 0) : Psi N y = 0 := by
  rw [Psi, phi_zero_of_nonpos h]
  ring

/-- `Ψ_N (y) = (1/2) log (2y)` for `2 N² y - 1 ≥ 1`. -/
lemma Psi_eq_log {N : ℕ} {y : ℝ} (h : 1 ≤ 2 * (N : ℝ) ^ 2 * y - 1) :
    Psi N y = (1 / 2) * Real.log (2 * y) := by
  rw [Psi, phi_one_of_one_le h, mul_one]

/-- `1 - cos x ≥ (43/96) x²` for `|x| ≤ 1`. -/
lemma one_sub_cos_ge {x : ℝ} (hx : |x| ≤ 1) : (43 / 96) * x ^ 2 ≤ 1 - Real.cos x := by
  have h := Real.cos_bound hx
  have hx2 : x ^ 2 ≤ 1 := by
    have : |x| ^ 2 ≤ 1 ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [one_pow, sq_abs] at this
  have h4 : |x| ^ 4 ≤ x ^ 2 := by
    have hsq : |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    rw [hsq, sq_abs]
    nlinarith [sq_nonneg x]
  have h5 : |x| ^ 4 * (5 / 96) ≤ x ^ 2 * (5 / 96) := by
    apply mul_le_mul_of_nonneg_right h4 (by norm_num)
  have h6 : Real.cos x - (1 - x ^ 2 / 2) ≤ |x| ^ 4 * (5 / 96) :=
    le_trans (le_abs_self _) h
  linarith

/-- `Ψ_N` is `C^∞` (for `N ≥ 1`). -/
lemma contDiff_Psi (N : ℕ) (hN : 1 ≤ N) : ContDiff ℝ ∞ (Psi N) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN2pos : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  rcases lt_or_ge y (1 / (2 * (N : ℝ) ^ 2)) with hy | hy
  · have hzero : Psi N =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hy] with z hz
      have hz' : 2 * (N : ℝ) ^ 2 * z - 1 < 0 := by
        have h1 : 2 * (N : ℝ) ^ 2 * z < 1 := by
          calc 2 * (N : ℝ) ^ 2 * z < 2 * (N : ℝ) ^ 2 * (1 / (2 * (N : ℝ) ^ 2)) :=
                mul_lt_mul_of_pos_left hz hN2pos
            _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hN2pos)]
        linarith
      exact Psi_eq_zero hz'.le
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
    have h1 : ContDiffAt ℝ ∞ (fun z : ℝ => Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1)) y := by
      have hinner : ContDiffAt ℝ ∞ (fun z : ℝ => 2 * (N : ℝ) ^ 2 * z - 1) y := by fun_prop
      have hτ : ContDiffAt ℝ ∞ Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) :=
        Real.smoothTransition.contDiff.contDiffAt
      exact hτ.comp y hinner
    have h2 : ContDiffAt ℝ ∞ (fun z : ℝ => Real.log (2 * z)) y :=
      ContDiffAt.log (by fun_prop) (by positivity)
    have h3 : ContDiffAt ℝ ∞ (fun z : ℝ =>
        (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1) * Real.log (2 * z)) y :=
      (contDiffAt_const.mul h1).mul h2
    exact h3

/-- `ufun N` is `C^∞`. -/
lemma contDiff_ufun (N : ℕ) (hN : 1 ≤ N) : ContDiff ℝ ∞ (ufun N) := by
  have h1 : ContDiff ℝ ∞ (fun α : ℝ => Psi N (1 - Real.cos α)) :=
    (contDiff_Psi N hN).comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ (fun α : ℝ => Psi N (1 + Real.cos α)) :=
    (contDiff_Psi N hN).comp (by fun_prop)
  have h3 : ContDiff ℝ ∞ (fun α : ℝ => -Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α)
      + 2 * Real.log 2) := (h1.neg.sub h2).add contDiff_const
  exact h3

/-- `ufun N` is `2π`-periodic. -/
lemma ufun_periodic (N : ℕ) (α : ℝ) : ufun N (α + 2 * Real.pi) = ufun N α := by
  simp only [ufun, Real.cos_add_two_pi]

/-- `cos α ≥ 0` for `|α| ≤ 1`. -/
lemma cos_nonneg_of_abs_le_one {α : ℝ} (h : |α| ≤ 1) : 0 ≤ Real.cos α := by
  apply Real.cos_nonneg_of_mem_Icc
  rw [Set.mem_Icc]
  constructor
  · have : -(Real.pi / 2) ≤ -1 := by linarith [Real.pi_gt_three]
    linarith [neg_abs_le α]
  · linarith [le_abs_self α, Real.pi_gt_three]

/-- `|sin α| > 0` for `0 < |α| < π`. -/
lemma abs_sin_pos_of {α : ℝ} (h0 : 0 < |α|) (hp : |α| < Real.pi) : 0 < |Real.sin α| := by
  rw [abs_pos]
  have hα0 : α ≠ 0 := (abs_pos.mp h0)
  rcases lt_or_gt_of_ne hα0 with h | h
  · have hsin : Real.sin α < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith [neg_abs_le α])
    exact ne_of_lt hsin
  · have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi h (by linarith [le_abs_self α])
    exact ne_of_gt hsin

/-- **The value of the mollified function on the range** `2/N ≤ |α| ≤ 1`. -/
lemma ufun_of_range (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (h1 : 2 / (N : ℝ) ≤ |α|) (h2 : |α| ≤ 1) :
    ufun N α = -Real.log (|Real.sin α| / 2) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hN2 : (2 : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hN)
  have hα0 : 0 < |α| := lt_of_lt_of_le (by positivity) h1
  have hαpi : |α| < Real.pi := by linarith [Real.pi_gt_three]
  have hsinn : |Real.sin α| ≠ 0 := ne_of_gt (abs_sin_pos_of hα0 hαpi)
  have hcosnn : 0 ≤ Real.cos α := cos_nonneg_of_abs_le_one h2
  -- `1 - cos α ≥ 1/N²`
  have hg : 1 / (N : ℝ) ^ 2 ≤ 1 - Real.cos α := by
    have h43 := one_sub_cos_ge (x := |α|) (by rw [abs_abs]; exact h2)
    rw [Real.cos_abs] at h43
    have hsq : ((2:ℝ) / (N:ℝ))^2 ≤ |α|^2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have hN2pos : (0:ℝ) < (N:ℝ)^2 := by positivity
    have h43' : (43/96) * (((2:ℝ)/(N:ℝ))^2) ≤ (43/96) * |α|^2 := by
      apply mul_le_mul_of_nonneg_left hsq (by norm_num)
    have heq : (43/96) * (((2:ℝ)/(N:ℝ))^2) = 43/(24 * (N:ℝ)^2) := by field_simp; ring
    have hfin : (1:ℝ)/(N:ℝ)^2 ≤ (43/96) * (((2:ℝ)/(N:ℝ))^2) := by
      rw [heq, le_div_iff₀ (by positivity : (0:ℝ) < 24 * (N:ℝ)^2)]
      have : (1:ℝ)/(N:ℝ)^2 * (24 * (N:ℝ)^2) = 24 := by field_simp
      linarith
    linarith
  -- `1 + cos α ≥ 1/N²`
  have hh2 : 1 / (N : ℝ) ^ 2 ≤ 1 + Real.cos α := by
    have h4 : 1 / (N : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hN1]
    linarith
  have hgs : 0 < 1 - Real.cos α := lt_of_lt_of_le (by positivity) hg
  have hhs : 0 < 1 + Real.cos α := lt_of_lt_of_le (by positivity) hh2
  have hA : (1:ℝ) ≤ 2 * (N:ℝ)^2 * (1 - Real.cos α) - 1 := by
    have hmul := mul_le_mul_of_nonneg_left hg (show (0:ℝ) ≤ 2 * (N:ℝ)^2 by positivity)
    have he : (2:ℝ) * (N:ℝ)^2 * (1/(N:ℝ)^2) = 2 := by field_simp
    linarith
  have hB : (1:ℝ) ≤ 2 * (N:ℝ)^2 * (1 + Real.cos α) - 1 := by
    have hmul := mul_le_mul_of_nonneg_left hh2 (show (0:ℝ) ≤ 2 * (N:ℝ)^2 by positivity)
    have he : (2:ℝ) * (N:ℝ)^2 * (1/(N:ℝ)^2) = 2 := by field_simp
    linarith
  rw [ufun, Psi_eq_log hA, Psi_eq_log hB]
  -- now the log identity
  have hL1 : Real.log (2 * (1 - Real.cos α)) = Real.log 2 + Real.log (1 - Real.cos α) :=
    Real.log_mul (by norm_num) (by positivity)
  have hL2 : Real.log (2 * (1 + Real.cos α)) = Real.log 2 + Real.log (1 + Real.cos α) :=
    Real.log_mul (by norm_num) (by positivity)
  have hL3 : Real.log (1 - Real.cos α) + Real.log (1 + Real.cos α)
      = 2 * Real.log |Real.sin α| := by
    rw [← Real.log_mul (ne_of_gt hgs) (ne_of_gt hhs),
      show (1 - Real.cos α) * (1 + Real.cos α) = Real.sin α ^ 2 by rw [Real.sin_sq]; ring,
      Real.log_pow, ← Real.log_abs]
    ring
  have htgt : Real.log (|Real.sin α| / 2) = Real.log |Real.sin α| - Real.log 2 :=
    Real.log_div hsinn (by norm_num)
  rw [htgt]
  linarith

end

end Work.FIArea4
