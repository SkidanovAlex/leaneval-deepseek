import Mathlib
import Submission.Work.CNum.Basic

/-!
# Taylor remainder bounds for the rational partial sums `cosT`, `sinT`

`cosT x P = ∑_{i ≤ P} (-1)^i x^{2i}/(2i)!` and `sinT x P = ∑_{i ≤ P} (-1)^i x^{2i+1}/(2i+1)!`
are the partial sums of the cosine and sine Taylor series.  In this file we prove the
Lagrange-remainder bounds
`|cos x - cosT x P| ≤ x^{2P+1}/(2P+1)!` and `|sin x - sinT x P| ≤ x^{2P+2}/(2P+2)!`
for `0 ≤ x`.

The proof goes through Taylor's theorem with the Lagrange remainder
(`taylor_mean_remainder_lagrange_iteratedDeriv`), for which one only needs that
`iteratedDeriv (2P+1) cos = ± sin` and `iteratedDeriv (2P+2) cos = ± cos` are bounded by `1`
(`Real.abs_iteratedDeriv_cos_le_one`, `Real.abs_iteratedDeriv_sin_le_one`), together with the
identification of the Taylor polynomial of `cos` (resp. `sin`) of order `2P` (resp. `2P+1`) at
`0` with `cosP` (resp. `sinP`).
-/

namespace Work.CNum

open Finset

/-- The real partial sum `Σ_{i ≤ P} (-1)^i x^{2i}/(2i)!` of the cosine series. -/
noncomputable def cosP (x : ℝ) (P : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (P + 1), (-1 : ℝ) ^ i * x ^ (2 * i) / ((2 * i).factorial : ℝ)

/-- The real partial sum `Σ_{i ≤ P} (-1)^i x^{2i+1}/(2i+1)!` of the sine series. -/
noncomputable def sinP (x : ℝ) (P : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (P + 1), (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)

lemma cosT_cast (x : ℚ) (P : ℕ) : (cosT x P : ℝ) = cosP (x : ℝ) P := by
  rw [cosT, cosP]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sinT_cast (x : ℚ) (P : ℕ) : (sinT x P : ℝ) = sinP (x : ℝ) P := by
  rw [sinT, sinP]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A sum of `g` over `range (2P+1)` equals the sum over the even indices, when `g` vanishes
at all odd indices. -/
lemma sum_range_odd (g : ℕ → ℝ) (hg : ∀ i, g (2 * i + 1) = 0) (P : ℕ) :
    ∑ k ∈ Finset.range (2 * P + 1), g k = ∑ i ∈ Finset.range (P + 1), g (2 * i) := by
  induction P with
  | zero => simp
  | succ P ih =>
    have h : 2 * (P + 1) + 1 = (2 * P + 1) + 2 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, hg P, add_zero]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show 2 * P + 2 = 2 * (P + 1) by ring]

/-- A sum of `g` over `range (2P+2)` equals the sum over the odd indices, when `g` vanishes
at all even indices. -/
lemma sum_range_even (g : ℕ → ℝ) (hg : ∀ i, g (2 * i) = 0) (P : ℕ) :
    ∑ k ∈ Finset.range (2 * P + 2), g k = ∑ i ∈ Finset.range (P + 1), g (2 * i + 1) := by
  induction P with
  | zero => simp [Finset.sum_range_succ, hg 0]
  | succ P ih =>
    have h : 2 * (P + 1) + 2 = (2 * P + 2) + 2 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [show 2 * P + 2 = 2 * (P + 1) by ring, hg (P + 1), add_zero]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show 2 * P + 3 = 2 * (P + 1) + 1 by ring]

/-- The Taylor polynomial of `cos` of order `2P` at `0` evaluated at `x` is `cosP x P`. -/
lemma taylorWithinEval_cosP (x : ℝ) (hx : 0 < x) (P : ℕ) :
    taylorWithinEval Real.cos (2 * P) (Set.uIcc 0 x) 0 x = cosP x P := by
  rw [taylor_within_apply, Set.uIcc_of_le hx.le]
  simp only [smul_eq_mul, sub_zero]
  trans ∑ k ∈ Finset.range (2 * P + 1),
      (k.factorial : ℝ)⁻¹ * x ^ k * iteratedDeriv k Real.cos 0
  · exact Finset.sum_congr rfl fun k _ =>
      congrArg _ (Real.iteratedDerivWithin_cos_Icc k hx (Set.left_mem_Icc.mpr hx.le))
  rw [sum_range_odd (g := fun k => (k.factorial : ℝ)⁻¹ * x ^ k * iteratedDeriv k Real.cos 0)
    (fun i => by rw [Real.iteratedDeriv_odd_cos i]; simp) P]
  rw [cosP]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.iteratedDeriv_even_cos, div_eq_mul_inv]; simp; ring

/-- The Taylor polynomial of `sin` of order `2P+1` at `0` evaluated at `x` is `sinP x P`. -/
lemma taylorWithinEval_sinP (x : ℝ) (hx : 0 < x) (P : ℕ) :
    taylorWithinEval Real.sin (2 * P + 1) (Set.uIcc 0 x) 0 x = sinP x P := by
  rw [taylor_within_apply, Set.uIcc_of_le hx.le]
  simp only [smul_eq_mul, sub_zero]
  trans ∑ k ∈ Finset.range (2 * P + 2),
      (k.factorial : ℝ)⁻¹ * x ^ k * iteratedDeriv k Real.sin 0
  · exact Finset.sum_congr rfl fun k _ =>
      congrArg _ (Real.iteratedDerivWithin_sin_Icc k hx (Set.left_mem_Icc.mpr hx.le))
  rw [sum_range_even (g := fun k => (k.factorial : ℝ)⁻¹ * x ^ k * iteratedDeriv k Real.sin 0)
    (fun i => by rw [Real.iteratedDeriv_even_sin i]; simp) P]
  rw [sinP]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.iteratedDeriv_odd_sin, div_eq_mul_inv]; simp; ring

lemma cosP_zero (P : ℕ) : cosP 0 P = 1 := by
  rw [cosP, Finset.sum_range_succ']; simp

lemma sinP_zero (P : ℕ) : sinP 0 P = 0 := by
  rw [sinP]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [zero_pow (by omega : 2 * i + 1 ≠ 0)]
  simp

/-- Lagrange-remainder bound for the cosine Taylor polynomial of order `2P`. -/
lemma cos_bound (x : ℝ) (hx : 0 ≤ x) (P : ℕ) :
    |Real.cos x - cosP x P| ≤ x ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    rw [cosP_zero, Real.cos_zero, sub_self, abs_zero]; simp
  · obtain ⟨x', -, hxl⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.cos) (x := x) (x₀ := 0) (n := 2 * P)
        (ne_of_lt hpos) (Real.contDiff_cos.contDiffOn)
    rw [taylorWithinEval_cosP x hpos P] at hxl
    rw [hxl, sub_zero, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hx _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * P + 1).factorial : ℝ))]
    have h1 : |iteratedDeriv (2 * P + 1) Real.cos x'| ≤ 1 :=
      Real.abs_iteratedDeriv_cos_le_one _ _
    have h2 : 0 ≤ x ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ) :=
      div_nonneg (pow_nonneg hx _) (by positivity)
    calc |iteratedDeriv (2 * P + 1) Real.cos x'| * x ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ)
        = |iteratedDeriv (2 * P + 1) Real.cos x'| *
            (x ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ)) := by ring
      _ ≤ 1 * (x ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = x ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ) := by ring

/-- Lagrange-remainder bound for the sine Taylor polynomial of order `2P+1`. -/
lemma sin_bound (x : ℝ) (hx : 0 ≤ x) (P : ℕ) :
    |Real.sin x - sinP x P| ≤ x ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    rw [sinP_zero, Real.sin_zero, sub_self, abs_zero]; simp
  · obtain ⟨x', -, hxl⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.sin) (x := x) (x₀ := 0)
        (n := 2 * P + 1) (ne_of_lt hpos) (Real.contDiff_sin.contDiffOn)
    rw [taylorWithinEval_sinP x hpos P] at hxl
    rw [hxl, sub_zero, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hx _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * P + 2).factorial : ℝ))]
    have h1 : |iteratedDeriv (2 * P + 2) Real.sin x'| ≤ 1 :=
      Real.abs_iteratedDeriv_sin_le_one _ _
    have h2 : 0 ≤ x ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ) :=
      div_nonneg (pow_nonneg hx _) (by positivity)
    calc |iteratedDeriv (2 * P + 2) Real.sin x'| * x ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ)
        = |iteratedDeriv (2 * P + 2) Real.sin x'| *
            (x ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ)) := by ring
      _ ≤ 1 * (x ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = x ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ) := by ring

theorem cosT_bound (x : ℚ) (hx : 0 ≤ x) (P : ℕ) :
    |Real.cos (x : ℝ) - (cosT x P : ℝ)| ≤ (x : ℝ) ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ) ∧
    |Real.sin (x : ℝ) - (sinT x P : ℝ)| ≤ (x : ℝ) ^ (2 * P + 2) / ((2 * P + 2).factorial : ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [cosT_cast]
    exact cos_bound (x : ℝ) (by exact_mod_cast hx) P
  · rw [sinT_cast]
    exact sin_bound (x : ℝ) (by exact_mod_cast hx) P

end Work.CNum
