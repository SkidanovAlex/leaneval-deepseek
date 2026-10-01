/-
# OffAxis/Tf72One/Cell2Ptwise

Pointwise two-point interpolation bounds for the integrand
`y ↦ (e^{sy} - 2) cos(t y) g72 y` of `Isub` in each of the two variables `s` and `t`,
with the exact second-derivative weight that one integrates afterwards.

* `integrand_interp_t_cell2`: interpolation in `t`, error weight `y² |e^{sy}-2| g72 y`;
* `integrand_interp_s_cell2`: interpolation in `s`, error weight `y² e^{by} g72 y` at the
  right endpoint `b ≥ s`.
-/
import Mathlib
import Submission.Work.OffAxis.Tf72One.Cell2Chord
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables

/-- `a cos θ ≤ |a|` for all real `a`, `θ`. -/
lemma mul_cos_le_abs (a θ : ℝ) : a * Real.cos θ ≤ |a| := by
  rcases le_total 0 a with ha | ha
  · calc a * Real.cos θ ≤ a * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) ha
      _ = |a| := by rw [abs_of_nonneg ha, mul_one]
  · calc a * Real.cos θ ≤ a * (-1) := mul_le_mul_of_nonpos_left (Real.neg_one_le_cos θ) ha
      _ = |a| := by rw [abs_of_nonpos ha]; ring

/-- **Pointwise interpolation in `t`** for the integrand of `Isub`: for `a < b`, `t ∈ [a,b]`
and `y ∈ [0,2]`,
`(e^{sy}-2) cos(ty) g72 y ≤ (b-t)/(b-a)·F(a) + (t-a)/(b-a)·F(b) + (b-a)²/8·y²|e^{sy}-2|g72 y`. -/
lemma integrand_interp_t_cell2 (s t a b y : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
      (b-t)/(b-a) * ((Real.exp (s*y)-2)*Real.cos (a*y)*g72 y)
      + (t-a)/(b-a) * ((Real.exp (s*y)-2)*Real.cos (b*y)*g72 y)
      + (b-a)^2/8 * (y^2 * |Real.exp (s*y)-2| * g72 y) := by
  have hg : 0 ≤ g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
  have hM0 : 0 ≤ y^2 * |Real.exp (s*y) - 2| * g72 y := by positivity
  have hcos_deriv : ∀ τ : ℝ,
      HasDerivAt (fun τ : ℝ => Real.cos (τ*y)) (-(Real.sin (τ*y)) * y) τ := by
    intro τ
    have hinner : HasDerivAt (fun u : ℝ => u*y) y τ := by
      simpa using (hasDerivAt_id τ).mul_const y
    exact (HasDerivAt.comp (x := τ) (h := fun u : ℝ => u*y) (Real.hasDerivAt_cos (τ*y)) hinner)
  have hsin_deriv : ∀ τ : ℝ,
      HasDerivAt (fun τ : ℝ => Real.sin (τ*y)) (Real.cos (τ*y) * y) τ := by
    intro τ
    have hinner : HasDerivAt (fun u : ℝ => u*y) y τ := by
      simpa using (hasDerivAt_id τ).mul_const y
    exact (HasDerivAt.comp (x := τ) (h := fun u : ℝ => u*y) (Real.hasDerivAt_sin (τ*y)) hinner)
  refine chord_upper_of_second_deriv
    (fun τ => (Real.exp (s*y) - 2) * Real.cos (τ*y) * g72 y)
    (fun τ => (Real.exp (s*y) - 2) * (-(Real.sin (τ*y)) * y) * g72 y)
    (fun τ => (Real.exp (s*y) - 2) * ((-(Real.cos (τ*y) * y)) * y) * g72 y)
    a b t (y^2 * |Real.exp (s*y) - 2| * g72 y) hab ⟨hta, htb⟩ hM0 ?_ ?_ ?_ ?_
  · apply Continuous.continuousOn; fun_prop
  · intro τ _
    exact ((hcos_deriv τ).const_mul (Real.exp (s*y) - 2)).mul_const (g72 y)
  · intro τ _
    exact (((hsin_deriv τ).neg.mul_const y).const_mul (Real.exp (s*y) - 2)).mul_const (g72 y)
  · intro τ _
    have hcos : (Real.exp (s*y) - 2) * Real.cos (τ*y) ≤ |Real.exp (s*y) - 2| :=
      mul_cos_le_abs _ _
    have hy2 : (0:ℝ) ≤ y^2 := sq_nonneg y
    have step : (Real.exp (s*y) - 2) * Real.cos (τ*y) * y^2 * g72 y
        ≤ |Real.exp (s*y) - 2| * y^2 * g72 y := by
      have h1 : (Real.exp (s*y) - 2) * Real.cos (τ*y) * y^2 ≤ |Real.exp (s*y) - 2| * y^2 :=
        mul_le_mul_of_nonneg_right hcos hy2
      exact mul_le_mul_of_nonneg_right h1 hg
    have hM : y^2 * |Real.exp (s*y) - 2| * g72 y = |Real.exp (s*y) - 2| * y^2 * g72 y := by ring
    rw [hM]
    nlinarith [step]

/-- **Pointwise interpolation in `s`** for the integrand of `Isub`: for `a < b`, `s ∈ [a,b]`
and `y ∈ [0,2]`,
`(e^{sy}-2) cos(ty) g72 y ≤ (b-s)/(b-a)·F(a) + (s-a)/(b-a)·F(b) + (b-a)²/8·y²e^{by}g72 y`. -/
lemma integrand_interp_s_cell2 (s t a b y : ℝ) (hab : a < b) (hsa : a ≤ s) (hsb : s ≤ b)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
      (b-s)/(b-a) * ((Real.exp (a*y)-2)*Real.cos (t*y)*g72 y)
      + (s-a)/(b-a) * ((Real.exp (b*y)-2)*Real.cos (t*y)*g72 y)
      + (b-a)^2/8 * (y^2 * Real.exp (b*y) * g72 y) := by
  have hg : 0 ≤ g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
  have hM0 : 0 ≤ y^2 * Real.exp (b*y) * g72 y := by positivity
  have hexp_deriv : ∀ u : ℝ,
      HasDerivAt (fun u : ℝ => Real.exp (u*y)) (Real.exp (u*y) * y) u := by
    intro u
    have hinner : HasDerivAt (fun z : ℝ => z*y) y u := by
      simpa using (hasDerivAt_id u).mul_const y
    exact (HasDerivAt.comp (x := u) (h := fun z : ℝ => z*y) (Real.hasDerivAt_exp (u*y)) hinner)
  refine chord_upper_of_second_deriv
    (fun u => (Real.exp (u*y) - 2) * Real.cos (t*y) * g72 y)
    (fun u => Real.exp (u*y) * y * Real.cos (t*y) * g72 y)
    (fun u => Real.exp (u*y) * y * y * Real.cos (t*y) * g72 y)
    a b s (y^2 * Real.exp (b*y) * g72 y) hab ⟨hsa, hsb⟩ hM0 ?_ ?_ ?_ ?_
  · apply Continuous.continuousOn; fun_prop
  · intro u _
    exact (((hexp_deriv u).sub_const 2).mul_const (Real.cos (t*y))).mul_const (g72 y)
  · intro u _
    exact ((((hexp_deriv u).mul_const y).mul_const (Real.cos (t*y))).mul_const (g72 y))
  · intro u hu
    have hcos : -1 ≤ Real.cos (t*y) := Real.neg_one_le_cos _
    have hy2 : (0:ℝ) ≤ y^2 := sq_nonneg y
    have hEu : 0 ≤ Real.exp (u*y) := Real.exp_nonneg _
    have hee : Real.exp (u*y) ≤ Real.exp (b*y) :=
      Real.exp_le_exp.mpr (by nlinarith [hu.2, hy.1])
    have step1 : -(Real.exp (u*y) * y^2 * g72 y)
        ≤ Real.exp (u*y) * y^2 * Real.cos (t*y) * g72 y := by
      have hnn : 0 ≤ Real.exp (u*y) * y^2 * g72 y := mul_nonneg (mul_nonneg hEu hy2) hg
      have h := mul_le_mul_of_nonneg_left hcos hnn
      linarith [h]
    have step2 : -(Real.exp (b*y) * y^2 * g72 y) ≤ -(Real.exp (u*y) * y^2 * g72 y) := by
      have h := mul_le_mul_of_nonneg_right hee (mul_nonneg hy2 hg)
      linarith [h]
    have hf'' : Real.exp (u*y) * y * y * Real.cos (t*y) * g72 y
        = Real.exp (u*y) * y^2 * Real.cos (t*y) * g72 y := by ring
    have hM : y^2 * Real.exp (b*y) * g72 y = Real.exp (b*y) * y^2 * g72 y := by ring
    rw [hf'', hM]
    linarith [step1, step2]

end Work.OffAxis.Tf72One
