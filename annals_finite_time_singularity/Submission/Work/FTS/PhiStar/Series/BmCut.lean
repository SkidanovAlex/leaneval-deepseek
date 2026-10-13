import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Series.BmCutAux
import Submission.Work.FTS.PhiStar.Series.abs_deriv_mul_le
import Submission.Work.FTS.PhiStar.Series.abs_deriv2_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

/-! # A `C²` cutoff family on `[0, π/2]` whose derivatives also vanish at the layer ends

For every `δ > 0` we construct a `C²` function `bmcut δ : ℝ → ℝ` with values in `[0,1]` which
is `1` on `[δ, π/2-δ]`, vanishes outside `(δ/2, π/2-δ/2)`, whose first and second derivatives
are `O(1/δ)` resp. `O(1/δ²)` with `δ`-independent constants, and whose first two derivatives
vanish *everywhere outside the two open layers* `(δ/2,δ) ∪ (π/2-δ, π/2-δ/2)` — including at
the boundary points `δ/2`, `δ`, `π/2-δ`, `π/2-δ/2`.

The construction is the product of two rescaled copies of `Real.smoothTransition`
(`0` on `(-∞,0]`, `1` on `[1,∞)`):

`bmcut δ θ = ψ(2θ/δ - 1) · ψ(2(π/2-θ)/δ - 1)`  for `δ ≤ π/4`,

and `bmcut δ = 0` for `δ > π/4` (where the plateau condition is vacuous).  The vanishing of
the derivatives at the boundary points of the layers uses `ψ'(0) = ψ''(0) = ψ'(1) = ψ''(1) = 0`
(`BmCutAux.st_deriv_eq_zero_of_nonpos` and friends). -/

/-! ## The cutoff family -/

/-- The cutoff of size `δ`. -/
def bmcut (δ : ℝ) : ℝ → ℝ :=
  if δ ≤ Real.pi / 4 then
    ramp (2 / δ) (-1) * ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)
  else 0

theorem bmcut_of_le {δ : ℝ} (h : δ ≤ Real.pi / 4) :
    bmcut δ = ramp (2 / δ) (-1) * ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1) := by
  rw [bmcut]
  exact ite_eq_left h

theorem bmcut_of_gt {δ : ℝ} (h : ¬ δ ≤ Real.pi / 4) : bmcut δ = 0 := by
  rw [bmcut]
  exact ite_eq_right h

/-- Membership test for the complement of an open interval. -/
theorem not_mem_Ioo_or {x a b : ℝ} (h : x ∉ Set.Ioo a b) : x ≤ a ∨ b ≤ x := by
  by_contra hcon
  rw [not_or] at hcon
  exact h ⟨not_le.mp hcon.1, not_le.mp hcon.2⟩

/-! ## Elementary arithmetic for the two ramps -/

private lemma arg_low {δ θ : ℝ} (hδ : 0 < δ) (h : θ ≤ δ / 2) :
    (2 / δ) * θ + (-1) ≤ 0 := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * (δ / 2) = 1 := by field_simp
  linarith

private lemma arg_high {δ θ : ℝ} (hδ : 0 < δ) (h : δ ≤ θ) :
    1 ≤ (2 / δ) * θ + (-1) := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * δ = 2 := by field_simp
  linarith

private lemma narg_low {δ θ : ℝ} (hδ : 0 < δ) (h : Real.pi / 2 - δ / 2 ≤ θ) :
    (-(2 / δ)) * θ + ((2 / δ) * (Real.pi / 2) - 1) ≤ 0 := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * (Real.pi / 2 - δ / 2) = (2 / δ) * (Real.pi / 2) - 1 := by
    field_simp
  linarith

private lemma narg_high {δ θ : ℝ} (hδ : 0 < δ) (h : θ ≤ Real.pi / 2 - δ) :
    1 ≤ (-(2 / δ)) * θ + ((2 / δ) * (Real.pi / 2) - 1) := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * (Real.pi / 2 - δ) = (2 / δ) * (Real.pi / 2) - 2 := by
    field_simp
  linarith

/-! ## Vanishing of the derivatives of a ramp on the flat pieces -/

theorem deriv_ramp_eq_zero {a b θ : ℝ} (h : a * θ + b ≤ 0 ∨ 1 ≤ a * θ + b) :
    deriv (ramp a b) θ = 0 := by
  rcases h with h | h
  · rw [deriv_ramp, st_deriv_eq_zero_of_nonpos h, zero_mul]
  · rw [deriv_ramp, st_deriv_eq_zero_of_one_le h, zero_mul]

theorem deriv2_ramp_eq_zero {a b θ : ℝ} (h : a * θ + b ≤ 0 ∨ 1 ≤ a * θ + b) :
    deriv (deriv (ramp a b)) θ = 0 := by
  rcases h with h | h
  · rw [deriv2_ramp, st_deriv2_eq_zero_of_nonpos h, zero_mul, zero_mul]
  · rw [deriv2_ramp, st_deriv2_eq_zero_of_one_le h, zero_mul, zero_mul]

/-- Leibniz for the second derivative of a product. -/
theorem deriv2_mul_eq {f g : ℝ → ℝ} {θ : ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hf' : DifferentiableAt ℝ (deriv f) θ)
    (hg' : DifferentiableAt ℝ (deriv g) θ) :
    deriv (deriv (f * g)) θ
      = deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ) + f θ * deriv (deriv g) θ := by
  have h1 : deriv (f * g) = fun x => deriv f x * g x + f x * deriv g x := by
    funext x
    exact deriv_mul (hf x) (hg x)
  rw [h1]
  have hd1 : DifferentiableAt ℝ (fun x => deriv f x * g x) θ := hf'.mul hg.differentiableAt
  have hd2 : DifferentiableAt ℝ (fun x => f x * deriv g x) θ := hf.differentiableAt.mul hg'
  rw [show (fun x => deriv f x * g x + f x * deriv g x)
      = (fun x => deriv f x * g x) + (fun x => f x * deriv g x) from rfl]
  rw [deriv_add hd1 hd2]
  have e1 : deriv (fun x => deriv f x * g x) θ
      = deriv (deriv f) θ * g θ + deriv f θ * deriv g θ := by
    rw [show (fun x => deriv f x * g x) = deriv f * g from rfl, deriv_mul hf' hg.differentiableAt]
  have e2 : deriv (fun x => f x * deriv g x) θ
      = deriv f θ * deriv g θ + f θ * deriv (deriv g) θ := by
    rw [show (fun x => f x * deriv g x) = f * deriv g from rfl, deriv_mul hf.differentiableAt hg']
  rw [e1, e2]
  ring

/-! ## The main existence theorem -/

set_option maxHeartbeats 1000000 in
theorem exists_bmcut_supp : ∃ χ : ℝ → ℝ → ℝ, ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
    (∀ δ : ℝ, 0 < δ → ContDiff ℝ 2 (χ δ)) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, 0 ≤ χ δ θ ∧ χ δ θ ≤ 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ ∈ Set.Icc δ (Real.pi / 2 - δ), χ δ θ = 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) → χ δ θ = 0) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (χ δ) θ| ≤ K₁ / δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (deriv (χ δ)) θ| ≤ K₂ / δ ^ 2) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ,
      (θ ∉ Set.Ioo (δ / 2) δ ∧ θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)) →
      deriv (χ δ) θ = 0 ∧ deriv (deriv (χ δ)) θ = 0) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb₁, hb₂⟩ := st_bounds
  refine ⟨bmcut, 4 * C₁ + 1, 8 * C₂ + 8 * C₁ ^ 2 + 1, by linarith,
    by nlinarith [sq_nonneg C₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ContDiff`
    intro δ hδ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      exact (ramp_contDiff _ _).mul (ramp_contDiff _ _)
    · rw [bmcut_of_gt h4]
      exact contDiff_const
  · -- `0 ≤ χ δ θ ≤ 1`
    intro δ hδ θ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      refine ⟨mul_nonneg (ramp_nonneg _ _ _) (ramp_nonneg _ _ _), ?_⟩
      calc ramp (2 / δ) (-1) θ * ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1) θ
          ≤ 1 * 1 := mul_le_mul (ramp_le_one _ _ _) (ramp_le_one _ _ _)
              (ramp_nonneg _ _ _) (by norm_num)
        _ = 1 := by norm_num
    · rw [bmcut_of_gt h4]
      exact ⟨le_refl 0, zero_le_one⟩
  · -- the plateau
    intro δ hδ θ hθ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      simp only [Pi.mul_apply]
      rw [ramp_eq_one _ _ _ (arg_high hδ hθ.1), ramp_eq_one _ _ _ (narg_high hδ hθ.2), one_mul]
    · exfalso
      linarith [hθ.1, hθ.2, not_le.mp h4]
  · -- vanishing outside the transition region
    intro δ hδ θ hθ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      simp only [Pi.mul_apply]
      rcases not_mem_Ioo_or hθ with h | h
      · rw [ramp_eq_zero _ _ _ (arg_low hδ h), zero_mul]
      · rw [ramp_eq_zero _ _ _ (narg_low hδ h), mul_zero]
    · exact congrFun (bmcut_of_gt h4) θ
  · -- first derivative bound
    intro δ hδ θ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      have hb := abs_deriv_mul_le (f := ramp (2 / δ) (-1))
        (g := ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) (θ := θ)
        (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt
        (deriv_ramp_bound hb₁ _ _ θ) (deriv_ramp_bound hb₁ _ _ θ)
        (ramp_nonneg _ _ _) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (ramp_le_one _ _ _)
      refine le_trans hb ?_
      have hA1 : |(2 : ℝ) / δ| = 2 / δ := abs_of_pos (by positivity)
      have hA2 : |(-(2 / δ))| = 2 / δ := by rw [abs_neg, hA1]
      rw [hA1, hA2]
      have hsum : C₁ * (2 / δ) + C₁ * (2 / δ) = 4 * C₁ / δ := by ring
      rw [hsum, div_le_div_iff_of_pos_right hδ]
      linarith
    · have hz : deriv (bmcut δ) θ = 0 := by
        rw [bmcut_of_gt h4]
        exact deriv_const θ 0
      rw [hz, abs_zero]
      positivity
  · -- second derivative bound
    intro δ hδ θ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      have hb := abs_deriv2_mul_le (f := ramp (2 / δ) (-1))
        (g := ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) (θ := θ)
        (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ) (ramp_diffAt_deriv _ _ θ)
        (deriv_ramp_bound hb₁ _ _ θ) (deriv_ramp_bound hb₁ _ _ θ)
        (deriv2_ramp_bound hb₂ _ _ θ) (deriv2_ramp_bound hb₂ _ _ θ)
        (ramp_nonneg _ _ _) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (ramp_le_one _ _ _)
      refine le_trans hb ?_
      have hA1 : |(2 : ℝ) / δ| = 2 / δ := abs_of_pos (by positivity)
      have hA2 : |(-(2 / δ))| = 2 / δ := by rw [abs_neg, hA1]
      rw [hA1, hA2]
      have hval : C₂ * ((2 / δ) * (2 / δ)) + 2 * (C₁ * (2 / δ)) * (C₁ * (2 / δ))
          + C₂ * ((2 / δ) * (2 / δ)) = (8 * C₂ + 8 * C₁ ^ 2) / δ ^ 2 := by ring
      rw [hval, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < δ ^ 2)]
      linarith [sq_nonneg C₁]
    · have hz : deriv (deriv (bmcut δ)) θ = 0 := by
        rw [bmcut_of_gt h4]
        have hfun : deriv (0 : ℝ → ℝ) = (0 : ℝ → ℝ) := by
          funext t
          exact deriv_const t 0
        rw [hfun]
        exact deriv_const θ 0
      rw [hz, abs_zero]
      positivity
  · -- the derivative support
    intro δ hδ θ hθ
    obtain ⟨h1, h2⟩ := hθ
    have h1' := not_mem_Ioo_or h1
    have h2' := not_mem_Ioo_or h2
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      rcases h1' with h1 | h1
      · -- `θ ≤ δ / 2`: the first ramp is flat (its derivative vanishes everywhere there)
        have hfa : (2 / δ) * θ + (-1) ≤ 0 := arg_low hδ h1
        have hdf : deriv (ramp (2 / δ) (-1)) θ = 0 :=
          deriv_ramp_eq_zero (a := 2 / δ) (b := -1) (Or.inl hfa)
        have hd2f : deriv (deriv (ramp (2 / δ) (-1))) θ = 0 :=
          deriv2_ramp_eq_zero (a := 2 / δ) (b := -1) (Or.inl hfa)
        have hfv : ramp (2 / δ) (-1) θ = 0 := ramp_eq_zero _ _ _ hfa
        constructor
        · rw [deriv_mul (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt,
            hdf, hfv]
          ring
        · rw [deriv2_mul_eq (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ)
              (ramp_diffAt_deriv _ _ θ), hdf, hd2f, hfv]
          ring
      · -- `δ ≤ θ`: the first ramp is flat `1`
        have hfg1 : 1 ≤ (2 / δ) * θ + (-1) := arg_high hδ h1
        have hdf : deriv (ramp (2 / δ) (-1)) θ = 0 :=
          deriv_ramp_eq_zero (Or.inr hfg1)
        have hd2f : deriv (deriv (ramp (2 / δ) (-1))) θ = 0 :=
          deriv2_ramp_eq_zero (Or.inr hfg1)
        rcases h2' with h2 | h2
        · -- `θ ≤ π/2 - δ`: the second ramp is flat `1`
          have hdg : deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) θ = 0 :=
            deriv_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inr (narg_high hδ h2))
          have hd2g : deriv (deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1))) θ = 0 :=
            deriv2_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inr (narg_high hδ h2))
          constructor
          · rw [deriv_mul (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt,
              hdf, hdg]
            ring
          · rw [deriv2_mul_eq (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ)
                (ramp_diffAt_deriv _ _ θ), hdf, hd2f, hdg, hd2g]
            ring
        · -- `π/2 - δ/2 ≤ θ`: the second ramp is flat `0`
          have hdg : deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) θ = 0 :=
            deriv_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inl (narg_low hδ h2))
          have hd2g : deriv (deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1))) θ = 0 :=
            deriv2_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inl (narg_low hδ h2))
          constructor
          · rw [deriv_mul (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt,
              hdf, hdg]
            ring
          · rw [deriv2_mul_eq (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ)
                (ramp_diffAt_deriv _ _ θ), hdf, hd2f, hdg, hd2g]
            ring
    · have h1z : deriv (bmcut δ) θ = 0 := by
        rw [bmcut_of_gt h4]
        exact deriv_const θ 0
      have h2z : deriv (deriv (bmcut δ)) θ = 0 := by
        rw [bmcut_of_gt h4]
        have hfun : deriv (0 : ℝ → ℝ) = (0 : ℝ → ℝ) := by
          funext t
          exact deriv_const t 0
        rw [hfun]
        exact deriv_const θ 0
      exact ⟨h1z, h2z⟩

end Work.FTS.PhiStar.Series
