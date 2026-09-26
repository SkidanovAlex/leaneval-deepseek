import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DirichletExpansion

/-!
# The `τ`-difference combination `F(τ,x) - τ (F(τ+1,x) - F(τ,x))`

This file collects the elementary facts about the two functions

* `diffF S x τ = F(τ+1,x) - F(τ,x)`, and
* `tauDiffF S x τ = F(τ,x) - τ (F(τ+1,x) - F(τ,x))`

associated with a solution `S` of the functional equations of CKMRV Theorem 3.1:
`1`-periodicity in `τ`, holomorphy on the upper half plane, the strip bounds coming
from hypothesis (iv), and the norm sum `dirichletNormSum` controlling the size of a
Dirichlet series with coefficients `c`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-- `F(τ+1,x) - F(τ,x)`. -/
def diffF (S : FunctionalEquationSolution n) (x : E n) : ℂ → ℂ :=
  fun τ => S.F (τ + 1) x - S.F τ x

/-- `F(τ,x) - τ (F(τ+1,x) - F(τ,x))`, the function whose Dirichlet coefficients are the
`a`-coefficients of CKMRV (3.1). -/
def tauDiffF (S : FunctionalEquationSolution n) (x : E n) : ℂ → ℂ :=
  fun τ => S.F τ x - τ * (S.F (τ + 1) x - S.F τ x)

/-- The norm sum `∑_k ‖c k‖ e^{-2π(k+1)y}` controlling the size of the Dirichlet series
`∑_k c_k e^{2πi(k+1)τ}` on the line `Im τ = y`. -/
def dirichletNormSum (c : ℕ → ℂ) (y : ℝ) : ℝ :=
  ∑' k : ℕ, ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))

@[simp] lemma diffF_apply (S : FunctionalEquationSolution n) (x : E n) (τ : ℂ) :
    diffF S x τ = S.F (τ + 1) x - S.F τ x := rfl

@[simp] lemma tauDiffF_apply (S : FunctionalEquationSolution n) (x : E n) (τ : ℂ) :
    tauDiffF S x τ = S.F τ x - τ * (S.F (τ + 1) x - S.F τ x) := rfl

/-! ## Periodicity on the upper half plane -/

/-- Extending a `1`-periodic function of the upper half plane by zero gives a globally
`1`-periodic function on `ℂ`. -/
lemma periodic_extend_of_upperHalfPlane {f : ℂ → ℂ}
    (hper : ∀ τ : ℂ, 0 < τ.im → f (τ + 1) = f τ) :
    Function.Periodic (fun z : ℂ => if 0 < z.im then f z else 0) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    simp only [hz, hz', if_true]
    exact hper z hz
  · have hz' : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [hz, hz', if_false]

/-- **Reduction to the fundamental strip.**  A `1`-periodic function on the upper half
plane agrees, at any point, with its value at a point of the strip `-1 ≤ Re ≤ 0`, at the
same height. -/
lemma exists_periodic_reduce {f : ℂ → ℂ}
    (hper : ∀ τ : ℂ, 0 < τ.im → f (τ + 1) = f τ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ τ' : ℂ, τ'.im = τ.im ∧ -1 ≤ τ'.re ∧ τ'.re ≤ 0 ∧ f τ' = f τ := by
  set k : ℤ := ⌈τ.re⌉ with hk
  have hkre : ((k : ℂ)).re = (k : ℝ) := by simp
  refine ⟨τ - (k : ℂ), ?_, ?_, ?_, ?_⟩
  · simp [Complex.sub_im]
  · have h := Int.ceil_lt_add_one τ.re
    rw [← hk] at h
    have h' : (τ - (k : ℂ)).re = τ.re - (k : ℝ) := by
      simp [Complex.sub_re, hkre]
    rw [h']
    linarith
  · have h := Int.le_ceil τ.re
    rw [← hk] at h
    have h' : (τ - (k : ℂ)).re = τ.re - (k : ℝ) := by
      simp [Complex.sub_re, hkre]
    rw [h']
    linarith
  · have hshift := (periodic_extend_of_upperHalfPlane hper).zsmul (-k) τ
    have him : 0 < (τ - (k : ℂ)).im := by simp [Complex.sub_im]; exact hτ
    have hz : τ + ((-k : ℤ) • (1 : ℂ)) = τ - (k : ℂ) := by
      rw [zsmul_eq_mul]; push_cast; ring
    rw [hz] at hshift
    rw [if_pos him, if_pos hτ] at hshift
    exact hshift

/-! ## Periodicity and holomorphy of `diffF`, `tauDiffF` -/

lemma diffF_periodic (S : FunctionalEquationSolution n) (x : E n) :
    ∀ τ : ℂ, 0 < τ.im → diffF S x (τ + 1) = diffF S x τ := by
  intro τ hτ
  have h2 : S.F (τ + 1 + 1) x - 2 * S.F (τ + 1) x + S.F τ x = 0 := by
    rw [show τ + 1 + 1 = τ + 2 by ring]
    exact S.recur_F τ x hτ
  simp only [diffF_apply]
  linear_combination h2

lemma tauDiffF_periodic (S : FunctionalEquationSolution n) (x : E n) :
    ∀ τ : ℂ, 0 < τ.im → tauDiffF S x (τ + 1) = tauDiffF S x τ := by
  intro τ hτ
  have hper := diffF_periodic S x τ hτ
  simp only [tauDiffF_apply, diffF_apply] at hper ⊢
  rw [hper]
  ring

lemma diffF_differentiableOn (S : FunctionalEquationSolution n) (x : E n) :
    DifferentiableOn ℂ (diffF S x) {τ : ℂ | 0 < τ.im} := by
  have hmap : Set.MapsTo (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} {τ : ℂ | 0 < τ.im} := by
    intro τ hτ
    simpa using hτ
  have hcomp : DifferentiableOn ℂ (fun τ : ℂ => S.F (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
    (S.holomorphic_F x).comp (by fun_prop) hmap
  have h : DifferentiableOn ℂ (fun τ : ℂ => S.F (τ + 1) x - S.F τ x) {τ : ℂ | 0 < τ.im} :=
    hcomp.sub (S.holomorphic_F x)
  exact h

lemma tauDiffF_differentiableOn (S : FunctionalEquationSolution n) (x : E n) :
    DifferentiableOn ℂ (tauDiffF S x) {τ : ℂ | 0 < τ.im} := by
  have hg : DifferentiableOn ℂ (fun τ : ℂ => S.F (τ + 1) x - S.F τ x) {τ : ℂ | 0 < τ.im} := by
    have hmap : Set.MapsTo (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} {τ : ℂ | 0 < τ.im} := by
      intro τ hτ
      simpa using hτ
    have hcomp : DifferentiableOn ℂ (fun τ : ℂ => S.F (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
      (S.holomorphic_F x).comp (by fun_prop) hmap
    exact hcomp.sub (S.holomorphic_F x)
  have h1 : DifferentiableOn ℂ (fun τ : ℂ => τ * (S.F (τ + 1) x - S.F τ x))
      {τ : ℂ | 0 < τ.im} :=
    (differentiableOn_id (𝕜 := ℂ)).mul hg
  have h : DifferentiableOn ℂ (fun τ : ℂ => S.F τ x - τ * (S.F (τ + 1) x - S.F τ x))
      {τ : ℂ | 0 < τ.im} := (S.holomorphic_F x).sub h1
  exact h

/-! ## Strip bounds -/

/-- In the strip `-1 ≤ Re τ ≤ 0` the difference `F(τ+1,x) - F(τ,x)` is bounded by
`2 α y^{-β}`. -/
lemma norm_diffF_le_of_strip (S : FunctionalEquationSolution n) (x : E n)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    {τ : ℂ} (hτ : 0 < τ.im) (h1 : -1 ≤ τ.re) (h2 : τ.re ≤ 0) :
    ‖diffF S x τ‖ ≤ 2 * α * τ.im ^ (-β) := by
  have hτ1 : 0 < (τ + 1).im := by simpa using hτ
  have hre1 : -1 ≤ (τ + 1).re := by simp [Complex.add_re]; linarith
  have hre2 : (τ + 1).re ≤ 1 := by simp [Complex.add_re]; linarith
  calc ‖diffF S x τ‖ = ‖S.F (τ + 1) x - S.F τ x‖ := rfl
    _ ≤ ‖S.F (τ + 1) x‖ + ‖S.F τ x‖ := norm_sub_le _ _
    _ ≤ α * τ.im ^ (-β) + α * τ.im ^ (-β) := by
        refine add_le_add ?_ (hstrip τ x hτ h1 (by linarith))
        simpa using hstrip (τ + 1) x hτ1 hre1 hre2
    _ = 2 * α * τ.im ^ (-β) := by ring

/-- The same bound everywhere on the upper half plane, by periodicity. -/
lemma norm_diffF_le (S : FunctionalEquationSolution n) (x : E n)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β)) :
    ∀ τ : ℂ, 0 < τ.im → ‖diffF S x τ‖ ≤ 2 * α * τ.im ^ (-β) := by
  intro τ hτ
  obtain ⟨τ', him, hre1, hre2, heq⟩ := exists_periodic_reduce (diffF_periodic S x) τ hτ
  have hτ' : 0 < τ'.im := by rw [him]; exact hτ
  rw [← heq, ← him]
  exact norm_diffF_le_of_strip S x hstrip hτ' hre1 hre2

/-- In the strip `-1 ≤ Re τ ≤ 0` the combination `F(τ,x) - τ (F(τ+1,x) - F(τ,x))` is
bounded by `α y^{-β} + (1+y) ‖diffF S x τ‖`. -/
lemma norm_tauDiffF_le (S : FunctionalEquationSolution n) (x : E n)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    {τ : ℂ} (hτ : 0 < τ.im) (h1 : -1 ≤ τ.re) (h2 : τ.re ≤ 0) :
    ‖tauDiffF S x τ‖ ≤ α * τ.im ^ (-β) + (1 + τ.im) * ‖diffF S x τ‖ := by
  have hnorm : ‖τ‖ ≤ 1 + τ.im := by
    have hsq : ‖τ‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hre : τ.re ^ 2 ≤ 1 := by nlinarith [h1, h2]
    nlinarith [norm_nonneg τ, hτ, hsq, hre]
  calc ‖tauDiffF S x τ‖ = ‖S.F τ x - τ * (S.F (τ + 1) x - S.F τ x)‖ := rfl
    _ ≤ ‖S.F τ x‖ + ‖τ * (S.F (τ + 1) x - S.F τ x)‖ := norm_sub_le _ _
    _ = ‖S.F τ x‖ + ‖τ‖ * ‖diffF S x τ‖ := by rw [norm_mul]; rfl
    _ ≤ α * τ.im ^ (-β) + (1 + τ.im) * ‖diffF S x τ‖ := by
        refine add_le_add (hstrip τ x hτ h1 (by linarith)) ?_
        exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-! ## The size of a Dirichlet series -/

lemma norm_exp_two_pi_I_nat_sub {k : ℕ} {τ : ℂ} :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)‖ =
      Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * τ.im)) := by
  rw [← Complex.re_add_im τ]
  simpa using norm_exp_two_pi_I_nat k τ.re τ.im

/-- A Dirichlet series with coefficients `c` is dominated, pointwise, by the norm sum
`dirichletNormSum c (Im τ)`. -/
lemma norm_le_dirichletNormSum {c : ℕ → ℂ} {g : ℂ → ℂ}
    (hc : ∀ τ : ℂ, 0 < τ.im → HasSum (fun k : ℕ =>
      c k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)) (g τ))
    {τ : ℂ} (hτ : 0 < τ.im) :
    ‖g τ‖ ≤ dirichletNormSum c τ.im := by
  have hsum := (hc τ hτ).summable
  calc ‖g τ‖ = ‖∑' k : ℕ, c k * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)‖ := by
        rw [(hc τ hτ).tsum_eq]
    _ ≤ ∑' k : ℕ, ‖c k * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ = dirichletNormSum c τ.im := by
        refine tsum_congr fun k => ?_
        rw [norm_mul, norm_exp_two_pi_I_nat_sub]

/-! ## The comparison function `tauDiffM` and elementary decay estimates -/

/-- The comparison function bounding `‖tauDiffF S x τ‖` in terms of `Im τ`: the crude strip
bound `5α y^{-β}` for `y ≤ 1`, and `α y^{-β} + (1+y) Φ(y)` above it, where `Φ` is the norm
sum of the Dirichlet coefficients of `diffF`. -/
def tauDiffM (α β : ℝ) (c : ℕ → ℂ) (y : ℝ) : ℝ :=
  if y ≤ 1 then 5 * α * y ^ (-β) else α * y ^ (-β) + (1 + y) * dirichletNormSum c y

lemma exp_neg_two_pi_mul_pow (m : ℕ) (y : ℝ) :
    Real.exp (-(2 * Real.pi) * y) ^ m = Real.exp (-(2 * Real.pi * m) * y) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- `y ≤ e^{π y}` for `y ≥ 0`. -/
lemma le_exp_pi_mul {y : ℝ} (hy : 0 ≤ y) : y ≤ Real.exp (Real.pi * y) := by
  have h1 : 1 + Real.pi * y ≤ Real.exp (Real.pi * y) := by
    have := Real.add_one_le_exp (Real.pi * y)
    linarith
  by_cases h : y ≤ 1
  · nlinarith [Real.pi_pos]
  · push_neg at h
    have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [h1, h, hy, hp]

/-- `y e^{-π y} ≤ 1` for `y ≥ 0`. -/
lemma mul_exp_neg_pi_le_one {y : ℝ} (hy : 0 ≤ y) : y * Real.exp (-(Real.pi * y)) ≤ 1 := by
  have he : 0 < Real.exp (Real.pi * y) := Real.exp_pos _
  rw [Real.exp_neg, mul_inv_le_iff₀ he]
  simpa using le_exp_pi_mul hy

/-- `y ^ (-β)` times a power of `e^{-2πy}` tends to `0` at `+∞`. -/
lemma tendsto_rpow_neg_mul_exp {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    Tendsto (fun y : ℝ => y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, mul_one]
    have h : Tendsto (fun y : ℝ => (y ^ β)⁻¹) atTop (𝓝 0) :=
      (tendsto_rpow_atTop hβ).inv_tendsto_atTop
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy.le]
  · have hb : (0 : ℝ) < 2 * Real.pi * m := by positivity
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β) (2 * Real.pi * m) hb
    refine h.congr' ?_
    filter_upwards with y
    rw [exp_neg_two_pi_mul_pow]

/-- The comparison function `fun y => 2 * α * y^{-β}` satisfies the decay hypothesis of
`DirichletExpansion`. -/
lemma tendsto_const_mul_rpow_neg_mul_exp (α β : ℝ) (hβ : 0 < β) (m : ℕ) :
    Tendsto (fun y : ℝ => 2 * α * y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m)
      atTop (𝓝 0) := by
  simpa [mul_assoc] using (tendsto_rpow_neg_mul_exp hβ m).const_mul (2 * α)

end

end Work.FunctionalEquations
