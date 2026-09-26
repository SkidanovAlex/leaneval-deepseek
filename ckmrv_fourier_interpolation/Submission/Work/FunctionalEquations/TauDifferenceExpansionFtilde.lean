import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DirichletExpansion
import Submission.Work.FunctionalEquations.TauDiffSetup
import Submission.Work.FunctionalEquations.DifferenceExpansionF

/-!
# The `τ`-difference expansion of `F̃`

This file proves the `F̃`-counterpart of `TauDifferenceExpansionF`: for a solution `S`
of the functional equations of CKMRV Theorem 3.1, the combination

`F̃(τ,x) - τ (F̃(τ+1,x) - F̃(τ,x))`

is `1`-periodic in `τ`, holomorphic on the upper half plane, and bounded by the Dirichlet
norm sum of the coefficients of `F̃(τ+1,x) - F̃(τ,x)`; hence it has an absolutely
convergent Dirichlet expansion, whose coefficients are the contour integrals along any
horizontal line `Im τ = y > 0`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-- `F̃(τ+1,x) - F̃(τ,x)`. -/
def tildeDiff (S : FunctionalEquationSolution n) (x : E n) : ℂ → ℂ :=
  fun τ => S.Ftilde (τ + 1) x - S.Ftilde τ x

/-- `F̃(τ,x) - τ (F̃(τ+1,x) - F̃(τ,x))`, the function whose Dirichlet coefficients are the
`ã`-coefficients of CKMRV (3.2). -/
def tildeTauDiff (S : FunctionalEquationSolution n) (x : E n) : ℂ → ℂ :=
  fun τ => S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x)

@[simp] lemma tildeDiff_apply (S : FunctionalEquationSolution n) (x : E n) (τ : ℂ) :
    tildeDiff S x τ = S.Ftilde (τ + 1) x - S.Ftilde τ x := rfl

@[simp] lemma tildeTauDiff_apply (S : FunctionalEquationSolution n) (x : E n) (τ : ℂ) :
    tildeTauDiff S x τ = S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x) := rfl

lemma tildeDiff_periodic (S : FunctionalEquationSolution n) (x : E n) :
    ∀ τ : ℂ, 0 < τ.im → tildeDiff S x (τ + 1) = tildeDiff S x τ := by
  intro τ hτ
  have h2 : S.Ftilde (τ + 2) x - 2 * S.Ftilde (τ + 1) x + S.Ftilde τ x = 0 :=
    S.recur_Ftilde τ x hτ
  simp only [tildeDiff]
  rw [show τ + 1 + 1 = τ + 2 from by ring]
  linear_combination h2

lemma tildeTauDiff_periodic (S : FunctionalEquationSolution n) (x : E n) :
    ∀ τ : ℂ, 0 < τ.im → tildeTauDiff S x (τ + 1) = tildeTauDiff S x τ := by
  intro τ hτ
  have hper : tildeDiff S x (τ + 1) = tildeDiff S x τ := tildeDiff_periodic S x τ hτ
  rw [tildeTauDiff_apply, tildeTauDiff_apply]
  simp only [tildeDiff] at hper
  rw [hper]
  ring

lemma tildeDiff_differentiableOn (S : FunctionalEquationSolution n) (x : E n) :
    DifferentiableOn ℂ (tildeDiff S x) {τ : ℂ | 0 < τ.im} := by
  have hmap : Set.MapsTo (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} {τ : ℂ | 0 < τ.im} := by
    intro τ hτ; simpa using hτ
  have hcomp : DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
    (S.holomorphic_Ftilde x).comp (by fun_prop) hmap
  have h := hcomp.sub (S.holomorphic_Ftilde x)
  change DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) {τ : ℂ | 0 < τ.im}
  exact h

lemma tildeTauDiff_differentiableOn (S : FunctionalEquationSolution n) (x : E n) :
    DifferentiableOn ℂ (tildeTauDiff S x) {τ : ℂ | 0 < τ.im} := by
  have hg : DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x)
      {τ : ℂ | 0 < τ.im} := by
    have hmap : Set.MapsTo (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} {τ : ℂ | 0 < τ.im} := by
      intro τ hτ; simpa using hτ
    have hcomp : DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
      (S.holomorphic_Ftilde x).comp (by fun_prop) hmap
    exact hcomp.sub (S.holomorphic_Ftilde x)
  have h1 : DifferentiableOn ℂ (fun τ : ℂ => τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x))
      {τ : ℂ | 0 < τ.im} :=
    (differentiableOn_id (𝕜 := ℂ)).mul hg
  have h := (S.holomorphic_Ftilde x).sub h1
  change DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x))
    {τ : ℂ | 0 < τ.im}
  exact h

lemma norm_tildeDiff_le_of_strip (S : FunctionalEquationSolution n) (x : E n)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.Ftilde τ z‖ ≤ α * τ.im ^ (-β))
    {τ : ℂ} (hτ : 0 < τ.im) (h1 : -1 ≤ τ.re) (h2 : τ.re ≤ 0) :
    ‖tildeDiff S x τ‖ ≤ 2 * α * τ.im ^ (-β) := by
  have hτ1 : 0 < (τ + 1).im := by simpa using hτ
  have hre1 : -1 ≤ (τ + 1).re := by simp [Complex.add_re]; linarith
  have hre2 : (τ + 1).re ≤ 1 := by simp [Complex.add_re]; linarith
  calc ‖tildeDiff S x τ‖ = ‖S.Ftilde (τ + 1) x - S.Ftilde τ x‖ := rfl
    _ ≤ ‖S.Ftilde (τ + 1) x‖ + ‖S.Ftilde τ x‖ := norm_sub_le _ _
    _ ≤ α * τ.im ^ (-β) + α * τ.im ^ (-β) := by
        refine add_le_add ?_ (hstrip τ x hτ h1 (by linarith))
        simpa using hstrip (τ + 1) x hτ1 hre1 hre2
    _ = 2 * α * τ.im ^ (-β) := by ring

lemma norm_tildeDiff_le (S : FunctionalEquationSolution n) (x : E n)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.Ftilde τ z‖ ≤ α * τ.im ^ (-β)) :
    ∀ τ : ℂ, 0 < τ.im → ‖tildeDiff S x τ‖ ≤ 2 * α * τ.im ^ (-β) := by
  intro τ hτ
  obtain ⟨τ', him, hre1, hre2, heq⟩ := exists_periodic_reduce (tildeDiff_periodic S x) τ hτ
  have hτ' : 0 < τ'.im := by rw [him]; exact hτ
  rw [← heq, ← him]
  exact norm_tildeDiff_le_of_strip S x hstrip hτ' hre1 hre2

lemma norm_tildeTauDiff_le (S : FunctionalEquationSolution n) (x : E n)
    {α β : ℝ} (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.Ftilde τ z‖ ≤ α * τ.im ^ (-β))
    {τ : ℂ} (hτ : 0 < τ.im) (h1 : -1 ≤ τ.re) (h2 : τ.re ≤ 0) :
    ‖tildeTauDiff S x τ‖ ≤ α * τ.im ^ (-β) + (1 + τ.im) * ‖tildeDiff S x τ‖ := by
  have hnorm : ‖τ‖ ≤ 1 + τ.im := by
    have hsq : ‖τ‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hre : τ.re ^ 2 ≤ 1 := by nlinarith [h1, h2]
    nlinarith [norm_nonneg τ, hτ, hsq, hre]
  calc ‖tildeTauDiff S x τ‖ = ‖S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x)‖ := rfl
    _ ≤ ‖S.Ftilde τ x‖ + ‖τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x)‖ := norm_sub_le _ _
    _ = ‖S.Ftilde τ x‖ + ‖τ‖ * ‖tildeDiff S x τ‖ := by rw [norm_mul]; rfl
    _ ≤ α * τ.im ^ (-β) + (1 + τ.im) * ‖tildeDiff S x τ‖ := by
        refine add_le_add (hstrip τ x hτ h1 (by linarith)) ?_
        exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- **The Dirichlet expansion of `F̃(τ+1,x) - F̃(τ,x)`** (paper (3.3)): the difference is
`1`-periodic, holomorphic, and bounded by `2α (Im τ)^{-β}` in the upper half plane, so it
has an absolutely convergent Dirichlet series with coefficients given by the contour
integrals along any horizontal line `Im τ = y > 0`. -/
lemma tildeDiff_expansion (S : FunctionalEquationSolution n) (x : E n) :
    ∃ c : ℕ → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun k : ℕ =>
          c k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ))
        (tildeDiff S x τ)) ∧
      (∀ (k : ℕ) (y : ℝ), 0 < y → c k = ∫ t in (0 : ℝ)..1,
        tildeDiff S x ((t : ℂ) + (y : ℂ) * Complex.I) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
            * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨α, β, hα0, hβpos, hunif⟩ := S.uniform_Ftilde
  exact DirichletExpansion (tildeDiff S x)
    (tildeDiff_periodic S x) (tildeDiff_differentiableOn S x) (fun y => 2 * α * y ^ (-β))
    (norm_tildeDiff_le S x hunif)
    ⟨2 * α, β, by linarith, le_of_lt hβpos, fun y _ => le_refl _⟩
    (fun m => tendsto_const_mul_rpow_neg_mul_exp α β hβpos m)

/-! ### Bounds on the coefficients of the `F̃`-difference -/

/-- The coefficients `c` of the expansion of `F̃(τ+1,x) - F̃(τ,x)` are bounded by
evaluating the contour integral on a line at half the height: `‖c k‖ ≤ 2α (y/2)^{-β}
e^{π(k+1)y}`. -/
lemma tildeDiff_coeff_bound (S : FunctionalEquationSolution n) (x : E n) (c : ℕ → ℂ)
    (hc : ∀ (k : ℕ) (y : ℝ), 0 < y → c k = ∫ t in (0 : ℝ)..1,
        tildeDiff S x ((t : ℂ) + ((y : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
            * ((t : ℂ) + ((y : ℝ) : ℂ) * Complex.I))))
    {α β : ℝ}
    (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.Ftilde τ z‖ ≤ α * τ.im ^ (-β))
    (k : ℕ) (y : ℝ) (hy : 0 < y) :
    ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
  have hy2 : 0 < y / 2 := by linarith
  rw [hc k (y / 2) hy2]
  set C : ℝ := 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) with hC
  have hbnorm : ∀ t : ℝ, ‖tildeDiff S x ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
          * ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)))‖ ≤ C := by
    intro t
    have him : ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I).im = y / 2 := by
      simp [Complex.add_im, Complex.mul_im]
    have h1 : ‖tildeDiff S x ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * α * (y / 2) ^ (-β) := by
      have := norm_tildeDiff_le S x hstrip ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)
        (by rw [him]; linarith)
      rwa [him] at this
    rw [norm_mul, norm_exp_neg_two_pi_I_nat k t (y / 2)]
    have hexp : Real.exp (2 * Real.pi * ((k : ℝ) + 1) * (y / 2))
        = Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
      congr 1; ring
    rw [hexp, hC]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := C)
    (f := fun t : ℝ => tildeDiff S x ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
          * ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I))))
    (fun t _ => hbnorm t)
  simpa using this

/-- From the coefficient bound to a bound on the Dirichlet norm sum, by summing the
geometric series `∑_k e^{-π(k+1)y}`. -/
lemma tildeDiff_phi_bound (c : ℕ → ℂ) {α β : ℝ} (_hα : 0 ≤ α)
    (hbound : ∀ (k : ℕ) (y : ℝ), 0 < y →
      ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y))
    {y : ℝ} (hy : 0 < y) :
    dirichletNormSum c y ≤ 2 * α * (y / 2) ^ (-β) *
      (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := by
  set r : ℝ := Real.exp (-(Real.pi * y)) with hr
  have hrpos : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hrlt : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy]
  have hnormlt : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hrlt
  have hterm : ∀ k : ℕ, ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))
      ≤ (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1) := by
    intro k
    have hb := hbound k y hy
    have hfac : Real.exp (Real.pi * ((k : ℝ) + 1) * y)
        * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) = r ^ (k + 1) := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    calc ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))
        ≤ (2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y))
            * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = 2 * α * (y / 2) ^ (-β) * (Real.exp (Real.pi * ((k : ℝ) + 1) * y)
            * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))) := by ring
      _ = (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1) := by rw [hfac]
  have hgeo : Summable (fun k : ℕ => (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1)) := by
    have hbase : Summable (fun k : ℕ => ((2 * α * (y / 2) ^ (-β)) * r) * r ^ k) :=
      (summable_geometric_of_norm_lt_one hnormlt).mul_left _
    refine hbase.congr (fun k => ?_)
    rw [pow_succ]; ring
  have hf : Summable (fun k : ℕ => ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hterm k) hgeo
  have htsum : ∑' k : ℕ, r ^ (k + 1) = r / (1 - r) := by
    have h1 : HasSum (fun k : ℕ => r ^ (k + 1)) (r * (1 - r)⁻¹) := by
      have h0 : HasSum (fun k : ℕ => r * r ^ k) (r * (1 - r)⁻¹) :=
        (hasSum_geometric_of_norm_lt_one hnormlt).mul_left r
      have hfun : (fun k : ℕ => r * r ^ k) = (fun k : ℕ => r ^ (k + 1)) := by
        funext k; rw [pow_succ]; ring
      rwa [hfun] at h0
    rw [div_eq_mul_inv]
    exact h1.tsum_eq
  rw [dirichletNormSum]
  calc ∑' k : ℕ, ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))
      ≤ ∑' k : ℕ, (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1) :=
        Summable.tsum_le_tsum (fun k => hterm k) hf hgeo
    _ = (2 * α * (y / 2) ^ (-β)) * (r / (1 - r)) := by
        rw [tsum_mul_left, htsum]
    _ = 2 * α * (y / 2) ^ (-β) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := by
        rw [hr]

/-! ### The comparison function `tauDiffM` -/

/-- The two properties of `tauDiffM α β c` needed for `DirichletExpansion`: a power bound
and the decay of `tauDiffM α β c y * e^{-2πmy}`. -/
lemma tildeTauDiffM_props (c : ℕ → ℂ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hφ : ∀ y : ℝ, 0 < y → dirichletNormSum c y ≤
      2 * α * (y / 2) ^ (-β) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) :
    (∃ A β' : ℝ, 0 ≤ A ∧ 0 ≤ β' ∧ ∀ y : ℝ, 0 < y → tauDiffM α β c y ≤ A * y ^ (-β')) ∧
    (∀ m : ℕ, Tendsto (fun y : ℝ =>
      tauDiffM α β c y * Real.exp (-(2 * Real.pi) * y) ^ m) atTop (𝓝 0)) := by
  have hφ0 : ∀ y : ℝ, 0 < y → 0 ≤ dirichletNormSum c y := by
    intro y _
    rw [dirichletNormSum]
    exact tsum_nonneg (fun k => by positivity)
  have hgeo : ∀ y : ℝ, 1 < y →
      (1 + y) * Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))) ≤ 4 := by
    intro y hy1
    have hy : 0 < y := by linarith
    have hr1 : Real.exp (-(Real.pi * y)) ≤ 1 / 2 := by
      have hpiy : (1 : ℝ) < Real.pi * y := by nlinarith [Real.pi_gt_three, hy1]
      have hexp : (2 : ℝ) < Real.exp (Real.pi * y) :=
        lt_trans Real.exp_one_gt_two (Real.exp_lt_exp.mpr hpiy)
      rw [Real.exp_neg, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
      exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).mpr hexp |>.le
    have hr2 : (1 + y) * Real.exp (-(Real.pi * y)) ≤ 2 := by
      have h1 := mul_exp_neg_pi_le_one hy.le
      have h2 : Real.exp (-(Real.pi * y)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hy]
      linarith
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - Real.exp (-(Real.pi * y)))]
    nlinarith [hr1, hr2]
  have hrpow : ∀ y : ℝ, 0 < y → (y / 2) ^ (-β) = (2 : ℝ) ^ β * y ^ (-β) := by
    intro y hy
    have h2inv : ((2 : ℝ) ^ (-β))⁻¹ = (2 : ℝ) ^ β := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
    rw [show y / 2 = y * (2 : ℝ)⁻¹ by ring]
    rw [Real.mul_rpow hy.le (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    rw [Real.inv_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ)), h2inv]
    ring
  have hfac : ∀ y : ℝ, 1 < y →
      (1 + y) * dirichletNormSum c y ≤ 8 * α * (2 : ℝ) ^ β * y ^ (-β) := by
    intro y hy1
    have hy : 0 < y := by linarith
    have h2 := mul_le_mul_of_nonneg_left (hφ y hy) (by linarith : (0 : ℝ) ≤ 1 + y)
    have hg := hgeo y hy1
    have h2a : 0 ≤ 2 * α * (2 : ℝ) ^ β * y ^ (-β) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) β)) (Real.rpow_nonneg hy.le _)
    calc (1 + y) * dirichletNormSum c y
        ≤ (1 + y) * (2 * α * (y / 2) ^ (-β)
            * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) := h2
      _ = (2 * α * (2 : ℝ) ^ β * y ^ (-β))
            * ((1 + y) * Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := by
          rw [hrpow y hy]; ring
      _ ≤ (2 * α * (2 : ℝ) ^ β * y ^ (-β)) * 4 := mul_le_mul_of_nonneg_left hg h2a
      _ = 8 * α * (2 : ℝ) ^ β * y ^ (-β) := by ring
  refine ⟨?_, ?_⟩
  · refine ⟨max (5 * α) (α * (1 + 8 * (2 : ℝ) ^ β)), β,
      le_trans (by linarith : (0 : ℝ) ≤ 5 * α) (le_max_left _ _), le_of_lt hβ, ?_⟩
    intro y hy
    by_cases hle : y ≤ 1
    · rw [tauDiffM, if_pos hle]
      have hyb : 0 ≤ y ^ (-β) := Real.rpow_nonneg hy.le _
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hyb
    · rw [tauDiffM, if_neg hle]
      have hy1 : 1 < y := not_le.mp hle
      have hf := hfac y hy1
      have hyb : 0 ≤ y ^ (-β) := Real.rpow_nonneg hy.le _
      have hkey : α * y ^ (-β) + (1 + y) * dirichletNormSum c y
          ≤ (α * (1 + 8 * (2 : ℝ) ^ β)) * y ^ (-β) := by nlinarith [hf]
      calc α * y ^ (-β) + (1 + y) * dirichletNormSum c y
          ≤ (α * (1 + 8 * (2 : ℝ) ^ β)) * y ^ (-β) := hkey
        _ ≤ max (5 * α) (α * (1 + 8 * (2 : ℝ) ^ β)) * y ^ (-β) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hyb
  · intro m
    set C : ℝ := α + 8 * α * (2 : ℝ) ^ β with hC
    have hupper : Tendsto (fun y : ℝ => C * y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m)
        atTop (𝓝 0) := by
      simpa [mul_assoc] using (tendsto_rpow_neg_mul_exp hβ m).const_mul C
    have hf0 : ∀ᶠ y : ℝ in atTop,
        0 ≤ tauDiffM α β c y * Real.exp (-(2 * Real.pi) * y) ^ m := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy1
      have hy : 0 < y := by linarith
      rw [tauDiffM, if_neg (not_le.mpr hy1)]
      have hφy := hφ0 y hy
      have hyb : 0 ≤ y ^ (-β) := Real.rpow_nonneg hy.le _
      have h1 : 0 ≤ α * y ^ (-β) + (1 + y) * dirichletNormSum c y :=
        add_nonneg (mul_nonneg hα hyb) (mul_nonneg (by linarith) hφy)
      exact mul_nonneg h1 (by positivity)
    have hft : ∀ᶠ y : ℝ in atTop, tauDiffM α β c y * Real.exp (-(2 * Real.pi) * y) ^ m
        ≤ C * y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy1
      have hy : 0 < y := by linarith
      rw [tauDiffM, if_neg (not_le.mpr hy1), hC]
      have hf := hfac y hy1
      have hkey : α * y ^ (-β) + (1 + y) * dirichletNormSum c y
          ≤ (α + 8 * α * (2 : ℝ) ^ β) * y ^ (-β) := by nlinarith [hf]
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    exact squeeze_zero' hf0 hft hupper

/-- **The Dirichlet expansion of `F̃(τ,x) - τ (F̃(τ+1,x) - F̃(τ,x))`** (paper (3.2)): it is
`1`-periodic and holomorphic, and bounded by `tauDiffM`, whose power bound and decay come
from the exponential decay of the coefficients of `F̃(τ+1,x) - F̃(τ,x)`. -/
lemma tildeTauDiff_expansion (S : FunctionalEquationSolution n) (x : E n) :
    ∃ c : ℕ → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun k : ℕ =>
          c k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ))
        (tildeTauDiff S x τ)) ∧
      (∀ (k : ℕ) (y : ℝ), 0 < y → c k = ∫ t in (0 : ℝ)..1,
        tildeTauDiff S x ((t : ℂ) + ((y : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
            * ((t : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))) := by
  obtain ⟨α, β, hα0, hβpos, hunif⟩ := S.uniform_Ftilde
  obtain ⟨c, hcsum, hcint⟩ := tildeDiff_expansion S x
  have hcoeff : ∀ (k : ℕ) (y : ℝ), 0 < y →
      ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) :=
    fun k y hy => tildeDiff_coeff_bound S x c hcint hunif k y hy
  have hφ : ∀ y : ℝ, 0 < y → dirichletNormSum c y ≤
      2 * α * (y / 2) ^ (-β) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) :=
    fun y hy => tildeDiff_phi_bound c hα0 hcoeff hy
  have hM : ∀ τ : ℂ, 0 < τ.im → ‖tildeTauDiff S x τ‖ ≤ tauDiffM α β c τ.im := by
    intro τ hτ
    obtain ⟨τ', him, hre1, hre2, heq⟩ :=
      exists_periodic_reduce (tildeTauDiff_periodic S x) τ hτ
    have hτ' : 0 < τ'.im := by rw [him]; exact hτ
    have hb := norm_tildeTauDiff_le S x hunif hτ' hre1 hre2
    have hyb : 0 ≤ τ'.im ^ (-β) := Real.rpow_nonneg hτ'.le _
    have h1τ : (0 : ℝ) ≤ 1 + τ'.im := by linarith
    have h2α : ‖tildeDiff S x τ'‖ ≤ 2 * α * τ'.im ^ (-β) :=
      norm_tildeDiff_le S x hunif τ' hτ'
    have hd : ‖tildeDiff S x τ'‖ ≤ dirichletNormSum c τ'.im :=
      norm_le_dirichletNormSum hcsum hτ'
    have hbasic : ‖tildeTauDiff S x τ'‖ ≤
        α * τ'.im ^ (-β) + (1 + τ'.im) * ‖tildeDiff S x τ'‖ := hb
    rw [← heq]
    rcases lt_or_ge (1 : ℝ) τ.im with hlt | hle
    · have hstep : ‖tildeTauDiff S x τ'‖ ≤
          α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im :=
        calc ‖tildeTauDiff S x τ'‖
            ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * ‖tildeDiff S x τ'‖ := hbasic
          _ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im :=
                add_le_add_right (mul_le_mul_of_nonneg_left hd h1τ) _
      rw [tauDiffM, if_neg (not_le.mpr hlt), ← him]
      exact hstep
    · have hτ'le : τ'.im ≤ 1 := by rw [him]; exact hle
      have hstep : ‖tildeTauDiff S x τ'‖ ≤ 5 * α * τ'.im ^ (-β) := by
        have h35 : 3 + 2 * τ'.im ≤ 5 := by linarith
        calc ‖tildeTauDiff S x τ'‖
            ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * ‖tildeDiff S x τ'‖ := hbasic
          _ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * (2 * α * τ'.im ^ (-β)) :=
                add_le_add_right (mul_le_mul_of_nonneg_left h2α h1τ) _
          _ = α * (3 + 2 * τ'.im) * τ'.im ^ (-β) := by ring
          _ ≤ 5 * α * τ'.im ^ (-β) := by
                calc α * (3 + 2 * τ'.im) * τ'.im ^ (-β)
                    ≤ (α * 5) * τ'.im ^ (-β) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h35 hα0) hyb
                  _ = 5 * α * τ'.im ^ (-β) := by ring
      rw [tauDiffM, if_pos hle, ← him]
      exact hstep
  obtain ⟨hMbd, hdec⟩ := tildeTauDiffM_props c hα0 hβpos hφ
  exact DirichletExpansion (tildeTauDiff S x) (tildeTauDiff_periodic S x)
    (tildeTauDiff_differentiableOn S x) (tauDiffM α β c) hM hMbd hdec

/-- **CKMRV (3.2), the `τ`-difference of `F̃`**: for a solution of the functional equations
and each `x`, the function `F̃(τ,x) - τ (F̃(τ+1,x) - F̃(τ,x))` has an absolutely convergent
Dirichlet expansion with frequencies `1, 2, 3, …`, whose coefficients are the contour
integrals along any horizontal line `Im τ = y > 0`. -/
theorem TauDifferenceExpansionFtilde {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) :
    ∃ a : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          a m * Work.FE.dirichletTerm m.1 τ)
        (S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x))) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        a m = ∫ t in (0 : ℝ)..1,
          (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x
            - ((t : ℂ) + (y : ℂ) * Complex.I) * (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
              - S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
              * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨c, hcsum, hcint⟩ := tildeTauDiff_expansion S x
  refine ⟨fun m => c (m.1 - 1), ?_, ?_⟩
  · intro τ hτ
    have hshift := hasSum_nat_shift (c := c) (τ := τ) (hcsum τ hτ)
    have hdir : (fun m : Set.Ici (1 : ℕ) => c (m.1 - 1) * dirichletTerm m.1 τ)
        = (fun m : Set.Ici (1 : ℕ) => c (m.1 - 1) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * τ)) := by
      funext m; rw [dirichletTerm]
    rw [hdir]
    simpa only [tildeTauDiff_apply] using hshift
  · intro m y hy
    have h1 := hcint (m.1 - 1) y hy
    change c (m.1 - 1) = _
    rw [h1]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [tildeTauDiff_apply]
    rw [show ((m.1 - 1 : ℕ) : ℂ) + 1 = (m.1 : ℂ) from by
      rw [Nat.cast_sub m.2]; ring]

end

end Work.FunctionalEquations
