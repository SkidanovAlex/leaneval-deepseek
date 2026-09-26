import Submission.Work.FunctionalEquations.TauDifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.DifferenceExpansionF
import Submission.Work.CKFinal.Shadow.TauDiffSetup

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsto_const_mul_rpow_neg_mul_exp)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (norm_exp_neg_two_pi_I_nat)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (dirichletNormSum)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tildeDiff_phi_bound)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tauDiffM)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (norm_le_dirichletNormSum)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tildeTauDiffM_props)
end Work.FunctionalEquations

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


end Work.CKFinal.Shadow
