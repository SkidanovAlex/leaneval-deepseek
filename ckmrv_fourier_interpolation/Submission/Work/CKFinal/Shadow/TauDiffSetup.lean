import Submission.Work.FunctionalEquations.TauDiffSetup
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (exists_periodic_reduce)
end Work.FunctionalEquations

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

@[simp] lemma diffF_apply (S : FunctionalEquationSolution n) (x : E n) (τ : ℂ) :
    diffF S x τ = S.F (τ + 1) x - S.F τ x := rfl

@[simp] lemma tauDiffF_apply (S : FunctionalEquationSolution n) (x : E n) (τ : ℂ) :
    tauDiffF S x τ = S.F τ x - τ * (S.F (τ + 1) x - S.F τ x) := rfl

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

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
