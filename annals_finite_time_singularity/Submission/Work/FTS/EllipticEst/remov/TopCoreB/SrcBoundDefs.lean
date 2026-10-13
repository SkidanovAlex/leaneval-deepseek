import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/SrcBoundDefs`: the vocabulary of the source bound `srcBound`

The target `Work.FTS.EllipticEst.remov.TopCoreB.srcBound` bounds the
`sin(2θ)^{2k-γ}`-weighted `∂_θ^k`-norm of the *angular source*

  `G = F + α²·z²∂_z²Ψ + α(5+α)·D_zΨ`

(the right-hand side of the equation `Lzero1(Ψ z ·) = G`, i.e. `bslOp α Ψ = F` with the radial
part moved over) by the `ℋ^k`-slot quantities appearing on the right-hand side of the paper's
source estimate.  This module fixes the small vocabulary:

* `Abar Ψ = z²∂_z²Ψ` -- the second radial source term,
* `SrcG α F Ψ = F + α²·Abar Ψ + α(5+α)·D_zΨ` -- the angular source,
* `Maj α k cF cA cB F Ψ` -- the pointwise majorant of the source integrand obtained from the
  three slot recursions: the `∂_θ`-slots of `F` resp. `Abar Ψ` at order `≤ k` and of
  `∂_θ²(D_zΨ)` at order `≤ k-2`, weighted by `Wt α = w·sin(2θ)^{-γ/2}`.

All declarations here are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- `A = z²∂_z²Ψ`, the second term of the angular source (with its coefficient `α²`). -/
def Abar (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

@[simp] theorem Abar_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Abar Ψ z θ = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl

/-- The angular source `G = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` of the equation `Lzero1(Ψ z ·) = G`. -/
def SrcG (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ + α ^ 2 * Abar Ψ z θ + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ

@[simp] theorem SrcG_apply (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    SrcG α F Ψ z θ = F z θ + α ^ 2 * Abar Ψ z θ
      + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ := rfl

/-- The `j`-th angular slot of `X` against the mixed weight `Wt α` at fixed `(z,θ)`:
`(D_θ^j X · Wt α)²`. -/
def slot (α : ℝ) (j : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.mixed 0 j X z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The pointwise majorant of the source integrand produced by the three slot recursions: the
`∂_θ`-slots of `F` and of `Abar Ψ` of order `≤ k`, and the `∂_θ`-slots of
`∂_θ²(D_zΨ)` of order `≤ k-2`, with the coefficients of the source. -/
def Maj (α : ℝ) (k : ℕ) (cF cA cB : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    3 * cF * (∑ r ∈ Finset.Icc 1 k, slot α r F z θ)
      + 3 * α ^ 4 * cA * (∑ r ∈ Finset.Icc 1 k, slot α r (Abar Ψ) z θ)
      + 3 * (α * (5 + α)) ^ 2 * cB
          * (∑ r ∈ Finset.Icc 1 (k - 2),
              slot α r (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ)

theorem slot_nonneg (α : ℝ) (j : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ slot α j X z θ :=
  sq_nonneg _

theorem Maj_nonneg (α : ℝ) (k : ℕ) (cF cA cB : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hcF : 0 ≤ cF) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hα : 0 ≤ α) :
    0 ≤ Maj α k cF cA cB F Ψ z θ := by
  have h1 : 0 ≤ ∑ r ∈ Finset.Icc 1 k, slot α r F z θ :=
    Finset.sum_nonneg fun r _ => slot_nonneg α r F z θ
  have h2 : 0 ≤ ∑ r ∈ Finset.Icc 1 k, slot α r (Abar Ψ) z θ :=
    Finset.sum_nonneg fun r _ => slot_nonneg α r (Abar Ψ) z θ
  have h3 : 0 ≤ ∑ r ∈ Finset.Icc 1 (k - 2),
      slot α r (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ :=
    Finset.sum_nonneg fun r _ => slot_nonneg α r _ z θ
  simp only [Maj]
  have hα2 : (0 : ℝ) ≤ α * (5 + α) := by nlinarith
  have h4 : (0 : ℝ) ≤ 3 * cF * (∑ r ∈ Finset.Icc 1 k, slot α r F z θ) := by positivity
  have h5 : (0 : ℝ) ≤ 3 * α ^ 4 * cA * (∑ r ∈ Finset.Icc 1 k, slot α r (Abar Ψ) z θ) := by
    have : (0:ℝ) ≤ α ^ 4 := by positivity
    positivity
  have h6 : (0 : ℝ) ≤ 3 * (α * (5 + α)) ^ 2 * cB
      * (∑ r ∈ Finset.Icc 1 (k - 2),
          slot α r (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) := by positivity
  linarith [h4, h5, h6]

end Work.FTS.EllipticEst.remov.TopCoreB
