import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.MollDefs
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Dpair q Φ ψ = ∫ ⟪Φ − ∇q, ψ⟫` for smooth data

`Work.FTS.PressureOn.Dpair` is defined as

  `Dpair q Φ f = ∫ x, ⟪Φ x, f x⟫ + ∫ x, q x * div f x`,

i.e. the pairing `⟨Φ − ∇q, f⟩` of the distribution `D := Φ − ∇q` against `f` in the sense of
Schwartz distributions.  The present lemma identifies it, for `q` smooth and `ψ` a smooth
compactly supported test field, with the ordinary integral of `⟪Φ − ∇q, ψ⟫`.

The proof is one integration by parts, `∫ q · div ψ = −∫ ⟪∇q, ψ⟫`
(`Auxiliary.integral_mul_div_eq_neg_inner_gradient`, which is the divergence theorem applied to
`q • ψ`), combined with the linearity of the integral:

  `Dpair q Φ ψ = ∫ ⟪Φ, ψ⟫ + ∫ q · div ψ = ∫ ⟪Φ, ψ⟫ − ∫ ⟪∇q, ψ⟫ = ∫ ⟪Φ − ∇q, ψ⟫`.
-/

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory Filter Set
open scoped Topology

theorem Dpair_eq_integral_sub_gradient_of_smooth
    (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : ∀ n : ℕ, ContDiff ℝ n q) (hΦ : Continuous Φ)
    (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hψc : HasCompactSupport ψ) :
    Work.FTS.PressureOn.Dpair q Φ ψ
      = ∫ x, inner ℝ (Φ x - gradient q x) (ψ x) := by
  -- `∇q` is continuous (indeed `C¹`)
  have hgrad : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => gradient q x) :=
    (Work.FTS.PressureOn.Green.contDiff_gradient q (hq 2)).continuous
  -- anything paired with `ψ` against a field `G` is compactly supported
  have aux : ∀ (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      HasCompactSupport (fun x => inner ℝ (G x) (ψ x)) := by
    intro G
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro x hx
    by_contra hx'
    exact hx (by simp only [image_eq_zero_of_notMem_tsupport hx', inner_zero_right])
  have hI1 : Integrable (fun x => inner ℝ (Φ x) (ψ x)) :=
    (hΦ.inner (hψ 0).continuous).integrable_of_hasCompactSupport (aux Φ)
  have hI2 : Integrable (fun x => inner ℝ (gradient q x) (ψ x)) :=
    (hgrad.inner (hψ 0).continuous).integrable_of_hasCompactSupport (aux (fun x => gradient q x))
  -- the integration by parts
  have hibp : ∫ x, q x * FiniteTimeSingularity.div ψ x
      = -∫ x, inner ℝ (gradient q x) (ψ x) :=
    Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient q ψ hq hψ hψc
  -- linearity of the integral
  have key : (∫ x, inner ℝ (Φ x) (ψ x)) - ∫ x, inner ℝ (gradient q x) (ψ x)
      = ∫ x, inner ℝ (Φ x - gradient q x) (ψ x) := by
    rw [← integral_sub hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun x => (inner_sub_left _ _ _).symm)
  rw [Work.FTS.PressureOn.Dpair_apply, hibp]
  linarith [key]

end Work.FTS.PressureOn.MollAux
