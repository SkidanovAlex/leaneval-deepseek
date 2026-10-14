import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.SolutionDelivery.Scaling.Defs
import Submission.Work.Stability.OmegaCutSupport
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.SolutionDelivery.Holder.isContDiffHolderOn_coreRegion_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Holder

open Set
open scoped Topology

/-!
# Core-restricting a joint `C^{1,α}` bound: `univ × Icc` gives `coreRegion ρ × Icc`

The challenge hypothesis is the joint `C^{1,α}` regularity of `u.uncurry` on the *whole* spatial
space over the time interval `[0,S]`.  The core regularity statements of the construction, on the
other hand, are asked on the core strip `coreRegion ρ ×ˢ Icc 0 S`, i.e. on the closed spatial ball
of radius `ρ`.  This file records the (purely set-theoretic, given the uniqueness of the
within-derivative) passage from the first to the second.

The one point that is not automatic is that the derivative is taken *within* the set
(`fderivWithin`): for `t` on the spatial boundary of the core strip, or for `t = 0` or `t = S`,
the two `fderivWithin`s are related by `fderivWithin_subset`, which needs
`UniqueDiffWithinAt` of the *smaller* set.  That uniqueness holds because `coreRegion ρ` is a
closed ball with `ρ > 0` (convex, with nonempty interior, so `uniqueDiffWithinAt_convex` applies
at every point of its closure) and `Icc 0 S` has `0 < S`.
-/



end Work.SolutionDelivery.Holder
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.bkm_rescale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity

namespace Work.SolutionDelivery.Scaling

/-! ## The pointwise scaling of the vorticity -/


/-! ## Reindexing an `⨆` along `x ↦ λx` -/



/-! ## The `L∞`-in-space norm of the vorticity -/


/-! ## The interval-integral substitution -/


/-! ## The BKM integral under the scaling -/


end Work.SolutionDelivery.Scaling
end
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.contDiffOn_rescale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

open Set



end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.contDiffOn_rescalePressure =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling





end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.div_rescale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling


end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.euler_eq_rescale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Euler equation is invariant under the `(λ, λ²)`-scaling

The scaling that carries a blow-up at time `T > 0` to a blow-up at time `1` is

  `u'(x,t) = λ u(λx, λ²t)`,  `p'(x,t) = λ² p(λx, λ²t)`,  `λ = √T`.

Its effect on the incompressible Euler equation

  `∂ₜu + (u·∇)u + ∇p = 0`

is that all three terms are multiplied by the *same* factor `λ³`, so the equation is preserved.
This file proves that pointwise: if `(u,p)` solves the Euler equation on the strip `ℝ³ × (0,T)`
and `λ ≠ 0` with `λ² = T`, then the rescaled pair `(rescale λ u, rescalePressure λ p)` solves it on
`ℝ³ × (0,1)`.

The three scaling identities are proved through three plumbing lemmas about the joint derivative
`u.uncurry : ℝ³ × ℝ → ℝ³` (the two slices of a jointly differentiable map are differentiable)
and two abstract chain rules for the map `z ↦ c • f (a • z)` (one for `fderiv`, one for the
gradient of a scalar function), together with the time chain rule `deriv_smul_comp_time`.
-/

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery.Scaling

/-! ## Slices of a jointly differentiable map -/



/-! ## Chain rules for `z ↦ c • f (a • z)` -/




/-! ## The scaling of the Euler equation -/


end Work.SolutionDelivery.Scaling
end
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.isContDiffHolderOn_rescale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Euler rescaling preserves the strip `C^{1,α}` class

`rescale λ u = fun x t => λ • u (λ • x) (λ² t)`.  If `u.uncurry` is jointly `C^{1,α}` on every
strip `ℝ³ × [0,S']` with `S' < T`, then — for `λ² = T`, `λ ≠ 0` — the rescaled field is jointly
`C^{1,α}` on `ℝ³ × [0,S]` for every `S < 1`.

The rescaling is a *linear* change of the spacetime variables followed by a linear map on the
values: with

* `scaleCLM λ : ℝ³ × ℝ →L[ℝ] ℝ³ × ℝ`, `(x,t) ↦ (λx, λ²t)` and
* `smulCLM λ : ℝ³ →L[ℝ] ℝ³`, `y ↦ λ • y`,

one has `(rescale λ u).uncurry = smulCLM λ ∘ u.uncurry ∘ scaleCLM λ` (`rfl`), and `scaleCLM λ`
carries `ℝ³ × [0,S]` onto `ℝ³ × [0,λ²S]`.

The `C^{1,α}` class is stable under such a reparametrisation.  The only point needing care is the
`fderivWithin` in the definition of `IsContDiffHolderOn`: the strip `ℝ³ × [0,S]` has a boundary
(at `t = 0`), so `fderivWithin` is *not* the ambient `fderiv`; but the strip is uniquely
differentiable within at each of its points (`uniqueDiffOn_Icc` + `UniqueDiffWithinAt.prod`), so
the within-derivative is pinned down by the within chain rule
(`HasFDerivWithinAt.comp` + `HasFDerivWithinAt.fderivWithin`), and there the linearity of the
rescaling makes the derivative formula explicit:

  `D(fderivWithin (smulCLM λ ∘ g ∘ scaleCLM λ)) z = smulCLM λ ∘ D(fderivWithin g) (scaleCLM λ z) ∘ scaleCLM λ`.

The Hölder block then follows from `dist (scaleCLM λ z) (scaleCLM λ w) ≤ ‖scaleCLM λ‖ * dist z w`
and the boundedness block from the boundedness of `fderivWithin g` on the image strip.
-/

namespace Work.SolutionDelivery.Scaling

open Set Filter
open scoped Topology

noncomputable section

private abbrev R3 := Work.SolutionDelivery.R3

/-! ## The two linear maps of the rescaling -/

/-- The scaling `(x,t) ↦ (λx, λ²t)` of the spacetime variables, as a continuous linear map. -/
def scaleCLM (lam : ℝ) : (R3 × ℝ) →L[ℝ] (R3 × ℝ) :=
  (lam • ContinuousLinearMap.fst ℝ R3 ℝ).prod
    ((lam ^ 2) • ContinuousLinearMap.snd ℝ R3 ℝ)

@[simp] theorem scaleCLM_apply (lam : ℝ) (z : R3 × ℝ) :
    scaleCLM lam z = (lam • z.1, lam ^ 2 * z.2) := rfl

/-- The scalar multiplication `y ↦ λ • y` on the values, as a continuous linear map. -/
def smulCLM (lam : ℝ) : R3 →L[ℝ] R3 :=
  lam • ContinuousLinearMap.id ℝ R3

@[simp] theorem smulCLM_apply (lam : ℝ) (y : R3) : smulCLM lam y = lam • y := rfl

/-! ## The general reparametrisation lemma

For an arbitrary continuous linear `A` on the values and `Φ` on the variables mapping `s` into
`t`, the function `z ↦ A (g (Φ z))` inherits the `C^{1,α}` class of `g` on `t`.
-/

/-- **`C¹` block**: the composite of `g` with two continuous linear maps is `C¹` on `s`. -/
theorem contDiffOn_comp_clm {s t : Set (R3 × ℝ)} {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3) (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (hg : ContDiffOn ℝ 1 g t) :
    ContDiffOn ℝ 1 (fun z => A (g (Φ z))) s := by
  have h1 : ContDiffOn ℝ 1 (g ∘ Φ) s := hg.comp Φ.contDiff.contDiffOn hΦ
  have h2 : ContDiffOn ℝ 1 (⇑A) Set.univ := A.contDiff.contDiffOn
  have h3 := h2.comp h1 (fun _ _ => trivial)
  convert h3 using 1
  ext z
  rfl

/-- **The derivative formula**: on the strip `s` (which is uniquely differentiable within,
`huniq`), the within-derivative of `z ↦ A (g (Φ z))` is the composite of the within-derivative of
`g` at `Φ z` with the two fixed linear maps `A` and `Φ`. -/
theorem fderivWithin_comp_clm {s t : Set (R3 × ℝ)} {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3) (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t) :
    ∀ z ∈ s, fderivWithin ℝ (fun z => A (g (Φ z))) s z
      = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ) := by
  intro z hz
  have hz_t : Φ z ∈ t := hΦ hz
  have hg' : HasFDerivWithinAt g (fderivWithin ℝ g t (Φ z)) t (Φ z) :=
    (hg (Φ z) hz_t).hasFDerivWithinAt
  have hΦ' : HasFDerivWithinAt Φ Φ s z := Φ.hasFDerivAt.hasFDerivWithinAt
  have hcomp1 : HasFDerivWithinAt (g ∘ Φ) (fderivWithin ℝ g t (Φ z) ∘L Φ) s z :=
    HasFDerivWithinAt.comp z hg' hΦ' hΦ
  have hA : HasFDerivWithinAt (⇑A) A Set.univ ((g ∘ Φ) z) :=
    A.hasFDerivAt.hasFDerivWithinAt
  have hcomp2 : HasFDerivWithinAt (⇑A ∘ (g ∘ Φ))
      (A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)) s z :=
    HasFDerivWithinAt.comp z hA hcomp1 (fun _ _ => trivial)
  have := hcomp2.fderivWithin (huniq z hz)
  change fderivWithin ℝ (⇑A ∘ (g ∘ Φ)) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)
  exact this

/-- **Boundedness block**: the within-derivative of the composite is bounded on `s` whenever the
within-derivative of `g` is bounded on `t`. -/
theorem isBoundedFunOn_fderivWithin_comp {s t : Set (R3 × ℝ)} {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3) (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t)
    (hbdd : IsBoundedFunOn (fderivWithin ℝ g t) t) :
    IsBoundedFunOn (fderivWithin ℝ (fun z => A (g (Φ z))) s) s := by
  set S := (fderivWithin ℝ g t) '' t with hS
  have hSb : Bornology.IsBounded S := by rw [hS]; exact hbdd
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (s := S)
    (0 : (R3 × ℝ) →L[ℝ] R3)).1 hSb
  set R' := max R 0 with hR'def
  have hR' : ∀ y ∈ t, ‖fderivWithin ℝ g t y‖ ≤ R' := by
    intro y hy
    have hmem : fderivWithin ℝ g t y ∈ S := by rw [hS]; exact ⟨y, hy, rfl⟩
    have h := hR hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact le_trans h (le_max_left _ _)
  show Bornology.IsBounded ((fderivWithin ℝ (fun z => A (g (Φ z))) s) '' s)
  refine Metric.isBounded_iff.mpr ⟨2 * (‖A‖ * R' * ‖Φ‖), ?_⟩
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  rw [fderivWithin_comp_clm A Φ hΦ huniq hg z hz, fderivWithin_comp_clm A Φ hΦ huniq hg w hw]
  rw [dist_eq_norm]
  set Dz := fderivWithin ℝ g t (Φ z) with hDz
  set Dw := fderivWithin ℝ g t (Φ w) with hDw
  have hsub : A ∘L (Dz - Dw) ∘L Φ = (A ∘L Dz ∘L Φ) - (A ∘L Dw ∘L Φ) := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [← hsub]
  have hXY : ‖Dz - Dw‖ ≤ 2 * R' := by
    have h1 := hR' (Φ z) (hΦ hz)
    have h2 := hR' (Φ w) (hΦ hw)
    rw [← hDz] at h1
    rw [← hDw] at h2
    calc ‖Dz - Dw‖ ≤ ‖Dz‖ + ‖Dw‖ := norm_sub_le _ _
      _ ≤ 2 * R' := by linarith
  calc ‖A ∘L (Dz - Dw) ∘L Φ‖
      ≤ ‖A ∘L (Dz - Dw)‖ * ‖Φ‖ := ContinuousLinearMap.opNorm_comp_le (A ∘L (Dz - Dw)) Φ
    _ ≤ (‖A‖ * ‖Dz - Dw‖) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le A (Dz - Dw)) (norm_nonneg _)
    _ ≤ (‖A‖ * (2 * R')) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY (norm_nonneg _)) (norm_nonneg _)
    _ = 2 * (‖A‖ * R' * ‖Φ‖) := by ring

/-- **Hölder block**: if the within-derivative of `g` is `α`-Hölder on `t`, then so is the
within-derivative of the composite on `s` (with constant `‖A‖‖Φ‖C‖Φ‖^α`). -/
theorem holderOn_fderivWithin_comp {α : NNReal} {s t : Set (R3 × ℝ)} {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3) (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t)
    (hholder : HolderOn α (fderivWithin ℝ g t) t) :
    HolderOn α (fderivWithin ℝ (fun z => A (g (Φ z))) s) s := by
  obtain ⟨C, hC⟩ := hholder
  refine ⟨Real.toNNReal (‖A‖ * ‖Φ‖ * (C : ℝ) * ‖Φ‖ ^ (α : ℝ)), ?_⟩
  apply Work.StabilityFar.Holder.holderOnWith_of_norm_le
  intro x hx y hy
  rw [Real.coe_toNNReal _ (by positivity)]
  rw [fderivWithin_comp_clm A Φ hΦ huniq hg x hx, fderivWithin_comp_clm A Φ hΦ huniq hg y hy]
  set X := fderivWithin ℝ g t (Φ x) with hX
  set Y := fderivWithin ℝ g t (Φ y) with hY
  have hbound : ‖X - Y‖ ≤ (C : ℝ) * dist (Φ x) (Φ y) ^ (α : ℝ) := by
    have h := norm_le_of_holderOnWith hC (Φ x) (hΦ hx) (Φ y) (hΦ hy)
    rwa [← hX, ← hY] at h
  have hdist : dist (Φ x) (Φ y) ≤ ‖Φ‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖Φ x - Φ y‖ = ‖Φ (x - y)‖ := by rw [map_sub]
      _ ≤ ‖Φ‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm Φ (x - y)
  have hdistα : dist (Φ x) (Φ y) ^ (α : ℝ) ≤ ‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
    calc dist (Φ x) (Φ y) ^ (α : ℝ)
        ≤ (‖Φ‖ * dist x y) ^ (α : ℝ) := Real.rpow_le_rpow dist_nonneg hdist (by positivity)
      _ = ‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := Real.mul_rpow (norm_nonneg _) dist_nonneg
  have hsub : A ∘L X ∘L Φ - A ∘L Y ∘L Φ = A ∘L (X - Y) ∘L Φ := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [hsub]
  calc ‖A ∘L (X - Y) ∘L Φ‖
      ≤ ‖A ∘L (X - Y)‖ * ‖Φ‖ := ContinuousLinearMap.opNorm_comp_le (A ∘L (X - Y)) Φ
    _ ≤ (‖A‖ * ‖X - Y‖) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le A (X - Y)) (norm_nonneg _)
    _ ≤ (‖A‖ * ((C : ℝ) * dist (Φ x) (Φ y) ^ (α : ℝ))) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (‖A‖ * ((C : ℝ) * (‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ)))) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdistα C.coe_nonneg) (norm_nonneg _))
          (norm_nonneg _)
    _ = (‖A‖ * ‖Φ‖ * (C : ℝ) * ‖Φ‖ ^ (α : ℝ)) * dist x y ^ (α : ℝ) := by ring

/-- **The reparametrisation lemma**: `IsContDiffHolderOn` is stable under post-composition with a
continuous linear map `A` and pre-composition with a continuous linear map `Φ` carrying `s`
into `t`. -/
theorem isContDiffHolderOn_comp_clm {α : NNReal} {s t : Set (R3 × ℝ)} {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3) (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (h : IsContDiffHolderOn ℝ α g t) :
    IsContDiffHolderOn ℝ α (fun z => A (g (Φ z))) s :=
  ⟨contDiffOn_comp_clm A Φ hΦ h.1,
   isBoundedFunOn_fderivWithin_comp A Φ hΦ huniq (h.1.differentiableOn (by norm_num)) h.2.1,
   holderOn_fderivWithin_comp A Φ hΦ huniq (h.1.differentiableOn (by norm_num)) h.2.2⟩

/-! ## The rescaled field -/


end

end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.isContDiffHolder_rescaleDatum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

/-!
# `C^{1,α}` is preserved by the datum scaling `x ↦ λ • F (λ • x)`

The rescaling `rescaleDatum lam F = fun x ↦ lam • F (lam • x)` of a `C^{1,α}` vector field is
again `C^{1,α}`: it is smooth (composition of the smooth `F` with the dilation), its derivative

  `fderiv ℝ (rescaleDatum lam F) x = lam ^ 2 • fderiv ℝ F (lam • x)`

is bounded by `‖lam‖^2 * C` when `‖fderiv ℝ F‖ ≤ C`, and is `α`-Hölder with constant
`‖lam^2‖ * C * ‖lam‖^α` because the dilation `x ↦ lam • x` is `‖lam‖`-Lipschitz, and a Hölder
function composed with a Lipschitz map — and then multiplied by a constant — stays Hölder.

(The conclusion holds for *every* real `lam`, including `0`: then `rescaleDatum 0 F = 0`.)
-/

/-- **The `dist`/`HolderWith` bridge.**  A pointwise bound of the form
`dist (f x) (f y) ≤ C * dist x y ^ r` (real exponent) upgrades to `HolderWith C r f`, which is
stated in terms of `edist` and the `ENNReal` power. -/
theorem holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : NNReal} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
      ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)



end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.isOdd_rescaleDatum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Oddness is preserved by the Euler rescaling of a datum

`rescaleDatum lam F = fun x => lam • F (lam • x)`.  The oddness class
`FiniteTimeSingularity.IsOdd` is the coordinatewise parity condition of the challenge: the `i`-th
component of `u` is odd in the `i`-th coordinate and even in the other two.  Multiplication by a
constant preserves oddness/evenness of a real function, and the linear change of variable
`x ↦ lam • x` sends the `i`-th coordinate to `lam * xᵢ` while keeping the other two coordinates
proportional to constants, so each component of `rescaleDatum lam F` has exactly the same parity
profile as the corresponding component of `F`.
-/

namespace Work.SolutionDelivery.Scaling

open FiniteTimeSingularity






end Work.SolutionDelivery.Scaling
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.vorticity_rescale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Scaling


end Work.SolutionDelivery.Scaling
end
