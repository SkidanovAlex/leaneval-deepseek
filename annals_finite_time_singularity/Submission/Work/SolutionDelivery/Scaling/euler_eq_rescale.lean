import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.SolutionDelivery.Scaling.Defs
import Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply

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

/-- If `(x,t) ↦ u x t` is differentiable at `(y,s)`, then the time slice `t ↦ u y t` has
derivative `∂ₜu(y,s)` at `s`. -/
lemma hasDerivAt_slice_time {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {L : (Work.SolutionDelivery.R3 × ℝ) →L[ℝ] Work.SolutionDelivery.R3}
    {y : Work.SolutionDelivery.R3} {s : ℝ}
    (hf : HasFDerivAt u.uncurry L (y, s)) :
    HasDerivAt (fun s' => u y s') (FiniteTimeSingularity.timeDeriv u y s) s := by
  have hsl := hf.comp s (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := Work.SolutionDelivery.R3)
    (F := ℝ) y s)
  have hd : HasDerivAt (fun s' => u y s')
      ((L.comp (ContinuousLinearMap.inr ℝ Work.SolutionDelivery.R3 ℝ)) 1) s := hsl.hasDerivAt
  have hval : (L.comp (ContinuousLinearMap.inr ℝ Work.SolutionDelivery.R3 ℝ)) 1
      = FiniteTimeSingularity.timeDeriv u y s := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply hf (0 : Work.SolutionDelivery.R3) (1 : ℝ)]
    simp
  rw [hval] at hd
  exact hd

/-- If `(x,t) ↦ f x t` is differentiable at `(y,s)`, then the space slice `x ↦ f x s` is
differentiable at `y`. -/
lemma hasFDerivAt_slice_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Work.SolutionDelivery.R3 → ℝ → E} {L : (Work.SolutionDelivery.R3 × ℝ) →L[ℝ] E}
    {y : Work.SolutionDelivery.R3} {s : ℝ}
    (hf : HasFDerivAt f.uncurry L (y, s)) :
    HasFDerivAt (fun z => f z s) (L.comp (ContinuousLinearMap.inl ℝ Work.SolutionDelivery.R3 ℝ)) y := by
  refine HasFDerivAt.comp (g := f.uncurry) (f := fun e : Work.SolutionDelivery.R3 => (e, s)) y hf ?_
  exact hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := Work.SolutionDelivery.R3) (F := ℝ) y s

/-! ## Chain rules for `z ↦ c • f (a • z)` -/

/-- The derivative of `z ↦ c • f (a • z)` at `x`, for a map into a normed space. -/
lemma hasFDerivAt_smul_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Work.SolutionDelivery.R3 → E} {L : Work.SolutionDelivery.R3 →L[ℝ] E}
    {x : Work.SolutionDelivery.R3} {a c : ℝ}
    (hf : HasFDerivAt f L (a • x)) :
    HasFDerivAt (fun z => c • f (a • z)) ((c * a) • L) x := by
  have hσ : HasFDerivAt (fun z : Work.SolutionDelivery.R3 => a • z)
      (a • ContinuousLinearMap.id ℝ Work.SolutionDelivery.R3) x :=
    ContinuousLinearMap.hasFDerivAt (a • ContinuousLinearMap.id ℝ Work.SolutionDelivery.R3) (x := x)
  have h1 : HasFDerivAt (fun z : Work.SolutionDelivery.R3 => f (a • z))
      (L.comp (a • ContinuousLinearMap.id ℝ Work.SolutionDelivery.R3)) x :=
    HasFDerivAt.comp x hf hσ
  have h2 : L.comp (a • ContinuousLinearMap.id ℝ Work.SolutionDelivery.R3) = a • L := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  rw [h2] at h1
  have h3 : HasFDerivAt (c • fun z : Work.SolutionDelivery.R3 => f (a • z)) (c • (a • L)) x :=
    h1.const_smul c
  rw [smul_smul] at h3
  exact h3

/-- The gradient of `z ↦ c * f (a • z)` at `x`, for a scalar map `f`. -/
lemma gradient_smul_comp_smul {f : Work.SolutionDelivery.R3 → ℝ}
    {L : Work.SolutionDelivery.R3 →L[ℝ] ℝ} {x : Work.SolutionDelivery.R3} {a c : ℝ}
    (hf : HasFDerivAt f L (a • x)) :
    ∇ (fun z => c * f (a • z)) x = (c * a) • ∇ f (a • x) := by
  have hcomp : HasFDerivAt (fun z : Work.SolutionDelivery.R3 => c * f (a • z)) ((c * a) • L) x := by
    have h := hasFDerivAt_smul_comp_smul (E := ℝ) (f := f) (L := L) (x := x) (a := a) (c := c) hf
    simpa [smul_eq_mul] using h
  apply HasGradientAt.unique (x := x) (f := fun z => c * f (a • z))
  · exact hcomp.differentiableAt.hasGradientAt
  · rw [hasGradientAt_iff_hasFDerivAt]
    have hdual : (InnerProductSpace.toDual ℝ Work.SolutionDelivery.R3) ((c * a) • ∇ f (a • x))
        = (c * a) • L := by
      rw [map_smul, toDual_gradient, hf.fderiv]
    rw [hdual]
    exact hcomp

/-- The time chain rule: the derivative of `τ ↦ c • F (a * τ)` at `t`. -/
lemma deriv_smul_comp_time {F : ℝ → Work.SolutionDelivery.R3} {v : Work.SolutionDelivery.R3}
    {a c t : ℝ} (h : HasDerivAt F v (a * t)) :
    deriv (fun τ => c • F (a * τ)) t = (c * a) • v := by
  have hlin : HasDerivAt (fun τ : ℝ => a * τ) a t := hasDerivAt_const_mul a
  have h1 : HasDerivAt (F ∘ (fun τ : ℝ => a * τ)) (a • v) t := h.scomp t hlin
  have h2 : HasDerivAt (fun τ => c • F (a * τ)) (c • (a • v)) t := h1.const_smul c
  have h3 : c • (a • v) = (c * a) • v := smul_smul c a v
  rw [h3] at h2
  exact h2.deriv

/-! ## The scaling of the Euler equation -/

theorem euler_eq_rescale {lam T : ℝ} {p : Work.SolutionDelivery.R3 → ℝ → ℝ}
    {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    (hlam : lam ≠ 0) (hsq : lam ^ 2 = T)
    (hcu : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo 0 T))
    (hcp : ContDiffOn ℝ 1 p.uncurry (Set.univ ×ˢ Set.Ioo 0 T))
    (heq : ∀ x : Work.SolutionDelivery.R3, ∀ t ∈ Set.Ioo 0 T,
      FiniteTimeSingularity.timeDeriv u x t + FiniteTimeSingularity.directionalDeriv u u x t
        + FiniteTimeSingularity.spaceGrad p x t = 0) :
    ∀ x : Work.SolutionDelivery.R3, ∀ t ∈ Set.Ioo 0 1,
      FiniteTimeSingularity.timeDeriv (Work.SolutionDelivery.rescale lam u) x t
        + FiniteTimeSingularity.directionalDeriv (Work.SolutionDelivery.rescale lam u)
            (Work.SolutionDelivery.rescale lam u) x t
        + FiniteTimeSingularity.spaceGrad (Work.SolutionDelivery.rescalePressure lam p) x t = 0 := by
  intro x t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hlam2 : 0 < lam ^ 2 := sq_pos_of_ne_zero hlam
  have hTpos : 0 < T := by rw [← hsq]; exact hlam2
  have hs_mem : lam ^ 2 * t ∈ Set.Ioo 0 T := by
    refine ⟨mul_pos hlam2 ht0, ?_⟩
    calc lam ^ 2 * t < lam ^ 2 := by nlinarith [ht1, hlam2]
      _ = T := hsq
  have hu : HasFDerivAt u.uncurry (fderiv ℝ u.uncurry (lam • x, lam ^ 2 * t))
      (lam • x, lam ^ 2 * t) :=
    ((hcu.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hs_mem⟩)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hp : HasFDerivAt p.uncurry (fderiv ℝ p.uncurry (lam • x, lam ^ 2 * t))
      (lam • x, lam ^ 2 * t) :=
    ((hcp.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hs_mem⟩)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hus : HasFDerivAt (fun z : Work.SolutionDelivery.R3 => u z (lam ^ 2 * t))
      ((fderiv ℝ u.uncurry (lam • x, lam ^ 2 * t)).comp
        (ContinuousLinearMap.inl ℝ Work.SolutionDelivery.R3 ℝ)) (lam • x) :=
    hasFDerivAt_slice_space hu
  have hps : HasFDerivAt (fun z : Work.SolutionDelivery.R3 => p z (lam ^ 2 * t))
      ((fderiv ℝ p.uncurry (lam • x, lam ^ 2 * t)).comp
        (ContinuousLinearMap.inl ℝ Work.SolutionDelivery.R3 ℝ)) (lam • x) :=
    hasFDerivAt_slice_space hp
  have hut : HasDerivAt (fun s' => u (lam • x) s')
      (FiniteTimeSingularity.timeDeriv u (lam • x) (lam ^ 2 * t)) (lam ^ 2 * t) :=
    hasDerivAt_slice_time hu
  -- the time derivative scales by `λ³`
  have h1 : FiniteTimeSingularity.timeDeriv (Work.SolutionDelivery.rescale lam u) x t
      = lam ^ 3 • FiniteTimeSingularity.timeDeriv u (lam • x) (lam ^ 2 * t) := by
    show deriv (fun τ => lam • u (lam • x) (lam ^ 2 * τ)) t
        = lam ^ 3 • FiniteTimeSingularity.timeDeriv u (lam • x) (lam ^ 2 * t)
    rw [deriv_smul_comp_time (F := u (lam • x))
      (v := FiniteTimeSingularity.timeDeriv u (lam • x) (lam ^ 2 * t))
      (a := lam ^ 2) (c := lam) (t := t) hut]
    rw [show lam * lam ^ 2 = lam ^ 3 by ring]
  -- the convection term scales by `λ³`
  have h2 : FiniteTimeSingularity.directionalDeriv (Work.SolutionDelivery.rescale lam u)
      (Work.SolutionDelivery.rescale lam u) x t
      = lam ^ 3 • FiniteTimeSingularity.directionalDeriv u u (lam • x) (lam ^ 2 * t) := by
    show fderiv ℝ (fun z : Work.SolutionDelivery.R3 => lam • u (lam • z) (lam ^ 2 * t)) x
          (lam • u (lam • x) (lam ^ 2 * t))
        = lam ^ 3 • fderiv ℝ (fun z : Work.SolutionDelivery.R3 => u z (lam ^ 2 * t)) (lam • x)
            (u (lam • x) (lam ^ 2 * t))
    have hder : fderiv ℝ (fun z : Work.SolutionDelivery.R3 => lam • u (lam • z) (lam ^ 2 * t)) x
        = (lam * lam) • ((fderiv ℝ u.uncurry (lam • x, lam ^ 2 * t)).comp
            (ContinuousLinearMap.inl ℝ Work.SolutionDelivery.R3 ℝ)) :=
      (hasFDerivAt_smul_comp_smul (f := fun z : Work.SolutionDelivery.R3 => u z (lam ^ 2 * t))
        (L := (fderiv ℝ u.uncurry (lam • x, lam ^ 2 * t)).comp
          (ContinuousLinearMap.inl ℝ Work.SolutionDelivery.R3 ℝ))
        (x := x) (a := lam) (c := lam) hus).fderiv
    rw [hder, hus.fderiv]
    rw [_root_.smul_apply, map_smul, smul_smul]
    rw [show (lam * lam) * lam = lam ^ 3 by ring]
  -- the pressure gradient scales by `λ³`
  have h3 : FiniteTimeSingularity.spaceGrad (Work.SolutionDelivery.rescalePressure lam p) x t
      = lam ^ 3 • FiniteTimeSingularity.spaceGrad p (lam • x) (lam ^ 2 * t) := by
    show ∇ (fun z : Work.SolutionDelivery.R3 => lam ^ 2 * p (lam • z) (lam ^ 2 * t)) x
        = lam ^ 3 • ∇ (fun z : Work.SolutionDelivery.R3 => p z (lam ^ 2 * t)) (lam • x)
    have hg : ∇ (fun z : Work.SolutionDelivery.R3 => lam ^ 2 * p (lam • z) (lam ^ 2 * t)) x
        = (lam ^ 2 * lam) • ∇ (fun z : Work.SolutionDelivery.R3 => p z (lam ^ 2 * t)) (lam • x) :=
      gradient_smul_comp_smul (f := fun z : Work.SolutionDelivery.R3 => p z (lam ^ 2 * t))
        (L := (fderiv ℝ p.uncurry (lam • x, lam ^ 2 * t)).comp
          (ContinuousLinearMap.inl ℝ Work.SolutionDelivery.R3 ℝ))
        (x := x) (a := lam) (c := lam ^ 2) hps
    rw [hg]
    rw [show lam ^ 2 * lam = lam ^ 3 by ring]
  -- assemble: the common factor `λ³` multiplies the original equation, which vanishes
  have hkey := heq (lam • x) (lam ^ 2 * t) hs_mem
  rw [h1, h2, h3, ← smul_add, ← smul_add, hkey, smul_zero]

end Work.SolutionDelivery.Scaling
