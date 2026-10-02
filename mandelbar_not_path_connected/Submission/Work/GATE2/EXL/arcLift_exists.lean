/-
# GATE2 / EXL — the equipotential arc lifts into the far-left half plane

The arc `θ ↦ rayPt d.hN θ (exp p)`, `θ ∈ [θ₀, α₁]`, is by `harc` pointwise a `Ψ`-image of a point
of the half plane `U = {Re < -R}`, and `Ψ` is injective on `U` (`RayCylLift.hinj`).  Hence the
lift is *unique*: it is the canonical inverse `Function.invFunOn Ψ U`, which is continuous on
`Ψ '' U` because `Ψ` is holomorphic and injective on the open set `U`
(`Work.GATE2.PL.continuousOn_invFunOn_of_injOn`).  Composing with the continuous arc (continuity in
the angle, `Work.ELTop.continuous_rayPt_angle`) gives the path `A`, and the endpoint values are
forced by the two hypotheses `hx₀` (at `θ₀`) and `hτ` together with `Lray.hΨ₁` (at `α₁`).
-/
import Mathlib
import Submission.Work.GATE2.EXL.ArcPreimage
import Submission.Work.GATE2.PL.continuousOn_invFunOn_of_injOn
import Submission.Work.GATE2.Inputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

theorem arcLift_exists {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (Lray : Work.ELRig.RayCylLift d fl)
    {θ₀ x₀ p s₁ : ℝ} (hθ₀ : θ₀ ≤ Work.EL.alpha1)
    (hx₀R : x₀ < -Lray.R) (hγ₁R : (Lray.γ₁ s₁).re < -Lray.R)
    (hτ : Lray.τ s₁ = Real.exp p)
    (hx₀ : fl.Ψ ((x₀ : ℝ) : ℂ) = Work.EL.rayPt d.hN θ₀ (Real.exp p))
    (harc : ∀ θ ∈ Set.Icc θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ fl.Ψ '' {w : ℂ | w.re < -Lray.R}) :
    ∃ A : C(unitInterval, ℂ),
      A 0 = ((x₀ : ℝ) : ℂ) ∧ A 1 = Lray.γ₁ s₁ ∧
      (∀ r : unitInterval, (A r).re < -Lray.R) ∧
      (∀ r : unitInterval,
        fl.Ψ (A r) = Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p)) := by
  classical
  -- The half plane in which `Ψ` is injective and whose points lift uniquely.
  set U : Set ℂ := {w : ℂ | w.re < -Lray.R} with hUdef
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  -- The level `exp p` is `> 1` (it is `τ s₁`).
  have hexp : 1 < Real.exp p := by rw [← hτ]; exact Lray.hτ1 s₁
  -- The arc, as a function of `r ∈ [0,1]`.
  set f : unitInterval → ℂ :=
    fun r => Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p) with hfdef
  have hfcont : Continuous f := by
    rw [hfdef]
    exact (Work.ELTop.continuous_rayPt_angle d.hN hexp).comp (by fun_prop)
  -- Every point of the arc is a `Ψ`-image of `U`.
  have hfin : ∀ r : unitInterval, f r ∈ fl.Ψ '' U := by
    intro r
    have hθmem : θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀) ∈ Set.Icc θ₀ Work.EL.alpha1 := by
      refine ⟨?_, ?_⟩
      · have hr : (0 : ℝ) ≤ (r : ℝ) := r.2.1
        nlinarith [mul_nonneg hr (show (0 : ℝ) ≤ Work.EL.alpha1 - θ₀ by linarith)]
      · have hr : (r : ℝ) ≤ 1 := r.2.2
        nlinarith [mul_le_of_le_one_left (show (0 : ℝ) ≤ Work.EL.alpha1 - θ₀ by linarith) hr]
    have := harc _ hθmem
    simpa [hfdef, hUdef] using this
  -- Continuity of the canonical inverse on the image.
  have hinvc : ContinuousOn (Function.invFunOn fl.Ψ U) (fl.Ψ '' U) :=
    Work.GATE2.PL.continuousOn_invFunOn_of_injOn hUopen fl.Ψ_diff.differentiableOn Lray.hinj
  have hAcont : Continuous (fun r : unitInterval => Function.invFunOn fl.Ψ U (f r)) :=
    ContinuousOn.comp_continuous hinvc hfcont hfin
  have hAeq : ∀ r : unitInterval, fl.Ψ (Function.invFunOn fl.Ψ U (f r)) = f r :=
    fun r => Function.invFunOn_eq (hfin r)
  have hAmem : ∀ r : unitInterval, Function.invFunOn fl.Ψ U (f r) ∈ U :=
    fun r => Function.invFunOn_mem (hfin r)
  -- Endpoint `r = 0`: the preimage is `x₀` by injectivity.
  have hA0 : Function.invFunOn fl.Ψ U (f 0) = ((x₀ : ℝ) : ℂ) := by
    have hf0 : f 0 = fl.Ψ ((x₀ : ℝ) : ℂ) := by
      show Work.EL.rayPt d.hN (θ₀ + ((0 : unitInterval) : ℝ) * (Work.EL.alpha1 - θ₀))
        (Real.exp p) = fl.Ψ ((x₀ : ℝ) : ℂ)
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]
      exact hx₀.symm
    have haeq : fl.Ψ (Function.invFunOn fl.Ψ U (f 0)) = fl.Ψ ((x₀ : ℝ) : ℂ) := by
      rw [Function.invFunOn_eq (hfin 0), hf0]
    exact Lray.hinj (hAmem 0) (by simpa using hx₀R) haeq
  -- Endpoint `r = 1`: the preimage is `γ₁ s₁` by injectivity, using `hτ`.
  have hA1 : Function.invFunOn fl.Ψ U (f 1) = Lray.γ₁ s₁ := by
    have hf1 : f 1 = fl.Ψ (Lray.γ₁ s₁) := by
      show Work.EL.rayPt d.hN (θ₀ + ((1 : unitInterval) : ℝ) * (Work.EL.alpha1 - θ₀))
        (Real.exp p) = fl.Ψ (Lray.γ₁ s₁)
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul]
      have hα : θ₀ + (Work.EL.alpha1 - θ₀) = Work.EL.alpha1 := by ring
      rw [hα, Lray.hΨ₁ s₁, hτ]
    have haeq : fl.Ψ (Function.invFunOn fl.Ψ U (f 1)) = fl.Ψ (Lray.γ₁ s₁) := by
      rw [Function.invFunOn_eq (hfin 1), hf1]
    exact Lray.hinj (hAmem 1) (by simpa using hγ₁R) haeq
  refine ⟨⟨fun r : unitInterval => Function.invFunOn fl.Ψ U (f r), hAcont⟩,
    hA0, hA1, ?_, ?_⟩
  · intro r
    have h := hAmem r
    rw [hUdef] at h
    simpa using h
  · intro r
    simpa [hfdef] using hAeq r

end Work.GATE2.EXL
