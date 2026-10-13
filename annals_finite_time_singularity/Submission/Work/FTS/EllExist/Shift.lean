/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.EllExist.Shift` — the calculus of the singular shift `Ψ ↦ Ψ + Gsing α g · sin 2θ`

This module develops the elementary (and fully proved) part of the existence node
`FTS/EllExist` (design §1 (b)): the *shifting map*

  `shiftSing α g Ψ = fun z θ => Ψ z θ + Gsing α g z * Real.sin (2 * θ)`

and its interaction with the elliptic operator `bslOp α`, the angular moment `F_*`, the
Dirichlet data, joint smoothness and the decay at `z → ∞`.

Everything here is unconditional except for the *explicit* analytic inputs (the second-order ODE
satisfied by `Gsing α g`, the smoothness of `Gsing α g` on `(0,∞)`, its decay at infinity).

## Contents

* `shiftSing_sub_self` — `shiftSing α g` is invertible by subtracting the same multiple of
  `sin 2θ`;
* `bslOp_shiftSing` — the paper's identity `L(G sin 2θ) = (α²z²G'' + α(5+α)zG') sin 2θ`:
  the shift changes `bslOp α Ψ` only by a *radial* multiple of `sin 2θ`;
* `bslOp_shiftSing_of_ode` — with the singular-term ODE
  `α²z²G'' + α(5+α)zG' = (15/4) F_*(g)`, the shift turns the source `g` into
  `orthSource g = g - (15/4) sin 2θ · F_*(g)`;
* `shiftSing_zero`, `shiftSing_pi_half` — the shift preserves the two Dirichlet values;
* `Fstar_shiftSing` — `F_*(Ψ + Gsin 2θ) z = F_*(Ψ) z + (4/15) G(z)` (because
  `∫_θ sin 2θ · sinθcos²θ dθ = 4/15`);
* `contDiffOn_uncurry_shiftSing` — joint smoothness of the shift on the open quadrant;
* `tendsto_shiftSing` — the decay of the shift at `z → ∞`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.bslOp_sinG
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllExist.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Inverting the shift -/

/-- Subtracting the same multiple of `sin 2θ` inverts `shiftSing`. -/
theorem shiftSing_sub_self (α : ℝ) (g Ψ : Fn) :
    shiftSing α g (fun z θ => Ψ z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) = Ψ := by
  funext z θ
  simp only [shiftSing_apply]
  ring

/-! ## The operator identity -/

/-- **The paper's identity `L(G(R) sin 2θ) = (α²R²G'' + α(5+α)RG') sin 2θ`.**

Adding the radial multiple `G(z) sin 2θ` to `Ψ` changes `bslOp α Ψ` only by
`-(α²z²G'' + α(5+α)zG') sin 2θ`: the `sin 2θ`-direction of `bslOp` is purely radial.  This is
`Work.Elliptic.bslOp_sinG` in the notation of the area. -/
theorem bslOp_shiftSing (α : ℝ) (g Ψ : Fn) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z)
    (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (shiftSing α g Ψ) z θ
      = Work.Elliptic.bslOp α Ψ z θ
        - (α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
            + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z) * Real.sin (2 * θ) := by
  rw [shiftSing_eq]
  exact Work.Elliptic.bslOp_sinG α Ψ (Work.Elliptic.Gsing α g) z θ hΨ hG hcos

/-- **The shift orthogonalises the source.**  If `Gsing α g` satisfies the singular-term ODE
`α²z²G'' + α(5+α)zG' = (15/4) F_*(g)`, then shifting by `Gsin 2θ` replaces the source `g` by
`orthSource g = g - (15/4) sin 2θ · F_*(g)`, i.e. by a source whose angular moment vanishes
(`Work.Elliptic.Fstar_orthSource`). -/
theorem bslOp_shiftSing_of_ode (α : ℝ) (g Ψ : Fn) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z)
    (hcos : Real.cos θ ≠ 0)
    (hode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z) :
    Work.Elliptic.bslOp α (shiftSing α g Ψ) z θ
      = Work.Elliptic.bslOp α Ψ z θ - (15 / 4) * Work.Elliptic.Fstar g z * Real.sin (2 * θ) := by
  rw [bslOp_shiftSing α g Ψ z θ hΨ hG hcos, hode]

/-- The converse direction: if the shifted unknown solves the orthogonalised equation, then the
unshifted one solves the original equation.  This is the step that turns the existence theorem
for the orthogonalised source `orthSource g` (which is what the elliptic theory provides) into
`IsBslSol α g Ψ`. -/
theorem bslOp_eq_of_shiftSing_of_ode (α : ℝ) (g Ψ : Fn) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z)
    (hcos : Real.cos θ ≠ 0)
    (hode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z)
    (hsol : Work.Elliptic.bslOp α (shiftSing α g Ψ) z θ = Work.Elliptic.orthSource g z θ) :
    Work.Elliptic.bslOp α Ψ z θ = g z θ := by
  have h := bslOp_shiftSing_of_ode α g Ψ z θ hΨ hG hcos hode
  rw [hsol, Work.Elliptic.orthSource] at h
  have h2 : Work.Elliptic.bslOp α Ψ z θ
      = (g z θ - 15 / 4 * Work.Elliptic.Fstar g z * Real.sin (2 * θ))
        + 15 / 4 * Work.Elliptic.Fstar g z * Real.sin (2 * θ) := by linarith [h]
  linarith [h2]

/-! ## The Dirichlet values -/

/-- The shift preserves the Dirichlet value at `θ = 0`. -/
theorem shiftSing_zero (α : ℝ) (g Ψ : Fn) (h : ∀ z, Ψ z 0 = 0) :
    ∀ z, shiftSing α g Ψ z 0 = 0 := by
  intro z
  simp [shiftSing_apply, h z]

/-- The shift preserves the Dirichlet value at `θ = π/2`. -/
theorem shiftSing_pi_half (α : ℝ) (g Ψ : Fn) (h : ∀ z, Ψ z (π / 2) = 0) :
    ∀ z, shiftSing α g Ψ z (π / 2) = 0 := by
  intro z
  have hsin : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]
  simp [shiftSing_apply, h z, hsin]

/-! ## The angular moment of the shift -/

/-- `∫_θ sin 2θ · sinθcos²θ dθ = 4/15`, the normalisation constant of §'The singular term'. -/
theorem integral_sin_two_mul_sinCos2 :
    (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) = 4 / 15 :=
  Work.Elliptic.integral_sin_two_mul_sinCos2

/-- **The angular moment of the shifted function.**
`F_*(Ψ + G sin 2θ) z = F_*(Ψ) z + (4/15) G(z)`. -/
theorem Fstar_shiftSing (α : ℝ) (g Ψ : Fn) (z : ℝ)
    (hΨ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (shiftSing α g Ψ) z
      = Work.Elliptic.Fstar Ψ z + 4 / 15 * Work.Elliptic.Gsing α g z := by
  have hIθc : IsCompact Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact isCompact_Icc
  have hcont : Continuous (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.Gsing α g z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
      Work.Spaces.Iθ :=
    ((continuous_const.mul hcont).continuousOn).integrableOn_compact hIθc
  have hsplit : (∫ θ in Work.Spaces.Iθ, shiftSing α g Ψ z θ * Work.Elliptic.sinCos2 θ)
      = (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ)
        + (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.Gsing α g z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) := by
    rw [← MeasureTheory.integral_add hΨ hGint]
    apply MeasureTheory.setIntegral_congr_fun (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
    intro θ _
    simp only [shiftSing_apply]
    ring
  have hcon : (∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Gsing α g z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
      = Work.Elliptic.Gsing α g z * (4 / 15) := by
    rw [MeasureTheory.integral_const_mul, integral_sin_two_mul_sinCos2]
  rw [Work.Elliptic.Fstar, hsplit, hcon, Work.Elliptic.Fstar]
  ring

/-! ## Smoothness of the shift -/

/-- **The shifted function is as smooth as its two ingredients.** -/
theorem contDiffOn_uncurry_shiftSing (α : ℝ) (g Ψ : Fn) (n : ℕ)
    (hΨ : ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hG : ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (shiftSing α g Ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hG' : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Elliptic.Gsing α g p.1) Work.FTS.EllipticEst.Q0 :=
    hG.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 := by
    fun_prop
  have hfun : Function.uncurry (shiftSing α g Ψ)
      = fun p : ℝ × ℝ => Function.uncurry Ψ p
          + Work.Elliptic.Gsing α g p.1 * Real.sin (2 * p.2) := rfl
  rw [hfun]
  exact hΨ.add (hG'.mul hsin)

/-- `SmoothOpen` of the shift, from `SmoothOpen` of `Ψ` and all-order smoothness of
`Gsing α g` on `(0,∞)`. -/
theorem smoothOpen_shiftSing (α : ℝ) (g Ψ : Fn)
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hG : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (shiftSing α g Ψ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall fun n =>
    contDiffOn_uncurry_shiftSing α g Ψ n
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ n) (hG n)

/-- Joint smoothness of the shifted function on the open quadrant, from `IsBslSol`-type data. -/
theorem contDiffOn_uncurry_shiftSing_of_smoothOpen (α : ℝ) (g Ψ : Fn)
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hG : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (shiftSing α g Ψ))
      Work.FTS.EllipticEst.Q0 :=
  fun n => contDiffOn_uncurry_shiftSing α g Ψ n
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ n) (hG n)

/-! ## Decay of the shift -/

/-- The shift preserves the decay at `z → ∞`. -/
theorem tendsto_shiftSing (α : ℝ) (g Ψ : Fn) (θ : ℝ)
    (hΨ : Tendsto (fun z => Ψ z θ) atTop (𝓝 0))
    (hG : Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0)) :
    Tendsto (fun z => shiftSing α g Ψ z θ) atTop (𝓝 0) := by
  have hfun : (fun z => shiftSing α g Ψ z θ)
      = fun z => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl
  rw [hfun]
  simpa using hΨ.add (hG.mul_const (Real.sin (2 * θ)))

/-- **The orthogonality of `orthSource F`, unconditionally.**

`F_*(orthSource F)(z) = 0` for every `z`, with no hypothesis at all: if the slice
`θ ↦ F z θ · sinθcos²θ` is not integrable both sides of the identity are the junk value `0`,
and otherwise the integral splits and `∫_θ sin 2θ · sinθcos²θ dθ = 4/15` cancels the `15/4`.

(Proved here to keep the area self-contained: the version in
`Submission/Work/Elliptic/Fstar_orthSource.lean` asks for continuity of the angular slice.) -/
theorem Fstar_orthSource_zero (F : Fn) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z = 0 := by
  set u : ℝ → ℝ := fun θ => (F z θ - (15 / 4) * Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
    * Work.Elliptic.sinCos2 θ with hu
  have hval : Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z
      = ∫ θ in Work.Spaces.Iθ, u θ := by
    rw [Work.Elliptic.Fstar]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [hu, Work.Elliptic.orthSource]
  rw [hval]
  by_cases hint : MeasureTheory.Integrable u (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · have hpt : ∀ θ, u θ = F z θ * Work.Elliptic.sinCos2 θ
        - ((15 / 4) * Work.Elliptic.Fstar F z)
          * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; simp only [hu]; ring
    have h2int : MeasureTheory.Integrable
        (fun θ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hc : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
        simp only [Work.Elliptic.sinCos2]; fun_prop
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
    have h1int : MeasureTheory.Integrable (fun θ => F z θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hsub : MeasureTheory.Integrable
          (fun θ => u θ + ((15 / 4) * Work.Elliptic.Fstar F z)
            * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        hint.add (h2int.const_mul _)
      refine hsub.congr ?_
      filter_upwards with θ
      rw [hpt θ]; ring
    have hcongr : (∫ θ in Work.Spaces.Iθ, u θ)
        = ∫ θ in Work.Spaces.Iθ, (F z θ * Work.Elliptic.sinCos2 θ
            - ((15 / 4) * Work.Elliptic.Fstar F z)
              * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => hpt θ
    rw [hcongr, MeasureTheory.integral_sub h1int (h2int.const_mul _),
      MeasureTheory.integral_const_mul, integral_sin_two_mul_sinCos2]
    simp only [Work.Elliptic.Fstar]
    ring
  · exact MeasureTheory.integral_undef hint

end Work.FTS.EllExist
